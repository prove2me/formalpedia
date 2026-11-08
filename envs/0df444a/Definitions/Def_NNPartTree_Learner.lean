-- Prove2me | Definitions.Def_NNPartTree_Learner
-- name    : NNPartTree_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:19.444222+00:00
-- url     : https://prove2.me/theorems/aa28c2ba-8990-4d20-9f97-832ca62669f2
-- title:
--   Sample access, input layouts, and the semantics of a learned nearest neighbor data structure
-- statement:
--   The interface between the learning problem and the machine.
--
--   1. **Samples.** A pair $(x,y)$ is one vector of $\mathbb R^{2d}$, $x$ then $y$. A run with sample access to $\mathcal D$ reads fair coins and, independently, an i.i.d. stream from $\mathcal D$.
--   2. **Inputs.** The learner receives $n,d$ in integer memory and the points of $P$ in row-major order in real memory. An algorithm receiving a sample gets $d,k,m$ and $\beta,\varepsilon$ and the pairs. PolyCut gets $d,k_0$ and $\beta,\varepsilon,\delta$.
--   3. **Outputs.** A vector or matrix is read from the address in pointer register $1$, in the order of the monomials. Coefficient vector $w$ means the polynomial $w^\top\phi_k$ and the threshold function $\mathrm{sign}(w^\top\phi_k)$.
--   4. **Query.** $q$ runs the query program from the learner's halted memory, with $q_j$ written to real cell $-1-j$ and all registers and counters reset. The answer is pointer register $0$, read as an index $k<n$.
--   5. **Good structure.** A memory is good for $C,\eta$ if it has at most $Cnd$ nonzero cells; if on **every** $q$ the query halts within $\eta nd$ work with a valid index; and if the answer is a nearest neighbor of $q$ except with probability at most $\eta$ over $(q,p^\star)\sim\mathcal D$.
--
--   The unknown distribution is reachable only through $\mathrm{sample}$, which is what "sample access" means.
--
--   **Formalization Note** Space counts nonzero cells at the learner's halt, which is the structure described on p.28, and not the cells written during learning. A program can clear its scratch within its time bound. `encard` does not read an infinite set as $0$, unlike `ncard`.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), §1, p.3; Theorem 3, pp.14–15; Theorem 4, p.27; p.28 (the data structure)

import Mathlib
import Definitions.Def_NNPartTree_CutTree
import Definitions.Def_NNPartTree_PolySDP

open MeasureTheory
open scoped ENNReal

namespace NNPartTree

/-!
# Sample access, input layouts and the semantics of a learned data structure

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…, §1, p.3;
Theorem 3 (pp.14–15); Theorem 4 (p.27).

**Formalization Note.**
* A pair `(x, y) ∈ ℝᵈ × ℝᵈ` is written to the machine as one vector of `ℝ^{2d}`, `x` then `y`, so that one
  `sample` instruction reads one pair. The stream is i.i.d. from `D`, independent of the coin tape.
* Input of the learner (`learnInput`): integer cells `0, 1` hold `n, d`; the real cells from `0` hold the
  points in row-major order. Every other cell is `0`.
* A sample given as input (`sampleInput`): integer cells `0, 1, 2` hold `d, k, m`; real cells `0, 1` hold
  `β, ε`; the real cells from `2` hold the pairs of `S` in row-major order, `x` then `y`.
* A query `q` runs `Qry` from the halted memory of the learner with `q j` written to the real cell `−1 − j`
  (`j < d`). Program counter, registers, pointers, cursors, halted flag and work are reset. `Qry` has no
  coin and no sample, so it is a function of the data structure and `q`.
* The answer is pointer register `0`, read as an index `k < n`: "finds a nearest neighbor" (p.27). Under a
  tie `p★` is not a function of `q`, so the answer need only be a minimizer.
* The space of the data structure is the number of nonzero cells (real or integer) of the memory at the
  learner's halt, the structure of p.28, not the cells written during learning. It uses `encard`, which
  unlike `ncard` does not read an infinite set as `0`.
-/

variable {d : ℕ}

/-- A pair `(x, y)` as one vector of `ℝ^{2d}`, `x` then `y`. -/
noncomputable def toSample (z : Pt d × Pt d) : Pt (2 * d) :=
  WithLp.toLp 2 fun i : Fin (2 * d) =>
    if h : (i : ℕ) < d then z.1 ⟨i, h⟩ else z.2 ⟨i - d, by have := i.isLt; omega⟩

lemma continuous_toSample : Continuous (toSample (d := d)) := by
  unfold toSample
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : (i : ℕ) < d
  · simp only [h, dite_true]
    exact (PiLp.continuous_apply 2 _ _).comp continuous_fst
  · simp only [h, dite_false]
    exact (PiLp.continuous_apply 2 _ _).comp continuous_snd

/-- The law of one sample of `D`, as a vector of `ℝ^{2d}`. -/
noncomputable def sampleLaw (D : Measure (Pt d × Pt d)) : Measure (Pt (2 * d)) :=
  D.map toSample

instance (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] : IsProbabilityMeasure (sampleLaw D) :=
  Measure.isProbabilityMeasure_map continuous_toSample.measurable.aemeasurable

/-- The randomness of a run with sample access to `D`: a fair-coin tape and, independent of it, an i.i.d.
stream from `D`. -/
noncomputable def sampleSpace (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] :
    Measure ((ℕ → Bool) × (ℕ → Pt (2 * d))) :=
  coinTape.prod (Measure.infinitePi fun _ : ℕ => sampleLaw D)

/-- The input of the learner: sizes `n, d` in integer memory and the points in row-major order. -/
noncomputable def learnInput {n : ℕ} (P : Fin n → Pt d) : State :=
  initState [(n : ℤ), (d : ℤ)] (List.ofFn fun i : Fin n => List.ofFn fun j : Fin d => P i j).flatten

/-- The input of an algorithm that receives a sample `S ∼ D^m`, `k`, `β` and `ε`. -/
noncomputable def sampleInput {m : ℕ} (k : ℕ) (S : Fin m → Pt d × Pt d) (β ε : ℝ) : State :=
  initState [(d : ℤ), (k : ℤ), (m : ℤ)]
    (β :: ε :: (List.ofFn fun i : Fin m =>
      List.ofFn fun j : Fin (2 * d) => toSample (S i) j).flatten)

/-- The input of PolyCut (Theorem 3, p.14): `d, k₀` in integer memory and `β, ε, δ` in real memory. -/
noncomputable def polyCutInput (d k₀ : ℕ) (β ε δ : ℝ) : State :=
  initState [(d : ℤ), (k₀ : ℤ)] [β, ε, δ]

/-- The polynomial output by a halted state: `x ↦ w^⊤ φ_k(x)`, with `w` the `N` real cells from the address
in pointer register `1`, in the order of `monomials d k`. -/
noncomputable def outputPoly (k : ℕ) (st : State) : Pt d → ℝ :=
  evalCoef (k := k) (outputVec (numMonomials d k) st)

/-- The polynomial threshold function output by a halted state: `x ↦ sign(w^⊤ φ_k(x))`. A threshold `θ` is
part of the constant coefficient. -/
noncomputable def outputPTF (k : ℕ) (st : State) : Pt d → ℝ :=
  fun x => sgn (outputPoly k st x)

/-- The start state of a query `q ∈ ℝᵈ` on the data structure stored in the state `st`: the real cell
`−1 − j` holds `q j` for `j < d`, every other cell is that of `st`; program counter, registers, pointers,
cursors, halted flag and work are reset. -/
noncomputable def queryState (st : State) (q : Pt d) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
      fun z => if h : z < 0 ∧ (-1 - z).toNat < d then q ⟨(-1 - z).toNat, h.2⟩ else st.core.mem z⟩,
    st.integerMemory, 0, 0, false, 0⟩

/-- The space of the data structure in the state `st`: its number of nonzero real and integer cells. -/
noncomputable def spaceOf (st : State) : ℕ∞ :=
  {z | st.core.mem z ≠ 0}.encard + {z | st.integerMemory z ≠ 0}.encard

/-- `Qry` halts on the query `q` from the data structure in `st` at the state `st'`. -/
def QueryFinal (Qry : Program) (st : State) (q : Pt d) (st' : State) : Prop :=
  IsFinal Qry 0 (queryState st q) (noCoins, noStream) st'

/-- The data structure in `st` answers `q` with a nearest neighbor in `P`: `Qry` halts with pointer
register `0` equal to an index `k < n` of a nearest point. -/
def AnswersNN {n : ℕ} (Qry : Program) (P : Fin n → Pt d) (st : State) (q : Pt d) : Prop :=
  ∃ st', QueryFinal Qry st q st' ∧ ∃ k : Fin n, st'.core.ptrs 0 = ((k : ℕ) : ℤ) ∧
    ∀ j, ‖q - P k‖ ≤ ‖q - P j‖

/-- The data structure in `st` has space at most `C · n · d`, on **every** query halts within work
`η · n · d` with a valid index, and finds a nearest neighbor with probability at least `1 − η` over
`(q, p★) ∼ D` (Theorem 4, p.27). -/
def IsGoodStructure {n : ℕ} (Qry : Program) (P : Fin n → Pt d) (D : Measure (Pt d × Pt d)) (C : ℕ)
    (η : ℝ) (st : State) : Prop :=
  spaceOf st ≤ ((C * n * d : ℕ) : ℕ∞) ∧
    (∀ q : Pt d, ∃ st', QueryFinal Qry st q st' ∧ (st'.work : ℝ) ≤ η * n * d ∧
      ∃ k : Fin n, st'.core.ptrs 0 = ((k : ℕ) : ℤ)) ∧
    D {z | ¬ AnswersNN Qry P st z.1} ≤ ENNReal.ofReal η

end NNPartTree


