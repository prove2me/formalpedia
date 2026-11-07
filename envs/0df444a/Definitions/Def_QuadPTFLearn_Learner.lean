-- Prove2me | Definitions.Def_QuadPTFLearn_Learner
-- name    : QuadPTFLearn_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:20.149626+00:00
-- url     : https://prove2.me/theorems/1a3bd3cf-5c28-4436-aa7d-9e0a0cdd1d65
-- title:
--   Sample laws, the output layout of a PTF of quadratic features, and the bound $d^{Ck}2^{C_k\log^3(1/\varepsilon)}$
-- statement:
--   The interface between the learning problem and the machine.
--
--   1. **Examples.** A labelled example $(x,y)$ is given to the machine as $(x_1,\dots,x_d,y)\in\mathbb R^{d+1}$. For a law $D$ on $\mathbb R^d\times\mathbb R$ the stream is i.i.d. from $D$. In the realizable setting of Definition 1.2, with marginal $N(0,I_d)$ and $y=f^*(x)$ almost surely, the law of one example is the image of $N(0,I_d)$ under $x\mapsto(x,f^*(x))$.
--   2. **Error.** $\mathrm{err}(h)=\Pr_{x\sim N(0,I_d)}[h(x)\ne f^*(x)]$.
--   3. **Output hypotheses.** A hypothesis is
--   $$\hat f(x)=1\Big\{\sum_{t=1}^{T}a_t\prod_{j=1}^{m}\phi_j(x)^{e_{t,j}}\ge0\Big\},\qquad \phi_j(x)=c_j+\langle b_j,x\rangle+x^\top A_jx,$$
--   a single polynomial threshold function of learned quadratic features. It is read from memory starting at the cell $p[1]$: $m$; then for each $j$ the numbers $c_j$, $b_j$ ($d$ cells), $A_j$ ($d^2$ cells, row-major); then $T$; then $T$ records $(a_t,e_{t,1},\dots,e_{t,m})$. If $m$, $T$ or an exponent is not a natural number the output does not decode.
--   4. **Cost bound.** $\mathrm{bound}(C,C_k;d,k,\varepsilon)=d^{Ck}\,2^{C_k(k)\log^3(1/\varepsilon)}$ with the natural logarithm.
--   5. **Other layouts.** A vector of the lifted space $\mathbb R^N$ is input as its $d$ linear coordinates followed by a $d\times d$ row-major block holding the quadratic coordinates on and above the diagonal; a matrix output is a row-major block; a list of vectors is a count followed by blocks of $d$ cells. $\|M\|_{op}$ is the operator norm on $\mathbb R^d$.
--
--   **Formalization Note** The output form is the one stated on p.3 of the paper for the algorithm of Theorem 1.3. A run whose output does not decode counts as a failure.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Definition 1.2; the output form, p.2 (PDF p.4); output form p.3 (PDF p.5); Theorem 1.3 p.2; Algorithm 5 p.79 (PDF p.81); Lemma 6.3 and Theorem 6.2 p.63 (PDF p.65)

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian
import Definitions.Def_QuadPTFLearn_Machine

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# Sample laws, input and output layouts, and the cost bound of the learner

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Definition 1.2, p.2 (PDF p.4); the output form, p.3 (PDF p.5); Theorem 1.3, p.2; Theorem 8.1
and Algorithm 5, pp.72, 79 (PDF pp.74, 81); Lemma 6.3 and Theorem 6.2, p.63 (PDF p.65).

**Formalization Note.**
* A labelled example `(x, y) ∈ ℝᵈ × ℝ` is written to the machine as the vector
  `(x₁, …, x_d, y) ∈ ℝ^{d+1}` (`toSample`). For a joint law `D` on `ℝᵈ × ℝ` the stream law is the
  infinite product of `jointLaw D`. In the realizable setting of Definition 1.2 every admissible
  `D` (marginal `N(0, I_d)`, `y = f*(x)` almost surely) has the same law `sampleLaw q`, the
  push-forward of `N(0, I_d)` under `x ↦ (x, f*(x))`.
* `err q h = Pr_{x∼N(0,I)}[h(x) ≠ f*(x)]` is the Gaussian error `err_D(h)` of Definition 1.2.
* Output layout of a hypothesis (p.3: `f̂(x) = 1{P(ϕ₁(x), …, ϕ_m(x)) ≥ 0}` with learned quadratic
  features `ϕ_j`): at `halt`, memory from the cell `p[1]` holds `m`; then for each `j < m` a block
  `c_j, b_j (d cells), A_j (d² cells, row-major)`, with `ϕ_j(x) = c_j + ⟪b_j, x⟫ + xᵀA_j x`; then
  `T`; then `T` records `(a_t, e_{t,0}, …, e_{t,m−1})`, and
  `P(ϕ) = Σ_t a_t ∏_j ϕ_j^{e_{t,j}}`. `decode` returns `none` when `m`, `T` or an exponent is not a
  natural number; `none` counts as a failure.
* Input layout of a vector `u ∈ ℝᴺ` of the lifted space (`liftCells`): its `d` linear coordinates,
  then `d²` cells in row-major order whose entry `(i, j)` is `u_{(i,j)}` for `i ≤ j` and `0` for
  `i > j`.
* `bound C Ck d k ε = d^{C k} · 2^{Ck(k) · log³(1/ε)}` (natural logarithm) is the bound
  `d^{O(k)} 2^{O_k(log³(1/ε))}` of Theorem 1.3 with the universal constant `C` and the
  `k`-dependent constant `Ck k`.
-/

/-- The example `(x, y)` as the vector `(x₁, …, x_d, y) ∈ ℝ^{d+1}`. -/
noncomputable def toSample {d : ℕ} (x : Pt d) (y : ℝ) : Pt (d + 1) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i) y)

lemma measurable_toSample (d : ℕ) :
    Measurable (fun z : Pt d × ℝ => toSample z.1 z.2) := by
  have : Continuous (fun z : Pt d × ℝ => toSample z.1 z.2) := by
    unfold toSample
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact continuous_snd
    · simp only [Fin.snoc_castSucc]
      exact ((PiLp.continuous_apply 2 _ j).comp continuous_fst)
  exact this.measurable

lemma continuous_peval {d : ℕ} (p : Poly d) : Continuous (peval p) := by
  unfold peval
  exact (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => PiLp.continuous_apply 2 _ i)

lemma measurable_ptfInd {d k : ℕ} (q : Fin k → Poly d) : Measurable (ptfInd q) := by
  unfold ptfInd
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {x : Pt d | ∀ i, 0 ≤ peval (q i) x} = ⋂ i, {x | 0 ≤ peval (q i) x} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (continuous_peval _).measurable

/-- The law of one labelled example `(x, y)`, `y = f*(x)`, `f* = ptfInd q`, `x ∼ N(0, I_d)`. -/
noncomputable def sampleLaw {d k : ℕ} (q : Fin k → Poly d) : Measure (Pt (d + 1)) :=
  (gauss d).map (fun x => toSample x (ptfInd q x))

instance {d k : ℕ} (q : Fin k → Poly d) : IsProbabilityMeasure (sampleLaw q) := by
  unfold sampleLaw
  refine Measure.isProbabilityMeasure_map ?_
  exact ((measurable_toSample d).comp (measurable_id.prodMk (measurable_ptfInd q))).aemeasurable

/-- The law of one example of a joint distribution `D` on `ℝᵈ × ℝ`, written in `ℝ^{d+1}`. -/
noncomputable def jointLaw {d : ℕ} (D : Measure (Pt d × ℝ)) : Measure (Pt (d + 1)) :=
  D.map (fun z => toSample z.1 z.2)

instance {d : ℕ} (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (jointLaw D) :=
  Measure.isProbabilityMeasure_map (measurable_toSample d).aemeasurable

/-- The Gaussian error `err(h) = Pr_{x∼N(0,I)}[h(x) ≠ f*(x)]` against `f* = ptfInd q`. -/
noncomputable def err {d k : ℕ} (q : Fin k → Poly d) (h : Pt d → ℝ) : ENNReal :=
  gauss d {x | h x ≠ ptfInd q x}

/-- The distribution `D` on `ℝᵈ × ℝ` has marginal `N(0, I_d)` on the first coordinate. -/
def HasGaussMarginal {d : ℕ} (D : Measure (Pt d × ℝ)) : Prop := D.map Prod.fst = gauss d

/-- A natural number stored as a real cell, if it is one. -/
noncomputable def natOf (r : ℝ) : Option ℕ :=
  if 0 ≤ r ∧ ((Nat.floor r : ℕ) : ℝ) = r then some (Nat.floor r) else none

/-- A hypothesis `f̂(x) = 1{Σ_t a_t ∏_j ϕ_j(x)^{e_{t,j}} ≥ 0}` with quadratic features
`ϕ_j(x) = c_j + ⟪b_j, x⟫ + xᵀ A_j x`. -/
structure Hyp (d : ℕ) where
  m : ℕ
  c : Fin m → ℝ
  b : Fin m → Pt d
  A : Fin m → Matrix (Fin d) (Fin d) ℝ
  T : ℕ
  a : Fin T → ℝ
  e : Fin T → Fin m → ℕ

/-- The quadratic feature `ϕ_j(x) = c_j + ⟪b_j, x⟫ + xᵀ A_j x`. -/
noncomputable def Hyp.feature {d : ℕ} (H : Hyp d) (j : Fin H.m) (x : Pt d) : ℝ :=
  H.c j + ⟪H.b j, x⟫ + ∑ i, ∑ i', x i * H.A j i i' * x i'

/-- The polynomial of the features, `Σ_t a_t ∏_j ϕ_j(x)^{e_{t,j}}`. -/
noncomputable def Hyp.poly {d : ℕ} (H : Hyp d) (x : Pt d) : ℝ :=
  ∑ t, H.a t * ∏ j, H.feature j x ^ H.e t j

/-- The `{0,1}`-valued hypothesis `1{P(ϕ₁(x), …, ϕ_m(x)) ≥ 0}`. -/
noncomputable def Hyp.eval {d : ℕ} (H : Hyp d) (x : Pt d) : ℝ :=
  if 0 ≤ H.poly x then 1 else 0

/-- Read a hypothesis from memory `mem` starting at `base`, in the output layout above. -/
noncomputable def decode (d : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Option (Hyp d) :=
  match natOf (mem base) with
  | none => none
  | some m =>
    let blk : ℕ := 1 + d + d * d
    let cell : ℕ → ℕ → ℝ := fun j o => mem (base + 1 + ((j * blk + o : ℕ) : ℤ))
    let tb : ℤ := base + 1 + ((m * blk : ℕ) : ℤ)
    match natOf (mem tb) with
    | none => none
    | some T =>
      let rcell : ℕ → ℕ → ℝ := fun t o => mem (tb + 1 + ((t * (1 + m) + o : ℕ) : ℤ))
      if ∀ t < T, ∀ j < m, (natOf (rcell t (1 + j))).isSome then
        some
          { m := m
            c := fun j => cell j 0
            b := fun j => WithLp.toLp 2 (fun i => cell j (1 + i))
            A := fun j i i' => cell j (1 + d + d * i + i')
            T := T
            a := fun t => rcell t 0
            e := fun t j => (natOf (rcell t (1 + j))).getD 0 }
      else none

/-- The cost bound `d^{C k} · 2^{Ck(k) · log³(1/ε)}` of Theorem 1.3. -/
noncomputable def bound (C : ℕ) (Ck : ℕ → ℕ) (d k : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) ^ (C * k) * (2 : ℝ) ^ ((Ck k : ℝ) * Real.log (1 / ε) ^ 3)

/-- The input cells of a lifted vector `u ∈ ℝᴺ`: `d` linear coordinates, then `d²` cells in
row-major order holding `u_{(i,j)}` for `i ≤ j` and `0` for `i > j`. -/
noncomputable def liftCells {d : ℕ} (u : Lift d) : List ℝ :=
  (List.finRange d).map (fun i => u (Sum.inl i)) ++
    (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j =>
      if h : i ≤ j then u (Sum.inr ⟨(i, j), h⟩) else 0))

/-- Read a `d × d` matrix in row-major order from memory starting at `base`. -/
noncomputable def readMatrix (d : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => mem (base + ((d * i + j : ℕ) : ℤ))

/-- Read a list of vectors of `ℝᵈ`: a count `r` at `base`, then `r` blocks of `d` cells. -/
noncomputable def decodeVecs (d : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Option (List (Pt d)) :=
  match natOf (mem base) with
  | none => none
  | some r => some ((List.range r).map fun t =>
      WithLp.toLp 2 (fun i : Fin d => mem (base + 1 + ((d * t + i : ℕ) : ℤ))))

/-- The operator norm `‖M‖_op` of a real `d × d` matrix acting on `ℝᵈ`. -/
noncomputable def opNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

end QuadPTFLearn


