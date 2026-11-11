-- Prove2me | Definitions.Def_ExpanderWalkDecode_Main_Machine
-- name    : ExpanderWalkDecode_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:43.329906+00:00
-- url     : https://prove2.me/theorems/c8ac6cf6-5cfb-454d-b299-22038745956e
-- title:
--   Unit-cost randomized real RAM with fair coins, square root, logarithm and a charged symmetric eigensolver
-- statement:
--   The paper states running-time bounds and describes exact spectral projections in Figure 3 and an exact top eigenvector in Figure 4. It does not explicitly fix a machine or precision convention. Because an exact eigenvalue threshold is meaningful only in exact real arithmetic, this mission fixes the source's model as a unit-cost real RAM with an exact symmetric eigensolver.
--
--   A **program** is a finite list of instructions, the same for every input. A machine state consists of finitely many real registers $r_0, r_1, \dots$, integer pointer registers $p_0, p_1, \dots$, banked memories $R_k : \mathbb Z \to \mathbb R$ and $I_k : \mathbb Z \to \mathbb Z$ addressed through pointers, a cursor on a tape of fair coins, an output list of reals, a halting flag and a work counter. The instructions are those of the published real pointer machine (rational literals, exact $+,-,\times,\div$ with $x/0=0$, comparison jumps), together with:
--
--   1. integer pointer arithmetic $+,-,\times$; loads and stores between registers and the banks;
--   2. the cast of a pointer to a real (there is no conversion from reals to integers and no floor);
--   3. $\sqrt{\cdot}$ and the natural logarithm $\log$ (of $|x|$, with $\log 0 = 0$) on a real register;
--   4. **coin**: write the next fair bit ($0$ or $1$) into a pointer register;
--   5. **eig**: for $d = p[\cdot]$, read the $d\times d$ matrix stored row-major in a real bank and, if it is symmetric, write its eigenvalues and an orthonormal basis of eigenvectors; this costs $d^3+1$ units of work;
--   6. **emit**: append a real register to the output list; **halt**.
--
--   Every other executed instruction costs one unit. An invalid program counter is stuck and charged; after halt the state no longer changes. A program is **admissible** if all its literals are rational.
--
--   A run of $T$ steps reads at most $T$ coins, so the probability that the program halts within $T$ steps with an output satisfying a predicate is the fraction of the $2^T$ coin strings of length $T$ for which this happens. "$P$ runs within $B$ steps with success probability at least $p$" means: there is $T \le B$ such that, on every coin string, the run has halted after $T$ transitions and its work counter has increased by at most $T$; the output satisfies the predicate with probability at least $p$. This charges the cubic cost of every spectral call.
--
--   **Formalization Note** There is no floor, real-to-integer conversion, exponential, uniform real sample or optimization oracle, so a program cannot read its input or solve an SDP for free. The eigensolver is the one non-arithmetic instruction; it reflects the exact spectral steps of Figures 3 and 4 and is charged cubically in the dimension. The logarithm lets a program evaluate the source's parameter formulas exactly (for instance the dimension $\lceil C\theta^{-2}\log k\rceil$ of Proposition 6, by counting up to it); without it no program could output vectors of exactly that dimension for every real $\theta$. The published `SmaleNinth.RAMInstr` real RAM is reused as the scalar core.
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), pp. 11–19 (Lemmas 1–3, Figures 2–5, runtime analyses); p. 8, Definition 1

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace ExpanderWalkDecode.Main

/-!
# The cost model: a unit-cost randomized real RAM with a charged symmetric eigensolver

Richelson–Roy–Tulsiani, *Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear
Time*, STOC 2027 submission #1736. The paper counts arithmetic operations on real numbers, random
draws, and exact spectral computations (Figure 3 takes exact spectral projections, Figure 4 an
exact top eigenvector) without bit lengths, and its algorithms set parameters by logarithmic
formulas (`Δ = ⌈Cθ⁻² log k⌉` of Proposition 6, `ℓ` of Figure 4, `Δ` of §4.1). This file fixes
that model.

* The scalar core is the published real pointer machine `SmaleNinth.RAMInstr` (real registers,
  integer pointers, `+ - × ÷` with `x / 0 = 0`, literals, comparison jumps).
* Additions: integer pointer `+ - ×`; banked real and integer memories `ℕ → ℤ → ℝ`,
  `ℕ → ℤ → ℤ`, read and written through pointers; the cast of a pointer to a real (one way only);
  `sqrt`; `log` (`Real.log`); a fair `coin` (writes `0` or `1` into a pointer register); `eig`, the exact
  eigendecomposition of a symmetric `d × d` matrix stored row-major in a real bank, charged
  `d ^ 3 + 1` units; `emit`, which appends a real register to the output list; `halt`.
* Not in the language: floor, real-to-integer conversion, `exp`, a uniform real sample, an
  SDP solver, or any instruction carrying an arbitrary mathematical function.
* Every executed instruction costs one unit, except `eig`, which costs `d ^ 3 + 1`. An invalid
  program counter is stuck and charged. After `halt` the state stutters at no cost.
* `Admissible` programs use rational literals only and no core `accept`/`reject`.
* Fair coins come from a tape `ω : ℕ → Bool`; probabilities are counts of `T`-bit tapes divided by
  `2 ^ T`: a run of `T` steps reads at most `T` coins.
-/

/-- One instruction. Register, pointer, bank and label arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction (acting on the core registers and core memory).
* `padd d a b`, `psub d a b`, `pmul d a b`: `p[d] := p[a] ± p[b]`, `p[d] := p[a] * p[b]`.
* `rload d k a`: `r[d] := R k (p[a])`; `rstore k a v`: `R k (p[a]) := r[v]`.
* `iload d k a`: `p[d] := I k (p[a])`; `istore k a v`: `I k (p[a]) := p[v]`.
* `cast d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])` (`Real.sqrt`, which is `0` on negatives).
* `log d a`: `r[d] := log (r[a])` (`Real.log`, the natural logarithm of `|r[a]|`, `0` at `0`).
* `coin d`: `p[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `eig k dim src dst`: with `d = p[dim]`, read the `d × d` matrix `M i j = R k (p[src] + d*i + j)`;
  if it is symmetric write its eigenvalues to `R k (p[dst] + i)` and the `i`-th coordinate of the
  `j`-th orthonormal eigenvector to `R k (p[dst] + d + d*j + i)`; charged `d ^ 3 + 1`.
* `emit v`: append `r[v]` to the output list.
* `halt`: stop. -/
inductive Instr where
  | core (i : SmaleNinth.RAMInstr)
  | padd (dst a b : ℕ)
  | psub (dst a b : ℕ)
  | pmul (dst a b : ℕ)
  | rload (dst bank addr : ℕ)
  | rstore (bank addr src : ℕ)
  | iload (dst bank addr : ℕ)
  | istore (bank addr src : ℕ)
  | cast (dst src : ℕ)
  | sqrt (dst src : ℕ)
  | log (dst src : ℕ)
  | coin (dst : ℕ)
  | eig (bank dim src dst : ℕ)
  | emit (src : ℕ)
  | halt

/-- A program: one finite list of instructions, executed from position `0`, the same for every
input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions do not occur. This restricts
the existentially chosen program, never the input. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, match i with
    | .core (.const _ x) => ∃ q : ℚ, x = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- A machine state: the core configuration, the banked memories, the coin cursor, the output
list, the halting flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  reals : ℕ → ℤ → ℝ
  ints : ℕ → ℤ → ℤ
  cursor : ℕ
  output : List ℝ
  halted : Bool
  work : ℕ

/-- The core table of `P`; positions holding an addition of this module carry a placeholder that
`step` never executes. -/
def coreCode (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with
    | .core j => j
    | _ => .const 0 0

/-- The matrix read by `eig`: `M i j = R (base + d*i + j)`. -/
def readMatrix (R : ℤ → ℝ) (base : ℤ) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => R (base + (d : ℤ) * (i : ℤ) + (j : ℤ))

/-- The bank after `eig` wrote the eigenvalues of a symmetric `M` at `dst + i` and the `i`-th
coordinate of the `j`-th orthonormal eigenvector at `dst + d + d*j + i`. -/
noncomputable def writeEigen (R : ℤ → ℝ) (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (dst : ℤ) : ℤ → ℝ := fun z =>
  if h : dst ≤ z ∧ z < dst + d then
    hM.eigenvalues ⟨(z - dst).toNat, by omega⟩
  else if h' : dst + d ≤ z ∧ z < dst + d + (d : ℤ) * d then
    let k := (z - dst - d).toNat
    have hk : k < d * d := by
      have h0 : 0 ≤ z - dst - d := by omega
      have h1 : ((z - dst - d).toNat : ℤ) < (d : ℤ) * d := by
        rw [Int.toNat_of_nonneg h0]; omega
      exact_mod_cast h1
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; simp at hk
      · exact h0
    (hM.eigenvectorBasis ⟨k / d, Nat.div_lt_of_lt_mul hk⟩) ⟨k % d, Nat.mod_lt _ hd⟩
  else R z

/-- One step of `P` with coin tape `ω`. A halted state stutters at no cost; an invalid program
counter is stuck and charged. The tape occurs only in the `coin` branch. -/
noncomputable def step (P : Program) (ω : ℕ → Bool) (s : State) : State :=
  if s.halted then s else
    let p := s.core.ptrs
    let r := s.core.regs
    let t : State := { s with
      core := { s.core with pc := s.core.pc + 1 }
      work := s.work + 1 }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { s with core := SmaleNinth.RAMStep (coreCode P) s.core, work := s.work + 1 }
    | some (.padd d a b) => { t with core := { t.core with ptrs := Function.update p d (p a + p b) } }
    | some (.psub d a b) => { t with core := { t.core with ptrs := Function.update p d (p a - p b) } }
    | some (.pmul d a b) => { t with core := { t.core with ptrs := Function.update p d (p a * p b) } }
    | some (.rload d k a) =>
        { t with core := { t.core with regs := Function.update r d (s.reals k (p a)) } }
    | some (.rstore k a v) =>
        { t with reals := Function.update s.reals k (Function.update (s.reals k) (p a) (r v)) }
    | some (.iload d k a) =>
        { t with core := { t.core with ptrs := Function.update p d (s.ints k (p a)) } }
    | some (.istore k a v) =>
        { t with ints := Function.update s.ints k (Function.update (s.ints k) (p a) (p v)) }
    | some (.cast d a) => { t with core := { t.core with regs := Function.update r d (p a : ℝ) } }
    | some (.sqrt d a) =>
        { t with core := { t.core with regs := Function.update r d (Real.sqrt (r a)) } }
    | some (.log d a) =>
        { t with core := { t.core with regs := Function.update r d (Real.log (r a)) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with ptrs := Function.update p d (if ω s.cursor then 1 else 0) } }
    | some (.eig k dim src dst) =>
        let d := (p dim).toNat
        let M := readMatrix (s.reals k) (p src) d
        let t' : State := { t with work := s.work + d ^ 3 + 1 }
        if hM : M.IsHermitian then
          { t' with reals := Function.update s.reals k (writeEigen (s.reals k) d M hM (p dst)) }
        else t'
    | some (.emit v) => { t with output := s.output ++ [r v] }
    | some .halt => { t with halted := true }

/-- The state after `k` steps from `s₀`. -/
noncomputable def run (P : Program) (ω : ℕ → Bool) (s₀ : State) (k : ℕ) : State :=
  (step P ω)^[k] s₀

/-- The initial state on the input banks `R`, `I`: program counter `0`, all registers, pointers and
core memory `0`, no output, cursor and work `0`. -/
def init (R : ℕ → ℤ → ℝ) (I : ℕ → ℤ → ℤ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, R, I, 0, [], false, 0⟩

/-- A tape from finitely many bits; later bits are `false`. -/
def extendBits {T : ℕ} (bits : Fin T → Bool) : ℕ → Bool :=
  fun k => if h : k < T then bits ⟨k, h⟩ else false

/-- On every coin tape, the run from `s₀` has halted after `T` transitions and has consumed
at most `T` units of work. In particular, a spectral instruction is charged `d³ + 1`, not one. -/
def HaltsWithin (P : Program) (s₀ : State) (T : ℕ) : Prop :=
  ∀ bits : Fin T → Bool, (run P (extendBits bits) s₀ T).halted = true ∧
    (run P (extendBits bits) s₀ T).work ≤ s₀.work + T

/-- The fraction of `T`-bit tapes on which the run has halted after `T` steps with an output
satisfying `good`. When `HaltsWithin P s₀ T` holds this is the probability, under fair coins, that
the program outputs a list satisfying `good`. -/
noncomputable def successProb (P : Program) (s₀ : State) (T : ℕ) (good : List ℝ → Prop) : ℝ :=
  (Nat.card {bits : Fin T → Bool //
      (run P (extendBits bits) s₀ T).halted = true ∧ good (run P (extendBits bits) s₀ T).output} : ℝ)
    / 2 ^ T

/-- `P`, started in `s₀`, halts within `B` units of work on every coin tape and outputs a list satisfying
`good` with probability at least `p`. -/
def RunsWithin (P : Program) (s₀ : State) (B : ℝ) (good : List ℝ → Prop) (p : ℝ) : Prop :=
  ∃ T : ℕ, (T : ℝ) ≤ B ∧ HaltsWithin P s₀ T ∧ p ≤ successProb P s₀ T good

/-- A bank holding the list `L` from address `0` on, and `0` elsewhere. -/
def listBank (L : List ℝ) : ℤ → ℝ := fun z => if 0 ≤ z then L.getD z.toNat 0 else 0

/-- An integer bank holding the list `L` from address `0` on, and `0` elsewhere. -/
def listIBank (L : List ℤ) : ℤ → ℤ := fun z => if 0 ≤ z then L.getD z.toNat 0 else 0

end ExpanderWalkDecode.Main


