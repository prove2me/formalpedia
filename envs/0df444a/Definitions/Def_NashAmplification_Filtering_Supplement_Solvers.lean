-- Prove2me | Definitions.Def_NashAmplification_Filtering_Supplement_Solvers
-- name    : NashAmplification_Filtering_Supplement_Solvers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:58:42.26736+00:00
-- url     : https://prove2.me/theorems/d5861af8-623e-4918-8c61-efad8bcc0482
-- title:
--   Deterministic search solvers with running-time bounds
-- statement:
--   Fix the published complete-table encoding of games and profiles over the four-symbol alphabet (binary numerators and denominators with separators). This definition adds a time-indexed layer of deterministic search solvers.
--
--   1. **Problems.** For a $k$-player game $G$ with payoffs in $[0,1]$, a profile $\sigma$ solves the input problem if it lists one probability vector per player of $G$ and is a $\delta$-approximate Nash equilibrium of $G$. A table $H$ is a *symmetric binary-payoff $C$-player game* if all players share $n\ge1$ actions, the payoff table is invariant under player permutations, and every payoff is $0$ or $1$. A profile $\sigma$ solves the target problem for $H$ if it has $n$ probabilities per player and is an $(\varepsilon,\eta)$-weak approximate Nash equilibrium of $H$.
--   2. **Running within a bound.** A deterministic multi-stack Turing machine $A$ (fixed program, finite states, input and output alphabets identified with the encoding alphabet) *solves* a search problem on a promise set $P$ *within* a bound $B:\mathbb R\to\mathbb R$ if on every promised input $x$ it halts after some number $m$ of steps with the explicit encoding of a correct answer $\sigma$ on its output stack, where
--   $$m\le B(L)\quad\text{for every real }L\ge|\mathrm{enc}(x)|.$$
--   So the bound at $L$ covers every promised input of length at most $L$, the source's convention for real arguments. Nothing is required outside $P$; every output symbol is written by machine steps.
--   3. **Time classes.** $A$ solves the problem in time $O(F)$ (resp. $o(F)$) if it solves it within some bound $B$ with $B=O(F)$ (resp. $B=o(F)$) as the length tends to infinity.
--
--   These notions express the deterministic running-time statements of §4.1, including lower bounds of the form "no deterministic algorithm runs in time $o(T)$".
--
--   **Formalization Note** The machine model is Mathlib's bundled `FinTM2` with `TM2OutputsInTime`; the problems reuse the published equilibrium predicates `IsEpsApproxNash` and `IsWeakNash` on the published table and profile interpretations.
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, §4.1 running-time convention, PDF pp. 22–23 (printed pp. 21–22); §2 computational convention, PDF p. 6 (printed p. 5)

import Definitions.Def_NashAmplification_Filtering_Encoding

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering.Supplement
open OnlineCRS.Combine

/-! Deterministic search solvers with operational running-time bounds.
Deng, Li, Wang, Zhang, STOC 2027 submission #120, §4.1, PDF 22–23 (printed 21–22):
"Running-time bounds are nondecreasing and apply to inputs of length at most their argument.
We extend these bounds to positive real arguments using the same convention."

A solver is a fixed bundled Mathlib `FinTM2` machine whose input and output stack alphabets are
the published fixed alphabet `Sym`. Its input is the published encoding of a game; it must halt
with the published encoding `encProfile σ` of an explicit rational profile `σ` on its output
stack. The number of machine steps counts every output symbol written. -/

/-- The `k`-player input problem: `σ` is a δ-approximate Nash equilibrium of the complete-table
game `G` (payoffs in `[0,1]` are built into `Table`), with one probability list per player. -/
def IsDeltaANEOf {k : ℕ} (δ : ℝ) (G : Table k) (σ : RawProfile k) : Prop :=
  σ.sizes = G.sizes ∧
    DGPNash.WellSupported.IsEpsApproxNash G.utility (σ.on G.counts) δ

/-- `H` is a symmetric binary-payoff `C`-player game: all players share `n ≥ 1` actions, and the
uniform payoff table is symmetric under player permutations and takes only the values `0`, `1`. -/
def IsSymBinaryTable (C : ℕ) (H : Table C) : Prop :=
  ∃ n : ℕ, 0 < n ∧ H.sizes = List.replicate C n ∧
    IsSymmetric (uniformUtility H n) ∧ IsBinary (uniformUtility H n)

/-- The target problem: `σ` is an `(ε, η)`-weak approximate Nash equilibrium of the uniform game
`H`, with `n` probabilities for each of the `C` players. -/
def IsWeakANEOf {C : ℕ} (ε η : ℝ) (H : Table C) (σ : RawProfile C) : Prop :=
  ∃ n : ℕ, H.sizes = List.replicate C n ∧ σ.sizes = List.replicate C n ∧
    RubinsteinNash.WeakNash.IsWeakNash (uniformUtility H n) (uniformProfile σ n) ε η

/-- The deterministic machine `A` solves the search problem `R` on the promised inputs `P`
within the running-time bound `B`: on every promised input `x` it halts after at most `m` steps
with the explicit output `encProfile σ` of a correct answer `σ`, where `m ≤ B L` for every real
`L` at least the input length `|enc x|` (the bound at `L` applies to all inputs of length at
most `L`). Nothing is required on inputs outside the promise. -/
def SolvesWithin {α : Type} {C : ℕ} (A : Turing.TM2ComputableAux Sym Sym)
    (enc : α → List Sym) (P : α → Prop) (R : α → RawProfile C → Prop) (B : ℝ → ℝ) : Prop :=
  ∀ x, P x → ∃ σ : RawProfile C, R x σ ∧ ∃ m : ℕ,
    (∀ L : ℝ, ((enc x).length : ℝ) ≤ L → (m : ℝ) ≤ B L) ∧
    Nonempty (Turing.TM2OutputsInTime A.tm ((enc x).map A.inputAlphabet.symm)
      (some ((encProfile σ).map A.outputAlphabet.symm)) m)

/-- `A` solves `R` on `P` in time `O(F)`: within some running-time bound `B` with
`B = O(F)` as the length tends to infinity (a finite constant and a finite cutoff). -/
def SolvesInBigO {α : Type} {C : ℕ} (A : Turing.TM2ComputableAux Sym Sym)
    (enc : α → List Sym) (P : α → Prop) (R : α → RawProfile C → Prop) (F : ℝ → ℝ) : Prop :=
  ∃ B : ℝ → ℝ, SolvesWithin A enc P R B ∧ B =O[Filter.atTop] F

/-- `A` solves `R` on `P` in time `o(F)`: within some running-time bound `B` with
`B = o(F)` as the length tends to infinity. -/
def SolvesInLittleO {α : Type} {C : ℕ} (A : Turing.TM2ComputableAux Sym Sym)
    (enc : α → List Sym) (P : α → Prop) (R : α → RawProfile C → Prop) (F : ℝ → ℝ) : Prop :=
  ∃ B : ℝ → ℝ, SolvesWithin A enc P R B ∧ B =o[Filter.atTop] F

end NashAmplification.Filtering.Supplement


