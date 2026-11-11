-- Prove2me | Definitions.Def_RandKSATSample_Main_TrialScheme
-- name    : RandKSATSample_Main_TrialScheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:01:35.0022+00:00
-- url     : https://prove2.me/theorems/28d6e226-6978-465e-9edb-26cde4609525
-- title:
--   The core heat-bath update: repeated trials until acceptance (law, output law, termination, expected cost, acceptance products) and the objects J_i, H_{σ,i}, L_{i,σ}(z), ν_j, π(· | σ_{−i}) of §6.1
-- statement:
--   One **trial** draws a candidate $z$ of a finite set $\Omega_i$, runs its tests, and either accepts $z$ or rejects; it has a cost. A trial is given by the joint law of its outcome (accepted $z$, or reject) and its cost. The **procedure** runs independent trials until the first acceptance and returns the accepted candidate; its cost is the sum of the costs of all trials it ran, rejected trials included. The quantities are the termination probability, the output law $\hat p(z)=\Pr[\text{the procedure returns }z]$, the expected total cost, and, for tests with coin probabilities $\nu_j(z)$, the acceptance product
--   $$A_z=\prod_{j<\ell(z)}(1-\nu_j(z)).$$
--
--   For the core heat-bath update of §6.1 (p. 56), fix a nice formula $\Phi$, a core block $B_i$ and a core assignment $\sigma$. $J_i=\{a\in\mathcal C^{\mathrm{good}}:\mathrm{vbl}(C_a)\cap B_i\neq\emptyset\}$ is the set of mixed clauses incident to $B_i$ (so $r_i=|J_i|$), $H_{\sigma,i}=D_\sigma\setminus J_i$, and for a candidate $z\in\Omega_i$, $L_{i,\sigma}(z)=D_{(\sigma_{-i},z)}\cap J_i$, where $(\sigma_{-i},z)$ is $\sigma$ with its block $B_i$ replaced by $z$. Listing $L_{i,\sigma}(z)=\{a_1,\dots,a_\ell\}$ in a test order and putting $F_0=H_{\sigma,i}$, $F_j=F_{j-1}\cup\{a_j\}$, the ideal violation probability of the $j$-th test is $\nu_j=\mu_{F_{j-1}}(B_{a_j})$ (p. 57). The target of the update is the conditional core marginal
--   $$\pi(z\mid\sigma_{-i})=\frac{\mu^{\mathrm{bad}}(\sigma_{-i},z)}{\sum_{u\in\Omega_i}\mu^{\mathrm{bad}}(\sigma_{-i},u)}.$$
--
--   **Formalization Note.** `trial : PMF (Option Ω × ℕ)`. The procedure is a Markov chain on (outcome so far, accumulated cost); a finished procedure stays put. Termination probability and output law are suprema over time of the laws after $t$ steps (monotone in $t$). The expected cost is $\sup_t\mathbb E[\text{cost after }t\text{ steps}]$ in $[0,\infty]$, so nonterminating runs are charged their unbounded cost. The test order is a list; `nuTest` is $0$-based ($\nu$ at position $j$ uses the clauses before position $j$) and $0$ past the end of the list. A block is indexed by the component $B_i$ itself.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), §6.1 (p. 56), Definition 6.1 and the proof of Proposition 6.2, pp. 57–58

import Mathlib
import Definitions.Def_RandKSATSample_Main_CoreChain

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# The core heat-bath update: repeated trials with approximate acceptance (Proposition 6.2)

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), §6.1 (p. 56: `J_i`, `H_{σ,i}`, `L_{i,σ}(z)`),
Definition 6.1 and the proof of Proposition 6.2, pp. 57–58.

One trial draws a candidate `z` from the finite set `Ω_i` and runs coin tests; it either accepts
(`some z`) or rejects (`none`), and it has a cost. A trial is given by the joint law
`trial : PMF (Option Ω × ℕ)` of its outcome and its cost. The procedure runs independent trials
until the first acceptance and returns the accepted candidate; its cost is the sum of the costs of
all trials it ran, rejected ones included.

The second part constructs, from the formula, the objects of §6.1 the update is built on: the
mixed clauses `J_i` incident to a block, the families `H_{σ,i}` and `L_{i,σ}(z)`, the ideal
violation probability `ν_j = µ_{F_{j−1}}(B_{a_j})` of each test, and the target law
`π(· | σ_{−i})` of the block update.
-/

variable {Ω : Type}

/-- One step of the procedure on the state (outcome so far, accumulated cost): a finished
procedure stays put; otherwise a fresh independent trial is run and its cost is added. -/
def procStep (trial : PMF (Option Ω × ℕ)) : Option Ω × ℕ → PMF (Option Ω × ℕ)
  | (some z, c) => PMF.pure (some z, c)
  | (none, c) => trial.map fun r => (r.1, c + r.2)

/-- The law of the procedure's state after `t` steps. -/
def procLaw (trial : PMF (Option Ω × ℕ)) : ℕ → PMF (Option Ω × ℕ)
  | 0 => PMF.pure (none, 0)
  | t + 1 => (procLaw trial t).bind (procStep trial)

/-- The probability that the procedure terminates. -/
def procHaltProb (trial : PMF (Option Ω × ℕ)) : ℝ≥0∞ :=
  ⨆ t, (procLaw trial t).toOuterMeasure {s | s.1.isSome}

/-- The law of the returned candidate: the probability that the procedure returns `z`. -/
def procOut (trial : PMF (Option Ω × ℕ)) (z : Ω) : ℝ :=
  (⨆ t, (procLaw trial t).toOuterMeasure {s | s.1 = some z}).toReal

/-- The expected total cost, `sup_t E[cost after t steps]` in `ℝ≥0∞` (nonterminating runs are
charged their unbounded cost). -/
def procExpCost (trial : PMF (Option Ω × ℕ)) : ℝ≥0∞ :=
  ⨆ t, ∑' s, procLaw trial t s * (s.2 : ℝ≥0∞)

/-- An acceptance probability `Π_{j < ℓ(z)} (1 − ν_j(z))` built from per-test violation
probabilities `ν_j(z)`. -/
def acceptProb (ℓ : Ω → ℕ) (ν : Ω → ℕ → ℝ) (z : Ω) : ℝ :=
  ∏ j ∈ Finset.range (ℓ z), (1 - ν z j)

/-! ## The objects of §6.1 -/

section core

variable {n m k : ℕ}

/-- The core assignment `(σ_{−i}, z)`: `σ` with its values on the block `B` replaced by `z`. -/
def replaceBlock (Φ : Formula n m k) (σ : BadAssign Φ) (B : Finset (Fin n))
    (z : PartAssign n B) : BadAssign Φ :=
  fun v => if h : v.1 ∈ B then z ⟨v.1, h⟩ else σ v

/-- `J_i = {a ∈ C_good : vbl(C_a) ∩ B_i ≠ ∅}`: the mixed clauses incident to the block `B`
(a good clause meeting a core block has both good and bad variables); `r_i = |J_i|`. -/
def Jblk (Φ : Formula n m k) (B : Finset (Fin n)) : Finset (Fin m) :=
  (Cgood Φ).filter fun a => (vbl Φ a ∩ B).Nonempty

/-- `H_{σ,i} = D_σ ∖ J_i`. -/
def Hfam (Φ : Formula n m k) (σ : BadAssign Φ) (B : Finset (Fin n)) : Finset (Fin m) :=
  Dsig Φ σ \ Jblk Φ B

/-- `L_{i,σ}(z) = D_{(σ_{−i}, z)} ∩ J_i`. -/
def Lset (Φ : Formula n m k) (σ : BadAssign Φ) (B : Finset (Fin n)) (z : PartAssign n B) :
    Finset (Fin m) :=
  Dsig Φ (replaceBlock Φ σ B z) ∩ Jblk Φ B

/-- The ideal violation probability of the test at position `j` (`0`-based) of the test order
`ord = [a_1, …, a_ℓ]`: `ν = µ_F(B_a)` with `a` the clause at position `j` and
`F = H_{σ,i} ∪ {clauses before it}`, i.e. the paper's `ν_j = µ_{F_{j−1}}(B_{a_j})`
(the value `0` past the end of the list). -/
def nuTest (Φ : Formula n m k) (σ : BadAssign Φ) (B : Finset (Fin n)) (ord : List (Fin m))
    (j : ℕ) : ℝ :=
  match ord[j]? with
  | some a => muF Φ (Hfam Φ σ B ∪ (ord.take j).toFinset) (Viol Φ a)
  | none => 0

/-- The target law of the block update, `π(z | σ_{−i}) = µbad(σ_{−i}, z) / Σ_{u ∈ Ω_i}
µbad(σ_{−i}, u)` for a candidate `z ∈ Ω_i`. -/
def condBlockLaw (Φ : Formula n m k) (σ : BadAssign Φ) (B : Finset (Fin n))
    (z : {z // z ∈ OmegaBlock Φ B}) : ℝ :=
  muBad Φ (replaceBlock Φ σ B z.1) /
    ∑ u : {u // u ∈ OmegaBlock Φ B}, muBad Φ (replaceBlock Φ σ B u.1)

end core

end

end RandKSATSample.Main


