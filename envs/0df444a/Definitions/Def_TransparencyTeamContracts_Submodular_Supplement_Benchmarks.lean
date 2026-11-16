-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Benchmarks
-- name    : TransparencyTeamContracts_Submodular_Supplement_Benchmarks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:10:56.859047+00:00
-- url     : https://prove2.me/theorems/e85932ed-2f4c-4900-888d-141a00e9f901
-- title:
--   Rescaled technologies, weights, utilities and exact algorithm constants
-- statement:
--   Appendix D uses finite nonnegative monotone submodular technologies $f:2^{[n]}\to\mathbb R_{\ge0}$, allowing $f(\varnothing)>0$ and rewards above one. With nonnegative costs, put $w_i=\sqrt{c_i}$, $W(S)=\sum_{i\in S}w_i$, and let $\kappa(S)$ and $g(S)$ be the total share and principal utility of the base minimum-payment contract. These formulas are used for feasible teams; positive cost with zero marginal remains infeasible in the base predicate. The initialization value $M$ is the maximum over the empty team and feasible singletons.
--
--   The omega constant is the unique root $\varpi\in(0,1)$ of $\varpi e^\varpi=1$, represented by $\inf\{x\ge0:xe^x\ge1\}$, and $\gamma_\star=1-\varpi$. The numerical parameters are
--   $$\eta(\zeta)=\frac{((\zeta/20)^2/1000)^3}{32},\quad \tau(\epsilon)=\min\{1/10,\epsilon/20\},\quad \delta(\tau)=\eta(\tau/2)^2/12.$$
--   The module also defines $\psi_H(v)=\max\{v-W(H)\sqrt v,0\}$, support predicates, and the explicit scale, mesh, refill, multiplier and large-set enumeration counts from Appendix D. The query budgets multiply these actual finite loop counts; all domains are imposed by the corresponding theorem.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Appendix D, printed pp. 33–46 (PDF pp. 35–48)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

open Finset
open scoped Classical

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Appendix D permits reward rescaling above one and a positive empty baseline. -/
def IsTechnology {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  Monotone f ∧ (∀ S, 0 ≤ f S) ∧ SubsamplingSM.Offline.IsSubmodular f

noncomputable def weight {n : ℕ} (c : Fin n → ℝ) (i : Fin n) : ℝ := Real.sqrt (c i)
noncomputable def W {n : ℕ} (c : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, weight c i
noncomputable def kappa {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ := ∑ i, minimumContract f c S i
noncomputable def g {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ := principalUtility f (minimumContract f c S) S

/-- The empty team is always included; infeasible singletons are omitted. -/
noncomputable def initialValue {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) : ℝ :=
  max (f ∅) (Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset (Option (Fin n))).Nonempty)
    (fun j => match j with
      | none => f ∅
      | some i => if IsMinimumTeam f c {i} then g f c {i} else f ∅))

/-- A feasibility certificate includes all incentives, not merely a payoff. -/
def Supported {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  IsContract α ∧ (∀ i, i ∉ S → α i = 0) ∧
  (∀ i ∈ S, c i ≤ α i * teamMarginal f S i)

/-- Supports used in Appendix D need not have total share at most one (D.4). -/
def SupportsOn {n : ℕ} (f : Finset (Fin n) → ℝ) (c α : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop := ∀ i ∈ S, 0 ≤ α i ∧ α i ≤ 1 ∧
      c i ≤ α i * teamMarginal f S i

/-- The omega constant, specified without a floating point approximation. -/
noncomputable def omega : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ 1 ≤ x * Real.exp x}
noncomputable def gamma : ℝ := 1 - omega
noncomputable def eta (ζ : ℝ) : ℝ := ((ζ / 20) ^ 2 / 1000) ^ 3 / 32
noncomputable def tau (ε : ℝ) : ℝ := min (1 / 10) (ε / 20)
noncomputable def delta (τ : ℝ) : ℝ := eta (τ / 2) ^ 2 / 12
noncomputable def psi {n : ℕ} (c : Fin n → ℝ) (H : Finset (Fin n)) (v : ℝ) : ℝ :=
  max (v - W c H * Real.sqrt v) 0

/-- Explicit finite budgets in Appendix D; ceilings affect only accounting. -/
noncomputable def refillRounds (ζ : ℝ) : ℕ := ⌈112 / (3 * (ζ / 20) ^ 2)⌉₊ + 2
noncomputable def rewardGuesses (ζ Fmin Fmax : ℝ) : ℕ :=
  ⌊Real.log (Fmax / Fmin) / Real.log (1 + (ζ / 20) ^ 2 / 1000)⌋₊ + 1
noncomputable def weightGuesses (ζ : ℝ) : ℕ :=
  ⌈7 / (12 * ((ζ / 20) ^ 2 / 1000))⌉₊ + 1
noncomputable def multiplierGuesses (τ : ℝ) : ℕ :=
  ⌊Real.log 3 / Real.log (1 + τ / 12)⌋₊ + 1
noncomputable def largeGuesses (n : ℕ) (τ : ℝ) : ℕ :=
  ∑ h ∈ Finset.range (min n ⌈1 / delta τ⌉₊ + 1), Nat.choose n h

/-- Query accounting from the finite loops, before a uniform absolute constant:
all prefixes plus all scale/mesh/refill calls. No exponent is allowed to depend on f. -/
noncomputable def smallQueryBudget (n : ℕ) (ζ lo hi : ℝ) : ℕ :=
  (n + 1) ^ 3 + rewardGuesses ζ lo hi * weightGuesses ζ * refillRounds ζ *
    ((n + 1) ^ 2 + n + 1)
noncomputable def mainQueryBudget (n : ℕ) (ε : ℝ) : ℕ :=
  (n + 1) ^ 2 + largeGuesses n (tau ε) * multiplierGuesses (tau ε) *
    (smallQueryBudget n (tau ε / 2) 1 (6 * (n + 1)) + (n + 1) ^ 2)

end TransparencyTeamContracts.Submodular.Supplement


