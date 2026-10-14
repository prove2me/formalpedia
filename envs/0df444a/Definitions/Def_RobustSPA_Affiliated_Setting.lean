-- Prove2me | Definitions.Def_RobustSPA_Affiliated_Setting
-- name    : RobustSPA_Affiliated_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:03.697694+00:00
-- url     : https://prove2.me/theorems/51a8070b-40b8-4329-8047-bfa651ad00df
-- title:
--   §4.1, pp. 18–19 — exchangeable laws (Definition 3), affiliation (Definition 4), the class 𝓕_aff, and F^(1)_k (Definition 5), on top of the shared model RobustSPA.IID.Setting
-- statement:
--   This file adds to the shared model of Anunrojwong, Balseiro and Besbes (the module `RobustSPA.IID.Setting`: the type cube $[0,1]^n$, DSIC mechanisms, the regret (2), the minimax regret (3), $\mathcal F_{\mathrm{all}}$, $\mathcal F_{\mathrm{iid}}$, the order-statistic CDFs $F^{(1)}_n$, $F^{(2)}_n$, the second-price auction with random reserve, the $r^*$-equation, $\Phi^*_n$ and the isorevenue CDF) the objects of §4.1 that concern dependent valuations.
--
--   - A law $F$ of $(v_1,\dots,v_n)$, giving full mass to $[0,1]^n$, is **exchangeable** (Definition 3) if for every permutation $\sigma$ of $\{1,\dots,n\}$ the vector $(v_{\sigma(1)},\dots,v_{\sigma(n)})$ has the same law as $(v_1,\dots,v_n)$.
--   - A set $A\subseteq\mathbb R^n$ is **increasing** if its indicator is nondecreasing. A set $S$ is a **sublattice** if $v,v'\in S$ implies that the componentwise minimum $v\wedge v'$ and maximum $v\vee v'$ lie in $S$.
--   - $F$ is **affiliated** (Definition 4) if $\Pr_F(A\cap B\mid S)\ge\Pr_F(A\mid S)\Pr_F(B\mid S)$ for all increasing $A,B$ and every sublattice $S$. Here this is written in the cross-multiplied form
--   $$F(A\cap S)\,F(B\cap S)\le F(A\cap B\cap S)\,F(S).$$
--   - $\mathcal F_{\mathrm{aff}}$ (p. 19) is the class of exchangeable and affiliated laws on $[0,1]^n$.
--   - For $k\le n$, $F^{(1)}_k(t)=\Pr_F(\max(v_1,\dots,v_k)\le t)$ (Definition 5); for an exchangeable $F$ any $k$ coordinates give the same law, so the first $k$ are used.
--
--   These objects, together with the shared model, are used by every statement of the mission.
--
--   **Formalization Note.** Affiliation is cross-multiplied by $F(S)^2$, which makes it vacuous when $F(S)=0$ (where the conditional probability is undefined), and it is required for measurable $A,B,S$, the sets for which the probabilities are defined. "Increasing" is Lean's `IsUpperSet` for the coordinatewise order on $\mathbb R^n$, and $\wedge,\vee$ are the coordinatewise `⊓`, `⊔`. Exchangeability is invariance of the law under the coordinate permutations $v\mapsto v\circ\sigma$.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, pp. 18–19, Definitions 3, 4, 5, class 𝓕_aff

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.Affiliated

open MeasureTheory

/-- Exchangeable laws on `[0,1]ⁿ` (Definition 3, p. 18): invariant under every permutation of the
coordinates. -/
def Fexc (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ RobustSPA.IID.Fall n ∧ ∀ σ : Equiv.Perm (Fin n), μ.map (fun v => v ∘ σ) = μ}

set_option linter.dupNamespace false in
/-- Affiliation (Definition 4, p. 18), cross-multiplied by `μ(S)²`: for all measurable increasing sets
`A`, `B` and every measurable sublattice `S`, `μ(A ∩ S) μ(B ∩ S) ≤ μ(A ∩ B ∩ S) μ(S)`, i.e.
`Pr(A ∩ B | S) ≥ Pr(A | S) Pr(B | S)` whenever `μ(S) > 0`. -/
def Affiliated {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ A B S : Set (Fin n → ℝ), MeasurableSet A → MeasurableSet B → MeasurableSet S →
    IsUpperSet A → IsUpperSet B → (∀ v ∈ S, ∀ w ∈ S, v ⊓ w ∈ S ∧ v ⊔ w ∈ S) →
    μ (A ∩ S) * μ (B ∩ S) ≤ μ (A ∩ B ∩ S) * μ S

/-- The class `𝓕_aff` (p. 19): exchangeable and affiliated laws supported on `[0,1]ⁿ`. -/
def Faff (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ Fexc n ∧ Affiliated μ}

/-- `F^(1)_k(t) = Pr_F(max(v₁, …, v_k) ≤ t)` (Definition 5, p. 19): the CDF of the maximum of the first
`k` valuations. -/
noncomputable def F1k {n : ℕ} (k : ℕ) (μ : Measure (Fin n → ℝ)) (t : ℝ) : ℝ :=
  (μ {u | ∀ i : Fin n, (i : ℕ) < k → u i ≤ t}).toReal

end RobustSPA.Affiliated


