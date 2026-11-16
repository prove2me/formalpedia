-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
-- name    : ProcurementPoA_DeterministicCap_Supplement_StandardAuction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:23.230669+00:00
-- url     : https://prove2.me/theorems/fc70d009-4d84-4141-9789-d81dc2e04ee3
-- title:
--   Standard and restricted-bid procurement auctions
-- statement:
--   There are $N=n+1$ suppliers with independent private cost laws $D_i$ and mixed bid kernels $\sigma_i(c,db)$. A measurable tie rule selects a lowest bidder. Write $x_i(b)$ for supplier $i$'s interim winning probability. Every lowest bid is accepted and the winner is paid her bid; there is no outside option. The utility is
--   $$u_i(c,b)=(b-c)x_i(b).$$
--   For a bid set $A$, a Bayes–Nash equilibrium has no bids below cost, puts probability one on $A$ at every declared possible cost, and almost every used bid beats every deviation $a\in A$. The standard auction uses $A=\mathbb R$; the restricted auction uses $A=[L,U]$.
--
--   Expected social cost averages the winner's cost over independent costs, mixed bids and randomized ties. The optimum is the published expected minimum cost. The standard auction's price of anarchy on $[L,U]$ is
--   $$\sup_{n,D,\tau,\sigma:\ D_i\subseteq[L,U],\ \sigma\text{ a standard BNE}}\frac{\mathrm{SC}}{\mathrm{SC}_{\mathrm{OPT}}}.$$
--   An instance with no equilibrium contributes no ratio. The instance-specific supremum fixes its cost laws and tie rule. For arbitrary deterministic real costs, the constructor gives singleton type sets and Dirac laws, and social cost is the signed real sum $\sum_i c_i\Pr(i\text{ wins})$.
--
--   These objects distinguish the uncapped auction from the published deterministic-cap auction and provide the common interface for §3–§4.
--
--   **Formalization Note** Nonnegative expectations and suprema use $\mathbb R_{\ge0}\cup\{+\infty\}$. The deterministic signed sum is used for Lemma 3.1 so negative costs are preserved. Finite positive cost intervals ensure that every ratio used in the other statements has a finite, strictly positive denominator. The base model supplies the general independent-type, mixed-kernel and tie-rule structures.
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, §2–§4, printed pp. 4–6 (PDF pp. 6–8), including Lemma 3.1

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Every lowest bid is accepted; no cap or outside option. -/
noncomputable def standardUtility {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) (c b : ℝ) : ℝ :=
  (b - c) * (interimWin D τ σ i b).toReal

/-- Equilibrium with both used bids and deviations in A; no underbidding. -/
def IsBidSetBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (A : Set ℝ) : Prop :=
  NoUnderbidding D σ ∧
  (∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c), b ∈ A) ∧
  (∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c),
    ∀ a ∈ A, standardUtility D τ σ i c a ≤ standardUtility D τ σ i c b)

/-- The standard auction tests every real deviation. -/
def IsStandardBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) : Prop := IsBidSetBNE D τ σ Set.univ

/-- Winner cost averaged over the tie kernel. Used only for nonnegative costs. -/
noncomputable def winnerCost {n : ℕ} (τ : TieRule n)
    (x : Suppliers n → ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (x i).1 * τ.select (fun j => (x j).2) {i}

noncomputable def standardSocialCost {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) : ℝ≥0∞ := ∫⁻ x, winnerCost τ x ∂(playLaw D σ)

/-- Dirac private costs, with no sign restriction. -/
noncomputable def deterministicTypes {n : ℕ} (c : Suppliers n → ℝ) : IndependentTypes n where
  types i := {c i}
  measurable_types _ := measurableSet_singleton _
  law i := Measure.dirac (c i)
  probability _ := inferInstance
  concentrated i := by simp

noncomputable def winProbability {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) : ℝ≥0∞ :=
  ∫⁻ x, τ.select (fun j => (x j).2) {i} ∂(playLaw D σ)

/-- A finite signed sum, so Lemma 3.1 includes negative deterministic costs. -/
noncomputable def deterministicSocialCost {n : ℕ} (c : Suppliers n → ℝ)
    (τ : TieRule n) (σ : MixedProfile n) : ℝ :=
  ∑ i, c i * (winProbability (deterministicTypes c) τ σ i).toReal

noncomputable def standardInstancePoA {n : ℕ} (D : IndependentTypes n)
    (τ : TieRule n) : ℝ≥0∞ :=
  sSup {q | ∃ σ : MixedProfile n, IsStandardBNE D τ σ ∧
    q = standardSocialCost D τ σ / optimalSocialCost D}

/-- All finite populations, all independent laws, all ties and mixed equilibria. -/
noncomputable def standardPoA (L U : ℝ) : ℝ≥0∞ :=
  sSup {q | ∃ (n : ℕ) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n),
    InCostInterval D L U ∧ IsStandardBNE D τ σ ∧
    q = standardSocialCost D τ σ / optimalSocialCost D}

end ProcurementPoA.DeterministicCap.Supplement


