-- Prove2me | Definitions.Def_BilatMatch_InX
-- name    : BilatMatch_InX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:10:13.327636+00:00
-- url     : https://prove2.me/theorems/f5377f56-de12-480a-bcfe-b3c08939d568
-- title:
--   Allocation polytope $X$, revenue functional $\Lambda$ and Lagrangian $L_\alpha$
-- statement:
--   For finitely many agents with finitely supported priors let $\Theta$ be the finite set of type profiles. An allocation $x$ assigns to each profile edge trade probabilities. The **feasible, BIC-implementable allocation polytope** is
--   $$X=\{x:\ x(\theta)\in\operatorname{conv}\{1_M:M\in\mathcal F\}\ (\theta\in\Theta),\ \bar x_{B_i}\text{ nondecreasing},\ \bar x_{S_j}\text{ nonincreasing on the supports}\}.$$
--   For an allocation,
--   $$\Lambda(x)=\mathbb E\Big[\sum_i\phi_i(v_i)x_{B_i}\Big]-\mathbb E\Big[\sum_j\tau_j(c_j)x_{S_j}\Big],\qquad L_\alpha(x)=\mathrm{GFT}(x)+\alpha\Lambda(x).$$
--   The module also fixes the support report domain (each agent reports an atom of its prior) and says when a mechanism realizes $x$: its edge trade probabilities equal $x$ at every support profile.
--
--   **Formalization Note** Expectations are integrals under the product prior, which is concentrated on $\Theta$, so they are the finite weighted sums of the paper.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §2 Incentive Compatibility and Payments, p.6 (pdf p.8), Lemma 2.1 and eq. (3), p.7 (pdf p.9)

import Mathlib
import Definitions.Def_BilatMatch_Mechanism
import Definitions.Def_BilatMatch_virtualValue

open MeasureTheory

namespace BilatMatch

/-!
# The allocation polytope `X`, the revenue functional `Λ` and the Lagrangian `L_α`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §2 "Incentive Compatibility and Payments",
p.6 (pdf p.8), and Lemma 2.1, p.7 (pdf p.9). For markets with finitely many agents and finitely
supported priors.

**Formalization Note**
* An allocation is any `x : Profile B S → B × S → ℝ`; only its values at support profiles (every
  coordinate an atom of its prior) matter. `Θ` is `supportProfiles I`.
* Interim quantities and expectations are Bochner integrals under the product prior. For finitely
  supported priors the product prior is concentrated on the finite set `Θ` of support profiles, so
  each integrand is almost everywhere a finite simple function and every integral is the finite
  weighted sum of the paper (no junk value).
* Reports in a finite market range over the supports (`suppDomain`), as on p.6.
-/

variable {B S : Type*}

/-- The finite set `Θ` of type profiles: every value and cost is an atom of its prior. -/
def supportProfiles (I : Market B S) : Set (Profile B S) :=
  {θ | (∀ i, θ.1 i ∈ atoms (I.buyerLaw i)) ∧ ∀ j, θ.2 j ∈ atoms (I.sellerLaw j)}

/-- The support report domain: each agent reports an atom of its own prior (p.6). -/
def suppDomain (I : Market B S) : B ⊕ S → Set ℝ :=
  Sum.elim (fun i => atoms (I.buyerLaw i)) (fun j => atoms (I.sellerLaw j))

/-- An allocation: `x θ e` is the probability that edge `e` trades at profile `θ`. -/
abbrev Allocation (B S : Type*) := Profile B S → B × S → ℝ

variable [Fintype B] [Fintype S]

/-- Buyer `i`'s trade probability `x_{B_i}(θ) = ∑_j x_{ij}(θ)` under an allocation. -/
def allocXB (x : Allocation B S) (i : B) (θ : Profile B S) : ℝ := ∑ j, x θ (i, j)

/-- Seller `j`'s trade probability `x_{S_j}(θ) = ∑_i x_{ij}(θ)` under an allocation. -/
def allocXS (x : Allocation B S) (j : S) (θ : Profile B S) : ℝ := ∑ i, x θ (i, j)

/-- Buyer `i`'s interim trade probability at report `v` under an allocation. -/
noncomputable def allocInterimXB (I : Market B S) (x : Allocation B S) (i : B) (v : ℝ) : ℝ :=
  ∫ θ, allocXB x i (updateBuyer θ i v) ∂typeMeasure I

/-- Seller `j`'s interim trade probability at report `c` under an allocation. -/
noncomputable def allocInterimXS (I : Market B S) (x : Allocation B S) (j : S) (c : ℝ) : ℝ :=
  ∫ θ, allocXS x j (updateSeller θ j c) ∂typeMeasure I

/-- The edge-incidence vector `1_M ∈ {0,1}^E` of a matching `M`. -/
noncomputable def incidence (M : Set (B × S)) : B × S → ℝ := M.indicator 1

/-- The feasible, BIC-implementable allocation polytope `X` (p.6): `x(θ) ∈ conv{1_M : M ∈ F}` at
every `θ ∈ Θ`, buyers' interim trade probabilities nondecreasing and sellers' nonincreasing on
their supports. -/
def InX (I : Market B S) (x : Allocation B S) : Prop :=
  (∀ θ ∈ supportProfiles I, x θ ∈ convexHull ℝ (incidence '' I.family)) ∧
  (∀ i, MonotoneOn (allocInterimXB I x i) (atoms (I.buyerLaw i))) ∧
  (∀ j, AntitoneOn (allocInterimXS I x j) (atoms (I.sellerLaw j)))

/-- `GFT(x) = E[∑_{(i,j) ∈ E} (v_i − c_j) x_{ij}]` (p.6). -/
noncomputable def allocGFT (I : Market B S) (x : Allocation B S) : ℝ :=
  ∫ θ, ∑ᶠ e ∈ I.edges, (θ.1 e.1 - θ.2 e.2) * x θ e ∂typeMeasure I

/-- `Λ(x) = E[∑_i ϕ_i(v_i) x_{B_i}] − E[∑_j τ_j(c_j) x_{S_j}]` (Lemma 2.1, p.7). -/
noncomputable def Lambda (I : Market B S) (x : Allocation B S) : ℝ :=
  (∫ θ, ∑ i, virtualValue (I.buyerLaw i) (θ.1 i) * allocXB x i θ ∂typeMeasure I) -
    ∫ θ, ∑ j, virtualCost (I.sellerLaw j) (θ.2 j) * allocXS x j θ ∂typeMeasure I

/-- The matching-market Lagrangian `L_α(x) = GFT(x) + α Λ(x)` (p.7). -/
noncomputable def lagrangian (I : Market B S) (α : ℝ) (x : Allocation B S) : ℝ :=
  allocGFT I x + α * Lambda I x

/-- A mechanism realizes the allocation `x`: its edge trade probabilities equal `x` at every
support profile. -/
def Mechanism.Realizes {I : Market B S} (A : Mechanism I) (x : Allocation B S) : Prop :=
  ∀ θ ∈ supportProfiles I, ∀ e, A.x e θ = x θ e

end BilatMatch


