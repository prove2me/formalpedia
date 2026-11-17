-- Prove2me | Definitions.Def_FixedPriceTrade_Supplement_rStar2
-- name    : FixedPriceTrade_Supplement_rStar2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:27.978792+00:00
-- url     : https://prove2.me/theorems/3fb1868d-decb-49ae-a228-eed4bff86f60
-- title:
--   The two-unit model: $M_2$, $O_2$, $\Gamma_2(z)$, $r^*_2$ and the symmetric subclass
-- statement:
--   A seller owns two units. The buyer's marginal values $(B_1,B_2)$ and the seller's marginal costs $(S_1,S_2)$ satisfy $B_1\ge B_2>0$ and $0<S_1\le S_2$ almost surely; the two vectors are independent and have finite first moments, while the coordinates within a vector may be dependent. A common price $z$ trades unit $i$ exactly when $S_i\le z\le B_i$. Define
--   $$
--   M_2=\mathbb E(S_1+S_2),\qquad O_2=\sum_{i=1}^2\mathbb E\max\{B_i,S_i\},\qquad \Gamma_2(z)=\sum_{i=1}^2\mathbb E\big[(B_i-S_i)\mathbf 1\{S_i\le z\le B_i\}\big],
--   $$
--   the welfare ratio $(M_2+\Gamma_2(z))/O_2$ of the price $z$, and
--   $$
--   r^*_2=\inf\frac{M_2+\sup_{z\ge0}\Gamma_2(z)}{O_2}
--   $$
--   over all such instances. The **symmetric subclass** requires $(B_1,B_2)$ and $(S_2,S_1)$ to have the same law; $r^*_{2,\mathrm{sym}}$ is its infimum. A law on $\mathbb R^2$ is **finitely supported** if a finite set carries all its mass.
--
--   This is the increasing submodular two-unit model in which Theorem D separates two units from one.
--
--   **Formalization Note** An instance is a pair of laws $\nu_B,\nu_S$ on $\mathbb R^2$; independence is the product $\nu_B\otimes\nu_S$. The per-unit gain is the published `BilateralRegret.GFT`, $(b-s)\mathbf 1\{s\le z\le b\}$. The symmetric condition is $\nu_B=$ the image of $\nu_S$ under the coordinate swap.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), §13.1, (56) and the symmetric subclass, p.26 (PDF p.26)

import Mathlib
import Definitions.Def_BilateralRegret_GFT

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- **A two-unit instance** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §13.1, p.26: the seller
owns two units; the buyer's marginal values and the seller's marginal costs satisfy
`B₁ ≥ B₂ > 0` and `0 < S₁ ≤ S₂`; the two vectors are independent, with finite first moments; their
coordinates may be dependent.

`νB` is the law of `(B₁, B₂)` and `νS` the law of `(S₁, S₂)`, both on `ℝ × ℝ`.

**Formalization Note.** Independence of the two vectors is encoded by using the product
`νB.prod νS` as the joint law in every quantity; the coordinates inside a vector are arbitrary
(any law on `ℝ²`). The orderings and positivity hold almost surely; finite first moments are
integrability of each coordinate. -/
def IsTwoUnitInstance (νB νS : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure νB ∧ IsProbabilityMeasure νS ∧
    (∀ᵐ b ∂νB, b.2 ≤ b.1 ∧ 0 < b.2) ∧ (∀ᵐ s ∂νS, 0 < s.1 ∧ s.1 ≤ s.2) ∧
    Integrable (fun b : ℝ × ℝ => b.1) νB ∧ Integrable (fun b : ℝ × ℝ => b.2) νB ∧
    Integrable (fun s : ℝ × ℝ => s.1) νS ∧ Integrable (fun s : ℝ × ℝ => s.2) νS

/-- `M₂ = E(S₁ + S₂)` ((56), p.26). -/
noncomputable def M2 (νS : Measure (ℝ × ℝ)) : ℝ := ∫ s, s.1 + s.2 ∂νS

/-- `O₂ = Σᵢ E max{Bᵢ, Sᵢ}` ((56), p.26), over the product law. -/
noncomputable def O2 (νB νS : Measure (ℝ × ℝ)) : ℝ :=
  ∫ x, max x.1.1 x.2.1 + max x.1.2 x.2.2 ∂(νB.prod νS)

/-- `Γ₂(z) = Σᵢ E[(Bᵢ − Sᵢ) 1{Sᵢ ≤ z ≤ Bᵢ}]` ((56), p.26), inclusive at both ends as in §3,
through the published `BilateralRegret.GFT z s b = (b − s)·𝕀{s ≤ z ≤ b}` applied to each unit. -/
noncomputable def Gamma2 (νB νS : Measure (ℝ × ℝ)) (z : ℝ) : ℝ :=
  ∫ x, BilateralRegret.GFT z x.2.1 x.1.1 + BilateralRegret.GFT z x.2.2 x.1.2 ∂(νB.prod νS)

/-- The welfare ratio `(M₂ + Γ₂(z))/O₂` of the common price `z` (§13.1, p.26). -/
noncomputable def priceRatio2 (νB νS : Measure (ℝ × ℝ)) (z : ℝ) : ℝ :=
  (M2 νS + Gamma2 νB νS z) / O2 νB νS

/-- The best common-price welfare ratio `(M₂ + sup_{z ≥ 0} Γ₂(z))/O₂` of an instance ((56)).

**Formalization Note.** On an instance `0 ≤ Γ₂(z) ≤ Σᵢ E(Bᵢ − Sᵢ)₊ < ∞`, so the supremum over the
nonempty set `z ≥ 0` is a genuine real supremum. -/
noncomputable def bestRatio2 (νB νS : Measure (ℝ × ℝ)) : ℝ :=
  (M2 νS + sSup (Gamma2 νB νS '' Ici 0)) / O2 νB νS

/-- `r∗₂ = inf (M₂ + sup_{z≥0} Γ₂(z))/O₂` over all two-unit instances ((56), p.26).

**Formalization Note.** Every ratio is nonnegative, so the infimum is over a nonempty set that is
bounded below. -/
noncomputable def rStar2 : ℝ :=
  sInf {r : ℝ | ∃ νB νS : Measure (ℝ × ℝ), IsTwoUnitInstance νB νS ∧ bestRatio2 νB νS = r}

/-- The symmetric subclass (p.26): `(B₁, B₂)` and `(S₂, S₁)` have the same law, i.e. the buyer
law is the image of the seller law under the coordinate swap. -/
def IsSymmetricInstance (νB νS : Measure (ℝ × ℝ)) : Prop :=
  νB = νS.map Prod.swap

/-- `r∗_{2,sym}`, the infimum over symmetric instances (p.26). -/
noncomputable def rStar2Sym : ℝ :=
  sInf {r : ℝ | ∃ νB νS : Measure (ℝ × ℝ), IsTwoUnitInstance νB νS ∧
    IsSymmetricInstance νB νS ∧ bestRatio2 νB νS = r}

/-- A law on `ℝ²` is **finitely supported** if some finite set carries all its mass (Theorem D). -/
def IsFinitelySupported (ν : Measure (ℝ × ℝ)) : Prop :=
  ∃ t : Set (ℝ × ℝ), t.Finite ∧ ν tᶜ = 0

end FixedPriceTrade.Supplement


