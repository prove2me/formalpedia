-- Prove2me | Definitions.Def_FixedPriceTrade_Supplement_R2
-- name    : FixedPriceTrade_Supplement_R2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:42.66964+00:00
-- url     : https://prove2.me/theorems/ce3b98a5-58eb-47bf-aa6d-137db2b88936
-- title:
--   Normalized two-unit bodies, $\Gamma_0(z)$, admissible bodies and $\mathcal R_2(Z,Y)$
-- statement:
--   Let $Z=(Z_1,Z_2)$ (buyer body) and $Y=(Y_1,Y_2)$ (seller body) be independent bounded nonnegative random vectors with $Z_1\ge Z_2$ and $Y_1\le Y_2$. Define
--   $$
--   \Gamma_0(z)=\sum_{i=1}^2\mathbb E\Big[\mathbf 1\{Y_i<z\}\big(1+(Z_i-Y_i)\mathbf 1\{z\le Z_i\}\big)\Big],\qquad
--   \mathcal R_2(Z,Y)=\frac{2+\mathbb E(Y_1+Y_2)}{2+\sum_{i=1}^2\mathbb E\max\{Z_i,Y_i\}}.
--   $$
--   The pair $(Z,Y)$ is called **admissible bodies** if $\Gamma_0(z)\le2$ for every price $z$.
--
--   In the normalized model the buyer has an escaping atom whose first moment is one per unit (the constant $1$ in each gain term); seller acceptance is strict and buyer acceptance inclusive. Every two-unit instance reduces to admissible bodies without raising its ratio (Proposition 13.1 of the paper).
--
--   **Formalization Note** Bodies are laws $\nu_Z,\nu_Y$ on $\mathbb R^2$ carried by some square $[0,R]^2$, with the orders almost surely; independence is the product law. "Every price" is every real $z$, which is the same as every $z\ge0$ because the strict seller indicator vanishes for $z\le0$.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), §13.2, (57) and "admissible bodies", p.27 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- **Buyer bodies** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of Fixed-Price
Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §13.2, p.27: `Z = (Z₁, Z₂)` is a
bounded nonnegative random vector with `Z₁ ≥ Z₂`. `νZ` is its law on `ℝ²`.

**Formalization Note.** "Bounded nonnegative" is: some square `[0, R]²` carries all the mass; the
order holds almost surely. -/
def IsBuyerBody (νZ : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure νZ ∧ (∃ R : ℝ, νZ (Icc 0 R ×ˢ Icc 0 R)ᶜ = 0) ∧ ∀ᵐ z ∂νZ, z.2 ≤ z.1

/-- **Seller bodies** (§13.2, p.27): `Y = (Y₁, Y₂)` is a bounded nonnegative random vector with
`Y₁ ≤ Y₂` (an "ordered seller distribution" of the normalized model). -/
def IsSellerBody (νY : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure νY ∧ (∃ R : ℝ, νY (Icc 0 R ×ˢ Icc 0 R)ᶜ = 0) ∧ ∀ᵐ y ∂νY, y.1 ≤ y.2

/-- The per-unit gain in (57): `1{yᵢ < z}(1 + (zᵢ − yᵢ) 1{z ≤ zᵢ})` — strict seller acceptance,
inclusive buyer acceptance (p.27). -/
noncomputable def gainBody (zi yi z : ℝ) : ℝ :=
  (if yi < z then 1 else 0) * (1 + (zi - yi) * (if z ≤ zi then 1 else 0))

/-- `Γ₀(z) = Σᵢ E[1{Yᵢ < z}(1 + (Zᵢ − Yᵢ) 1{z ≤ Zᵢ})]` ((57), p.27), the buyer and seller bodies
independent (product law `νZ.prod νY`). -/
noncomputable def Gamma0 (νZ νY : Measure (ℝ × ℝ)) (z : ℝ) : ℝ :=
  ∫ x, gainBody x.1.1 x.2.1 z + gainBody x.1.2 x.2.2 z ∂(νZ.prod νY)

/-- **Admissible bodies** (p.27): buyer and seller bodies with `Γ₀(z) ≤ 2` for every price.

**Formalization Note.** "Every price" is every real `z`; for `z ≤ 0` the strict seller indicator
vanishes almost surely, so this is the same as every `z ≥ 0`. -/
def IsAdmissibleBodies (νZ νY : Measure (ℝ × ℝ)) : Prop :=
  IsBuyerBody νZ ∧ IsSellerBody νY ∧ ∀ z : ℝ, Gamma0 νZ νY z ≤ 2

/-- The normalized two-unit ratio ((57), p.27):
`R₂(Z, Y) = (2 + E(Y₁ + Y₂)) / (2 + Σᵢ E max{Zᵢ, Yᵢ})`. The denominator is at least `2`. -/
noncomputable def R2 (νZ νY : Measure (ℝ × ℝ)) : ℝ :=
  (2 + ∫ y, y.1 + y.2 ∂νY) / (2 + ∫ x, max x.1.1 x.2.1 + max x.1.2 x.2.2 ∂(νZ.prod νY))

end FixedPriceTrade.Supplement


