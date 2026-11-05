-- Prove2me | Definitions.Def_MenuCostPricing_Rational
-- name    : MenuCostPricing_Rational
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:28.960622+00:00
-- url     : https://prove2.me/theorems/999c9cff-91c6-4269-8629-bf44cb51bc0b
-- title:
--   Theorem 3.1, p.14 — rational instances and the input size $|I|$
-- statement:
--   A **rational instance** has the data of an instance with prices, weights, masses and $f,v,B$ in $\mathbb Q$ (inventories and support points in $\mathbb N$). Its **input size** $|I|$ is
--   $$
--   |I|=n+L+T+\sum_{i,\ell}\mathrm{bit}(p_{i\ell})+\sum_{t,i,\ell}\mathrm{bit}(w^t_{i\ell})+\sum_i(\mathrm{size}(u^1_i)+1)+\sum_t\sum_{\nu\in S_t}\big(\mathrm{size}(\nu)+1+\mathrm{bit}(\Pr[N_t=\nu])\big)+\mathrm{bit}(f)+\mathrm{bit}(v)+\mathrm{bit}(B),
--   $$
--   where $\mathrm{bit}(q)$ is the binary length of numerator and denominator plus a sign bit (the published `WeightedCongestionBR.bitLen`) and $\mathrm{size}$ the binary length of a natural number.
--
--   The running-time clause of Theorem 3.1 is stated for rational instances with this size.
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.1, p.14 ("|I| denotes the input size in its binary representation")

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_WeightedCongestionBR_bitLen

namespace MenuCostPricing

open WeightedCongestionBR (bitLen)

/-- A rational DPMC instance: the data of `Instance` in `ℚ` (inventories and support points stay in
`ℕ`). This is what has an input size `|I|` in binary.

**Formalization Note.** Theorem 3.1 bounds the running time in "the input size in its binary
representation" (p.14), which needs a finite representation of the numbers; the accuracy guarantee
holds for real data as well. -/
structure RatInstance (n L T : ℕ) where
  p : Fin n → Fin L → ℚ
  w : Fin T → Fin n → Fin L → ℚ
  u : Fin n → ℕ
  supp : Fin T → List ℕ
  mass : Fin T → ℕ → ℚ
  f : ℚ
  v : ℚ
  B : ℚ

/-- The real instance with the same data. -/
def RatInstance.toReal {n L T : ℕ} (J : RatInstance n L T) : Instance n L T where
  p := fun i ℓ => (J.p i ℓ : ℝ)
  w := fun t i ℓ => (J.w t i ℓ : ℝ)
  u := J.u
  supp := J.supp
  mass := fun t ν => (J.mass t ν : ℝ)
  f := (J.f : ℝ)
  v := (J.v : ℝ)
  B := (J.B : ℝ)

/-- **The input size `|I|`** (p.14, "the input size in its binary representation"): `n + L + T`, the
bit lengths of all prices, weights, inventories, support points and their masses, and of `f`, `v`,
`B`.

**Formalization Note.** `bitLen` is the published `WeightedCongestionBR.bitLen`,
`1 + size|num| + size den`: numerator and denominator in binary, plus a sign bit. -/
def RatInstance.inputSize {n L T : ℕ} (J : RatInstance n L T) : ℕ :=
  n + L + T + (∑ i, ∑ ℓ, bitLen (J.p i ℓ)) + (∑ t, ∑ i, ∑ ℓ, bitLen (J.w t i ℓ)) +
    (∑ i, (Nat.size (J.u i) + 1)) +
    (∑ t, ((J.supp t).map (fun ν => Nat.size ν + 1 + bitLen (J.mass t ν))).sum) +
    bitLen J.f + bitLen J.v + bitLen J.B

end MenuCostPricing


