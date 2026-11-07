-- Prove2me | Definitions.Def_OWFLocalDesc_pointProb
-- name    : OWFLocalDesc_pointProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:18.236531+00:00
-- url     : https://prove2.me/theorems/b90bc139-c02d-4015-9f9a-59be6029d821
-- title:
--   Point-vector probability $\mu^m(x)$ (Definition 2.6)
-- statement:
--   For a PAC-style sampler $D=(\mu,Q)$ and points $x_1,\dots,x_m\in\{0,1\}^n$,
--   $$\mu^m(x)=\prod_{i=1}^m\Pr_\rho\big[\mu(1^n;\rho)=x_i\big].$$
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.6, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_PACSampler
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Point-vector probability `µ^m(x)` (Definition 2.6).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.6, p.13: "µ^m(x) = ∏_{i=1}^m Pr[µ(1^n; ρ) = x_i]". -/
noncomputable def pointProb (D : PACSampler) {m n : ℕ} (x : Fin m → Fin n → Bool) : ℝ :=
  open Classical in
  ∏ i : Fin m,
    ((Finset.univ.filter fun ρ : Fin (D.rμ n) → Bool => D.point n ρ = x i).card : ℝ) /
      (2 : ℝ) ^ (D.rμ n)

end OWFLocalDesc


