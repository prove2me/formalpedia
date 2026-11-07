-- Prove2me | Definitions.Def_OWFLocalDesc_HasUniformPoints
-- name    : OWFLocalDesc_HasUniformPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:27.775436+00:00
-- url     : https://prove2.me/theorems/07c4e386-96b6-4bef-a0d7-a30437daa5a9
-- title:
--   A PAC-style sampler with uniform points
-- statement:
--   A PAC-style sampler $D=(\mu,Q)$ has **uniform points** if for every $n$ the point $\mu(1^n;\rho)$ is exactly uniform on $\{0,1\}^n$ when $\rho$ is uniform:
--   $$\Pr_\rho[\mu(1^n;\rho)=z]=2^{-n}\qquad\text{for every } z\in\{0,1\}^n.$$
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 4.8, p.23

import Mathlib
import Definitions.Def_OWFLocalDesc_PACSampler
set_option autoImplicit false

namespace OWFLocalDesc

/-- **A sampler with uniform points.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 4.8, p.23 ("a fixed
PAC-style sampler D_ind with uniform points"): at every point length `n`, the point `µ(1ⁿ; ρ)` is
exactly uniform on `{0,1}ⁿ` for a uniform tape `ρ`. -/
def HasUniformPoints (D : PACSampler) : Prop :=
  open Classical in
  ∀ (n : ℕ) (z : Fin n → Bool),
    ((Finset.univ.filter fun ρ : Fin (D.rμ n) → Bool => D.point n ρ = z).card : ℝ) /
      (2 : ℝ) ^ (D.rμ n) = 1 / (2 : ℝ) ^ n

end OWFLocalDesc


