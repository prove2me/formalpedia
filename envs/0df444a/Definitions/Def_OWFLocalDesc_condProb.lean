-- Prove2me | Definitions.Def_OWFLocalDesc_condProb
-- name    : OWFLocalDesc_condProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:29.089885+00:00
-- url     : https://prove2.me/theorems/7004a627-5f6b-4bd6-8995-31c8e2e2a18c
-- title:
--   Conditional label probability $D(y\mid x)$ (Definition 2.6)
-- statement:
--   For a PAC-style sampler $D$ and a dataset $(x,y)$ with $m$ points of length $n$,
--   $$D(y\mid x)=2^{-q(n)}\,\big|\{r\in\{0,1\}^{q(n)} : c_r(x_i)=y_i \text{ for all } i\}\big| .$$
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.6, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_PACSampler
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Conditional label probability `D(y|x)` (Definition 2.6).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.6, p.13: "D(y|x) = 2^{−q(n)} |{r : c_r(x_i) = y_i for all i}|". -/
noncomputable def condProb (D : PACSampler) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun r : Fin (D.q n) → Bool => ∀ i, D.concept n r (x i) = y i).card : ℝ) /
    (2 : ℝ) ^ (D.q n)

end OWFLocalDesc


