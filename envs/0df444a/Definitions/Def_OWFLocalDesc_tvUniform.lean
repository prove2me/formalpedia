-- Prove2me | Definitions.Def_OWFLocalDesc_tvUniform
-- name    : OWFLocalDesc_tvUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:20.81593+00:00
-- url     : https://prove2.me/theorems/302e3219-2f6c-49e9-920d-1d9f55c4aecf
-- title:
--   Total variation distance $\mathrm{TV}(D_n,D_{0,n})$ (Definition 2.3)
-- statement:
--   For distributions $P,Q$ on a finite set, $\mathrm{TV}(P,Q)=\tfrac12\sum_z|P(z)-Q(z)|$. For a PAC-style sampler $D$ with $m$ points of length $n$,
--   $$\mathrm{TV}(D_n,D_{0,n})=\frac12\sum_{x\in(\{0,1\}^n)^m}\ \sum_{y\in\{0,1\}^m}\Big|D_n(x,y)-2^{-(mn+m)}\Big|,$$
--   where $D_{0,n}$ is the uniform distribution of datasets.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.3, p.11

import Mathlib
import Definitions.Def_OWFLocalDesc_datasetMass
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Total variation distance `TV(D_n, D_{0,n})` (Definition 2.3).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.3, p.11: "TV(P,Q) = ½ ∑_z |P(z) − Q(z)|", for the dataset distribution `D_n` of a
PAC-style sampler with `m` points of length `n` and the uniform dataset distribution `D_{0,n}`,
which gives every dataset `(x, y) ∈ ({0,1}ⁿ)^m × {0,1}^m` mass `2^{−(mn+m)}`. -/
noncomputable def tvUniform (D : PACSampler) (m n : ℕ) : ℝ :=
  (1 / 2) * ∑ x : Fin m → Fin n → Bool, ∑ y : Fin m → Bool,
    |datasetMass D x y - 1 / (2 : ℝ) ^ (m * n + m)|

end OWFLocalDesc


