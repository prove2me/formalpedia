-- Prove2me | Definitions.Def_OWFLocalDesc_datasetMass
-- name    : OWFLocalDesc_datasetMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:58.639894+00:00
-- url     : https://prove2.me/theorems/a07b2162-bbaf-49ca-889d-87b1e11c0932
-- title:
--   Dataset mass under $D_n$
-- statement:
--   The **joint mass** of a dataset $(x,y)$ under a PAC-style sampler $D$ at point length $n$ is
--   $$D_n(x,y)=\mu^m(x)\,D(y\mid x).$$
--   The product form expresses the independence of the points from the concept. A dataset is **supported** when $D_n(x,y)>0$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.6 and p.14

import Mathlib
import Definitions.Def_OWFLocalDesc_condProb
import Definitions.Def_OWFLocalDesc_pointProb
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Dataset mass under `D_n`.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), p.14: "The joint mass of (x,y)
is the product µ^m(x)D(y|x) … Write D_n for the resulting distribution of datasets at point length
n … A dataset is supported when it has positive probability under D_n". -/
noncomputable def datasetMass (D : PACSampler) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) : ℝ :=
  pointProb D x * condProb D x y

end OWFLocalDesc


