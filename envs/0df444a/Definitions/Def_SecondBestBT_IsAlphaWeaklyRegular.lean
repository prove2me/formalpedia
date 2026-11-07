-- Prove2me | Definitions.Def_SecondBestBT_IsAlphaWeaklyRegular
-- name    : SecondBestBT_IsAlphaWeaklyRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:34.591192+00:00
-- url     : https://prove2.me/theorems/752cd083-45ce-420f-9840-ca31a1287445
-- title:
--   $\alpha$-weak regularity of the seller prior
-- statement:
--   A seller prior with full support on $\{0,\dots,K\}$ is **$\alpha$-weakly regular** if its $\alpha$-virtual value $\varphi^\alpha_S(s)$ is weakly increasing in $s\in\{0,\dots,K\}$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 4.1, p.9

import Mathlib
import Definitions.Def_SecondBestBT_alphaVirtualS

namespace SecondBestBT

/-- `F_S` is `α`-weakly regular when its `α`-virtual value `φ^α_S(s)` is weakly increasing in `s`
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Definition 4.1, p.9).

**Formalization Note** For a seller with full support on `{0, …, K}` the positive-mass points are
`{0, …, K}`, so monotonicity is required on `Set.Iic K`. -/
def IsAlphaWeaklyRegular (α : ℝ) (fS : ℕ → ℝ) (K : ℕ) : Prop :=
  MonotoneOn (alphaVirtualS α fS) (Set.Iic K)

end SecondBestBT


