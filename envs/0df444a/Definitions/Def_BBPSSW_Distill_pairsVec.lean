-- Prove2me | Definitions.Def_BBPSSW_Distill_pairsVec
-- name    : BBPSSW_Distill_pairsVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:22.469299+00:00
-- url     : https://prove2.me/theorems/50c3a7b8-2d3c-4d27-998a-72baedf3fc70
-- title:
--   Product vector $v_0\otimes\cdots\otimes v_{k-1}$ of $k$ shared pairs
-- statement:
--   Given two-spin vectors $v_0,\dots,v_{k-1}$, their tensor product as a bipartite vector between Alice (first spin of each pair) and Bob (second spin):
--
--   $$\Big(\bigotimes_j v_j\Big)_{(a,b)}=\prod_j (v_j)_{(a_j,b_j)},\qquad a,b\in\{0,1\}^k .$$
--
--   For example $(\Psi^-)^{\otimes m}$, $m$ perfect singlets, is `pairsVec (fun _ => bellVec .psiMinus)`.
--
--   **Formalization Note** Same register encoding as `pairsState`.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 1 ("a smaller number of entangled pairs of arbitrarily high purity")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **The product vector `v₀ ⊗ ⋯ ⊗ v_{k−1}` of `k` shared pairs, as a bipartite vector.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 1 ("a smaller number of entangled pairs of arbitrarily high purity (e.g.
near-perfect singlets)").

Same encoding as `pairsState`: `(a, b) ↦ ∏ j, v j (a_j, b_j)`, where `a_j` (resp. `b_j`) is
bit `j` of Alice's (resp. Bob's) register under `finFunctionFinEquiv`; Alice's spin `j` and
Bob's spin `j` form pair `j`. -/
noncomputable def pairsVec {k : ℕ} (v : Fin k → EuclideanSpace ℂ QQ) :
    EuclideanSpace ℂ (Fin (2 ^ k) × Fin (2 ^ k)) :=
  WithLp.toLp 2 fun x => ∏ j, v j ((finFunctionFinEquiv.symm x.1) j, (finFunctionFinEquiv.symm x.2) j)

end BBPSSW.Distill


