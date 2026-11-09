-- Prove2me | Definitions.Def_DerandSq_QH
-- name    : DerandSq_QH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:03:52.519226+00:00
-- url     : https://prove2.me/theorems/eb2ae54c-9435-41e1-ac3d-12b69e8cd9d4
-- title:
--   $s = Q_H(u)$, the adjacency operator of $T_d \circledS H$
-- statement:
--   Let $H$ be a graph on $[d]$ and $u_i = \lambda(m_i)$, $i \in [d]$, the left-regular representations of the generators of $\Gamma_d$ on $\ell^2(\Gamma_d)$. Then
--   $$
--   s = Q_H(u) = \sum_{\{i, j\} \in E(H)} \bigl( u_i u_j + u_j^* u_i^* \bigr),
--   $$
--   a self-adjoint element of $C^*_{\mathrm{red}}(\Gamma_d)$ (since $u_i^* = u_i$). It is the limit object of the derandomized square: by Lemma 4.3 the adjacency matrix of $G \circledS H$ is $Q_H$ evaluated at the permutation matrices of $G$, and $Q_H(u)$ is the adjacency operator of $T_d \circledS H$.
--
--   **Formalization Note** Each unordered edge is summed once, as the pair $i < j$. The norm $\|Q_H(u)\|_{C^*_{\mathrm{red}}(\Gamma_d)}$ is the operator norm on $\ell^2(\Gamma_d)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (4.10), p.21

import Mathlib
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_leftReg

namespace DerandSq

/-- `s = Q_H(u) = ∑_{{i,j} ∈ E(H)} (u_i u_j + u_j* u_i*)` with `u_i = λ(m_i)` on `ℓ²(Γ_d)`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), (4.10), p.21), the adjacency operator of `T_d Ⓢ H`.

**Formalization Note** Each unordered edge `{i, j}` is summed once, as the ordered pair with
`i < j`. The operator lives in `B(ℓ²(Γ_d))`; its operator norm is the norm of `C*_red(Γ_d)`. -/
noncomputable def QH {d : ℕ} (H : SimpleGraph (Fin d)) : L2 (Gam d) →L[ℂ] L2 (Gam d) := by
  classical exact ∑ i : Fin d, ∑ j : Fin d,
    if i < j ∧ H.Adj i j then
      leftReg (mGen i) * leftReg (mGen j) + star (leftReg (mGen j)) * star (leftReg (mGen i))
    else 0

end DerandSq


