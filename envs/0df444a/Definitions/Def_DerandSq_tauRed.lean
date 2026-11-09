-- Prove2me | Definitions.Def_DerandSq_tauRed
-- name    : DerandSq_tauRed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:34.990048+00:00
-- url     : https://prove2.me/theorems/35c4d395-dafe-43a0-a587-2364f35a2cb9
-- title:
--   Canonical trace $\tau(a) = \langle a\delta_e, \delta_e\rangle$
-- statement:
--   The **canonical trace** of the reduced C*-algebra of a group $\Gamma$ is
--   $$
--   \tau(a) = \langle a\,\delta_e, \delta_e \rangle = (a\,\delta_e)(e)
--   $$
--   for a bounded operator $a$ on $\ell^2(\Gamma)$, where $e$ is the identity of $\Gamma$. On $C^*_{\mathrm{red}}(\Gamma)$ it is a faithful tracial state; $\tau(\lambda(g)) = \mathbf 1[g = e]$.
--
--   **Formalization Note** Mathlib's inner product is linear in the second slot, so $\langle a\delta_e, \delta_e\rangle$ is written $\langle\delta_e, a\delta_e\rangle$; both equal $(a\delta_e)(e)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Example 2.4, p.8

import Mathlib
import Definitions.Def_DerandSq_delta

namespace DerandSq

open scoped InnerProductSpace in
/-- The canonical trace `τ(a) = ⟨a δ_e, δ_e⟩` of the reduced C*-algebra `C*_red(Γ)` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0),
Example 2.4, p.8), for a bounded operator `a` on `ℓ²(Γ)`.

**Formalization Note** The paper's inner product is linear in its first slot; Mathlib's is linear
in its second, so `⟨a δ_e, δ_e⟩` is written `⟪δ_e, a δ_e⟫`; both equal `(a δ_e)(e)`. -/
noncomputable def tauRed {Γ : Type*} [Group Γ] (a : L2 Γ →L[ℂ] L2 Γ) : ℂ :=
  ⟪delta (1 : Γ), a (delta 1)⟫_ℂ

end DerandSq


