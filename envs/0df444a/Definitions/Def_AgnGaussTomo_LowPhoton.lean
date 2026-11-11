-- Prove2me | Definitions.Def_AgnGaussTomo_LowPhoton
-- name    : AgnGaussTomo_LowPhoton
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:51.438215+00:00
-- url     : https://prove2.me/theorems/1862b1ce-0cd4-4dcb-8a30-4b010b298ef6
-- title:
--   Low-photon subspace $\mathcal F_{\le M}=\Pi_{\le M}\mathcal F$
-- statement:
--   A Fock vector $\varphi=\sum_m\varphi_m|m\rangle$ lies in $\mathcal F_{\le M}$, the range of the projector $\Pi_{\le M}$ onto total photon number at most $M$, if $\varphi_m=0$ whenever $|m|=\sum_im_i>M$. Such vectors have finitely many non-zero coefficients.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.10, printed p. 19 (PDF p. 22)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **The subspace `F_{≤M} = Π_{≤M} F` of total photon number at most `M`.** Arulandu, Chen, Chen, Li,
Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma
3.10, printed p. 19 (PDF p. 22): "Let Π_{≤m} be the projector onto states with total photon number at
most m. For |φ⟩ ∈ F_{≤m} ≡ Π_{≤m} F …".

`LowPhoton M φ` says the Fock coefficients `φ_m` vanish whenever `|m| = Σᵢ mᵢ > M`.

**Formalization Note.** Such `φ` are finitely supported (finitely many occupations of total
photon number at most `M`), hence automatically in `ℓ²`. -/
def LowPhoton {n : ℕ} (M : ℕ) (φ : Occupation (Fin n) → ℂ) : Prop :=
  ∀ m : Occupation (Fin n), M < ∑ i, m i → φ m = 0

end AgnGaussTomo


