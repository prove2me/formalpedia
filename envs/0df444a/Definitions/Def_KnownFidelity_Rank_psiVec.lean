-- Prove2me | Definitions.Def_KnownFidelity_Rank_psiVec
-- name    : KnownFidelity_Rank_psiVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:10.740848+00:00
-- url     : https://prove2.me/theorems/344ab8e4-9e68-4d0a-aa7b-8f8b1097fba9
-- title:
--   The unit vector $|\psi_G\rangle=\mathrm{vec}(G)/\|G\|_F$, Eq. (42)
-- statement:
--   For $G\ne0$ in $\mathbb C^{r\times r}$,
--
--   $$|\psi_G\rangle=\frac{\mathrm{vec}(G)}{\|G\|_F}\in\mathbb C^r\otimes\mathbb C^r .$$
--
--   **Formalization Note** At $G=0$, where it is undefined on the page, the value is the zero vector; $G=0$ has probability zero under every size-biased prior with $m\ge1$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.4, Eq. (42), p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_vecOf
import Definitions.Def_KnownFidelity_Rank_frobSq

namespace KnownFidelity.Rank

/-- **The unit vector `|ψ_G⟩ = vec(G)/‖G‖_F`, Eq. (42).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.4, Eq. (42), printed p. 17 (PDF p. 19): "For G ≠ 0, put
|ψ_G⟩ = vec(G)/∥G∥_F ∈ C^r ⊗ C^r."

**Formalization Note.** `vec` is `vecOf` (Eq. (7), system index first). At `G = 0`, where the page
leaves `ψ_G` undefined, the value is the zero vector (`0⁻¹ = 0`); `G = 0` has probability zero
under every size-biased prior with `m ≥ 1`, since its density vanishes there. -/
noncomputable def psiVec {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) : Fin r × Fin r → ℂ :=
  fun p => (((Real.sqrt (frobSq G))⁻¹ : ℝ) : ℂ) * vecOf G p

end KnownFidelity.Rank


