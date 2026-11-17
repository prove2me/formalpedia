-- Prove2me | Definitions.Def_FreeSpencer_Supplement_occForm
-- name    : FreeSpencer_Supplement_occForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:32:18.643103+00:00
-- url     : https://prove2.me/theorems/ca7e8bfd-1b62-488e-8b2d-3b2d31c0463d
-- title:
--   Occupancy form, soft maximum and value form for a general regularizer $\mathfrak r$
-- statement:
--   Let $\mathcal D_D=\{S\succeq0:\operatorname{Tr}S=1\}$ be the set of real $D\times D$ densities, let $\widehat A_1,\dots,\widehat A_\ell$ be real symmetric $D\times D$ matrices, $C$ a real $\ell\times\ell$ matrix, and $\eta_C(X)=\sum_{i,j}C_{ij}\widehat A_iX\widehat A_j$ the covariance map. Write $F(S,M)=\operatorname{Tr}\sqrt{S^{1/2}MS^{1/2}}$ for the (unsquared) fidelity. For a regularizer $\mathfrak r$ on matrices, define
--
--   1. the **soft maximum** $f_{\mathfrak r}(Y)=\max_{S\in\mathcal D_D}\{\operatorname{Tr}(YS)+\mathfrak r(S)\}$;
--   2. the **occupancy form**
--   $$E_{\mathfrak r}(H,C)=\max_{S\in\mathcal D_D}\big\{\operatorname{Tr}(HS)+2F(S,\eta_C(S))+\mathfrak r(S)\big\};$$
--   3. the **value form** $\inf_{Z\succ0} f_{\mathfrak r}\big(H+Z^{-1}+\eta_C(Z)\big)$, an infimum over positive definite real $Z$, together with the set of values it is the infimum of.
--
--   These are the objects of (4.11)–(4.12) with the regularizer left free; the Tsallis potentials of the paper are the special case $\mathfrak r(S)=\tfrac{\theta}{1-q}\operatorname{Tr}S^{1-q}+2\kappa\operatorname{Tr}\sqrt S$.
--
--   **Formalization Note** Maxima and the infimum are written as `sSup` and `sInf` of images (attainment is not asserted); only the values of $\mathfrak r$ on densities enter. $Z^{-1}$ is the matrix inverse, used only at positive definite $Z$.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (4.11)–(4.12), p.29

import Mathlib
import Definitions.Def_FreeSpencer_fidelity
import Definitions.Def_FreeSpencer_covMap
import Definitions.Def_FreeSpencer_IsDensity

namespace FreeSpencer.Supplement

open FreeSpencer

/-- The soft maximum of a general regularizer `𝔯`: `f_𝔯(Y) = max_{S ∈ 𝒟_D} {Tr(YS) + 𝔯(S)}`, the
first formula of (4.11). Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix
Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (4.11), p.29.

**Formalization Note** The maximum is written as `sSup` of the image of the density set; attainment is
not asserted. Only the values of `𝔯` on densities enter. -/
noncomputable def softMaxR {ι : Type*} [Fintype ι] (r : Matrix ι ι ℝ → ℝ) (Y : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun S : Matrix ι ι ℝ => Matrix.trace (Y * S) + r S) '' {S | IsDensity S})

/-- The objective of the occupancy form with a general regularizer `𝔯`:
`Tr(HS) + 2F(S, η_C(S)) + 𝔯(S)`. Source: eq. (4.11), p.29. -/
noncomputable def occObj {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (r : Matrix ι ι ℝ → ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (S : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (H * S) + 2 * fidelity S (covMap Ah C S) + r S

/-- The occupancy form `E_𝔯(H, C) = max_{S ∈ 𝒟_D} {Tr(HS) + 2F(S, η_C(S)) + 𝔯(S)}` of (4.11), for a
general regularizer `𝔯`. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix
Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (4.11), p.29.

**Formalization Note** `sSup` of the image of the density set, as the published `FreeSpencer.pot`, which
is the special case `𝔯 = regVal q θ κ`. -/
noncomputable def occForm {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (r : Matrix ι ι ℝ → ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : ℝ :=
  sSup (occObj r Ah H C '' {S | IsDensity S})

/-- The set of values `f_𝔯(H + Z⁻¹ + η_C(Z))` over positive definite real `Z`, whose infimum is the
value form (4.12). Source: eq. (4.12), p.29. -/
def valueSet {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (r : Matrix ι ι ℝ → ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : Set ℝ :=
  (fun Z : Matrix ι ι ℝ => softMaxR r (H + Z⁻¹ + covMap Ah C Z)) '' {Z | Z.PosDef}

/-- The value form `inf_{Z ≻ 0} f_𝔯(H + Z⁻¹ + η_C(Z))` of (4.12). Source: Kathuria, A Walk From Free
Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…),
eq. (4.12), p.29.

**Formalization Note** `Z⁻¹` is the matrix inverse (`Matrix.inv`), applied only at positive definite `Z`.
The infimum is `sInf` of `valueSet`, not a minimum. -/
noncomputable def valueForm {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (r : Matrix ι ι ℝ → ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : ℝ :=
  sInf (valueSet r Ah H C)

end FreeSpencer.Supplement


