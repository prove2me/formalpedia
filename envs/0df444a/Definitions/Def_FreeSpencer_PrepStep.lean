-- Prove2me | Definitions.Def_FreeSpencer_PrepStep
-- name    : FreeSpencer_PrepStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:26.174028+00:00
-- url     : https://prove2.me/theorems/1af17001-f2e2-4a8f-96ac-50d4aa6f7762
-- title:
--   Runs of Prepare
-- statement:
--   The steps of Prepare, in the form of Appendix F, which covers the eigendecomposition form as well. A cleanup step takes a nonzero $u\in\mathrm{ran}\,C$ with $u^TCu<2\delta\|u\|^2$ and a solution $z$ of $Cz=u$, and replaces $C$ by $C-uu^T/(u^Tz)$. A cut needs the floor $2\delta$ on $\mathrm{ran}\,C$ and an estimate $\hat\Gamma$ with $\|\hat\Gamma-\Gamma\|_{op,\mathrm{ran}\,C}\le t_\ell/64$, finds a unit $v\in\mathrm{ran}\,C$ with $v^T\hat\Gamma v>15t_\ell/16$, and replaces $C$ by $C-\alpha_\ell vv^T$. Prepare returns when the floor holds and an estimate shows no spike. The covariance history of an entire epoch records the number of cuts and the total cleanup loss, with movements $C-h^2Q$, $0\preceq Q\preceq C$, between them.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Prepare, p.78; Lemma F.2, p.88; Appendix F.2–F.3, p.89; Lemma C.1, p.79

import Mathlib
import Definitions.Def_FreeSpencer_Procs
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- A cleanup step of Prepare, in the form of Lemma F.2 and App. F.2: a nonzero `u ∈ ran C` with
`uᵀ C u < 2δ ‖u‖²`, a solution `z` of `C z = u`, and `C' = C - u uᵀ/(uᵀ z)`. Discarding one eigenvector
of eigenvalue below `2δ` is the case `u` an eigenvector.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma F.2, p.88; Appendix F.2, p.89; Prepare, p.78. -/
def CleanupStep {n : ℕ} (C C' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ u z : Fin n → ℝ, u ≠ 0 ∧ C *ᵥ z = u ∧ u ⬝ᵥ (C *ᵥ u) < 2 * deltaC * (u ⬝ᵥ u) ∧
    C' = C - (u ⬝ᵥ z)⁻¹ • Matrix.vecMulVec u u

/-- An estimate `Ĝ` of the covariance derivative with `‖Ĝ - Γ‖_{op, ran C} ≤ t_ℓ/64`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma C.1, p.79; Corollary A.4; Appendix F.3, p.89. -/
def GammaEst {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) (ℓ : ℕ)
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C G : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u, InRan C u →
    |u ⬝ᵥ (G *ᵥ u) - covForm par.q par.θ par.κ (liftFam A) H C u u| ≤ tEll ℓ / 64 * (u ⬝ᵥ u)

/-- A cut of Prepare at center `H`: after cleanup, the spike test on some estimate `Ĝ` finds a unit
`v ∈ ran C` with `vᵀ Ĝ v > 15 t_ℓ/16`, and `C' = C - α_ℓ v vᵀ`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Prepare, p.78; Appendix F.2, p.89. -/
def CutStep {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) (ℓ : ℕ)
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C C' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  CovFloor C ∧ ∃ G v, GammaEst A par ℓ H C G ∧ InRan C v ∧ v ⬝ᵥ v = 1 ∧
    15 * tEll ℓ / 16 < v ⬝ᵥ (G *ᵥ v) ∧ C' = C - alphaEll n m ℓ • Matrix.vecMulVec v v

/-- One step of Prepare at center `H`, a cleanup or a cut. -/
def PrepStep {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) (ℓ : ℕ)
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C C' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  CleanupStep C C' ∨ CutStep A par ℓ H C C'

/-- Prepare returns `C`: cleanup has finished and the spike test on some estimate finds no spike
(this includes the empty range `C = 0`). Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Prepare, p.78; Appendix F.2, p.89. -/
def PrepDone {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) (ℓ : ℕ)
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  CovFloor C ∧ ∃ G, GammaEst A par ℓ H C G ∧ ∀ u, InRan C u → u ⬝ᵥ (G *ᵥ u) ≤ 15 * tEll ℓ / 16 * (u ⬝ᵥ u)

/-- The covariance history of an entire epoch trial on the coordinates `I₀`, recording the number of
cuts and the total cleanup loss: it starts from the identity on `I₀`, and each later covariance is a
cleanup, a cut at a center `H` in the walk's range, or a movement `C - h² Q` with `0 ⪯ Q ⪯ C`, `h² ≤ 1/2`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma C.2 and its proof, pp.79–80; Lemma 7.5's proof, p.53. -/
inductive EpochRun {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params)
    (ℓ : ℕ) (I₀ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ → ℕ → ℝ → Prop
  | start : EpochRun A par ℓ I₀ I₀ 0 0
  | cleanup {C C' k u} : EpochRun A par ℓ I₀ C k u → CleanupStep C C' →
      EpochRun A par ℓ I₀ C' k (u + Matrix.trace (C - C'))
  | cut {C C' k u H} : EpochRun A par ℓ I₀ C k u → H.IsSymm → ‖H‖ ≤ (n : ℝ) + 1 →
      CutStep A par ℓ H C C' → EpochRun A par ℓ I₀ C' (k + 1) u
  | move {C Q k u} {h : ℝ} : EpochRun A par ℓ I₀ C k u → Q.PosSemidef → (C - Q).PosSemidef →
      0 < h → h ^ 2 ≤ 1 / 2 → EpochRun A par ℓ I₀ (C - h ^ 2 • Q) k u

end FreeSpencer


