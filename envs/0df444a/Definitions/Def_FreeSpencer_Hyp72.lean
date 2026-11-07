-- Prove2me | Definitions.Def_FreeSpencer_Hyp72
-- name    : FreeSpencer_Hyp72
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:28.731255+00:00
-- url     : https://prove2.me/theorems/3ad95190-890b-4494-ac8f-33a985225462
-- title:
--   The facts (7.2), (7.3), and $\Psi$, $M_*$
-- statement:
--   For a mode: (7.2), that for each epoch of size $\ell$, $\Gamma|_{\mathrm{ran}\,C}\preceq t_\ell I$ implies $0\preceq J$ and $\mathrm{Tr}(CJ)\le B\sqrt\ell$; and (7.3), that $f$ is convex, $E(H,C)\ge f(H)\ge\lambda_{\max}(H)$, $E(H,\cdot)$ is order preserving, $0\le E(H,C)-f(H)\le2\sqrt\ell$ and $|E(H,C)-E(H',C)|\le\|H-H'\|_{op}$. Also the height $\Psi=E(H,C)-f(H_*)-\mathrm{Tr}(S_*(H-H_*))$ and the martingale $M_*=\mathrm{Tr}(S_*Y)$ of (7.10), where $S_*$ is the exact maximizing density of $f(H_*)$, and the condition on a saved state from which a trial may start.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (7.2), (7.3), p.51; (7.10), p.53; Algorithm 2, p.78

import Mathlib
import Definitions.Def_FreeSpencer_Procs
import Definitions.Def_FreeSpencer_trialLaw
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The curvature implication (7.2) for a mode: for each epoch `I₀` of size `ℓ ≤ n`, center `H` and
covariance `0 ⪯ C ⪯ I_ℓ` on `ℝ^{I₀}`, `Γ|_{ran C} ⪯ t_ℓ I` implies `0 ⪯ J` and `Tr(CJ) ≤ B √ℓ`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.2), p.51. -/
def Hyp72 {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) : Prop :=
  ∀ (I₀ : Finset (Fin n)) (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ),
    1 ≤ I₀.card → H.IsSymm → C.PosSemidef → (diagOn I₀ - C).PosSemidef →
    NoSpike par.q par.θ par.κ (liftFam A) H C (tEll I₀.card) →
    (∀ u, 0 ≤ halfCurv par.q par.θ par.κ (liftFam A) H C u) ∧
    TrCJ par.q par.θ par.κ (liftFam A) H C ≤ par.B * Real.sqrt I₀.card

/-- The potential facts (7.3) for a mode: `f` is convex, `E(H, C) ≥ f(H) ≥ λ_max(H)`, `E(H, ·)` is
order preserving, `0 ≤ E(H, C) - f(H) ≤ 2√ℓ`, and `E(·, C)` is `1`-Lipschitz in operator norm.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.3), p.51.

**Formalization Note** `f(H) ≥ λ_max(H)` is written `vᵀ H v ≤ f(H) ‖v‖²` for every `v`. -/
def Hyp73 {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params) : Prop :=
  ConvexOn ℝ {H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ | H.IsSymm} (fpot par) ∧
  (∀ (I₀ : Finset (Fin n)) (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (C : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → C.PosSemidef → (diagOn I₀ - C).PosSemidef →
    fpot par H ≤ Epot par A H C ∧ Epot par A H C - fpot par H ≤ 2 * Real.sqrt I₀.card) ∧
  (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ), H.IsSymm →
    ∀ v, v ⬝ᵥ (H *ᵥ v) ≤ fpot par H * (v ⬝ᵥ v)) ∧
  (∀ (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C C' : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    C'.PosSemidef → (C - C').PosSemidef → Epot par A H C' ≤ Epot par A H C) ∧
  (∀ (H H' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    H'.IsSymm → C.PosSemidef → (1 - C).PosSemidef →
    |Epot par A H C - Epot par A H' C| ≤ ‖H - H'‖)

/-- The height `Ψ = E(H, C) - f(H∗) - Tr(S∗ (H - H∗))` of a trial state above the supporting plane at
the saved point `xs`, with `S∗` the exact maximizing density of `f(H∗)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.10), p.53. -/
noncomputable def trialPsi {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params)
    (xs : Fin n → ℝ) (s : TrialState n) : ℝ :=
  Epot par A (center A s.x) s.C - fpot par (center A xs) -
    Matrix.trace (softOpt par.q par.θ par.κ (center A xs) * (center A s.x - center A xs))

/-- The supporting-plane martingale `M∗ = Tr(S∗ Y)`, with `Y = Â(y)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (7.10), p.53. -/
noncomputable def trialMart {n m : ℕ} (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (par : Params)
    (xs : Fin n → ℝ) (s : TrialState n) : ℝ :=
  Matrix.trace (softOpt par.q par.θ par.κ (center A xs) * center A s.y)

/-- A saved state from which a trial can start: `x∗` in the cube, frozen coordinates are signs, and
every live coordinate has `1 - |x∗ᵢ| > a₀`, with at least `32` of them.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Algorithm 2 (Require), p.78; Section 7.2, p.50. -/
def SavedOK {n : ℕ} (xs : Fin n → ℝ) : Prop :=
  (∀ i, |xs i| ≤ 1) ∧ (∀ i ∈ liveSet xs, marginA n < 1 - |xs i|) ∧ 32 ≤ (liveSet xs).card

end FreeSpencer


