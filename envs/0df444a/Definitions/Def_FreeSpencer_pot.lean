-- Prove2me | Definitions.Def_FreeSpencer_pot
-- name    : FreeSpencer_pot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:29.144189+00:00
-- url     : https://prove2.me/theorems/524b01a0-6fea-4c10-86bc-8e7bfcea5b1d
-- title:
--   The potential $E(H,C)$, the soft maximum $f(H)$, their maximizers
-- statement:
--   For $0<q\le1/2$, $\theta>0$, $\kappa\ge0$, the Tsallis-regularized Lehner-style potential is
--   $$E(H,C)=\max_{S\succeq0,\ \mathrm{Tr}\,S=1}\Bigl\{\mathrm{Tr}(HS)+2F(S,\eta_C(S))+\frac{\theta}{1-q}\mathrm{Tr}\,S^{1-q}+2\kappa\mathrm{Tr}\sqrt S\Bigr\},$$
--   and $f(H)$ is the same maximum without the fidelity term, which is $E(H,0)$. The square potential is $(q,\kappa)=(1/2,0)$, since $\frac{\theta}{1/2}\mathrm{Tr}\sqrt S=2\theta\mathrm{Tr}\sqrt S$. The maximizing density $S(H,C)$ is the unique maximizer (Lemma 4.4).
--
--   **Formalization Note** The maximum is written as a supremum; attainment and uniqueness are part of `lemma_5_1`. The maximizing density is a choice from the maximizers, which `lemma_5_1` and `theorem_D_1` show to be a single matrix.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (2.3), (2.4), (2.6), p.19; (10.1), p.63

import Mathlib
import Definitions.Def_MatrixLewis_mpow
import Definitions.Def_FreeSpencer_fidelity
import Definitions.Def_FreeSpencer_covMap
import Definitions.Def_FreeSpencer_IsDensity

namespace FreeSpencer

/-- The regularizer of (2.6): `θ/(1-q) · Tr S^{1-q} + 2κ · Tr √S`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (2.6), p.19. -/
noncomputable def regVal {ι : Type*} [Fintype ι] [DecidableEq ι] (q θ κ : ℝ) (S : Matrix ι ι ℝ) : ℝ :=
  θ / (1 - q) * Matrix.trace (MatrixLewis.mpow (1 - q) S) + 2 * κ * Matrix.trace (MatrixLewis.mpow (1 / 2) S)

/-- The objective of (2.6). -/
noncomputable def potObj {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (S : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (H * S) + 2 * fidelity S (covMap Ah C S) + regVal q θ κ S

/-- The Tsallis-regularized potential `E(H, C)` of (2.6), the supremum of the objective over
densities. The square potential (2.4) is `(q, θ, κ) = (1/2, θ, 0)`, since `θ/(1/2) · Tr √S = 2θ Tr √S`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eqs. (2.4), (2.6), p.19; (10.1), p.63.

**Formalization Note** The source writes a maximum. Attainment is Lemma 4.4 and is proved inside
`lemma_5_1`, never assumed. The objective is continuous on the compact set of densities when `C ⪰ 0`
and `Nonempty ι`, so this `sSup` is over a nonempty bounded set. -/
noncomputable def pot {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : ℝ :=
  sSup (potObj q θ κ Ah H C '' {S | IsDensity S})

/-- The soft maximum `f(H) = max_S {Tr(HS) + regularizer}`, that is, `E(H, 0)`.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), eq. (2.3), p.19; p.57 and p.63. -/
noncomputable def softMax {ι : Type*} [Fintype ι] [DecidableEq ι] (q θ κ : ℝ) (H : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun S : Matrix ι ι ℝ => Matrix.trace (H * S) + regVal q θ κ S) '' {S | IsDensity S})

/-- `S` attains the maximum in (2.6). -/
def IsMaximizer {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ)
    (S : Matrix ι ι ℝ) : Prop :=
  IsDensity S ∧ ∀ S', IsDensity S' → potObj q θ κ Ah H C S' ≤ potObj q θ κ Ah H C S

/-- The maximizing density `S(H, C)`: the unique maximizer, by Lemma 4.4. -/
noncomputable def optDensity {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} (q θ κ : ℝ)
    (Ah : Fin ℓ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (C : Matrix (Fin ℓ) (Fin ℓ) ℝ) : Matrix ι ι ℝ :=
  Classical.epsilon (IsMaximizer q θ κ Ah H C)

/-- The maximizing density of the soft maximum `f(H)`. Source: p.53 (`S∗`). -/
noncomputable def softOpt {ι : Type*} [Fintype ι] [DecidableEq ι] (q θ κ : ℝ) (H : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Classical.epsilon fun S : Matrix ι ι ℝ => IsDensity S ∧ ∀ S', IsDensity S' →
    Matrix.trace (H * S') + regVal q θ κ S' ≤ Matrix.trace (H * S) + regVal q θ κ S

end FreeSpencer


