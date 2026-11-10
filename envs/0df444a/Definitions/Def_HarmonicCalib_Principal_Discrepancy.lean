-- Prove2me | Definitions.Def_HarmonicCalib_Principal_Discrepancy
-- name    : HarmonicCalib_Principal_Discrepancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:47.974091+00:00
-- url     : https://prove2.me/theorems/391d7c7d-f1fa-4800-9dae-6947ccea8a61
-- title:
--   The matrix discrepancy $\Gamma^{(T)}_{A,B}(H)$ and the geometric coefficient $\gamma(Y,L)$
-- statement:
--   For sets $A, B \subseteq \mathbb R^d$ and a real $T \times T$ matrix $H$,
--   $$\Gamma^{(T)}_{A,B}(H) = \sup_{a_0,\dots,a_{T-1} \in A,\; b_0,\dots,b_{T-1} \in B} \ \sum_{t,s=0}^{T-1} H_{ts} \langle a_t, b_s\rangle,$$
--   and for a forecast set $Y$ and a norm unit ball $L$,
--   $$\gamma(Y, L) = \sup_{T \ge 1} \frac{\Gamma^{(T)}_{\tilde Y, L^\circ}(K_T)}{T},$$
--   with $\tilde Y = Y - c_Y$ the centered forecast set and $L^\circ$ the polar of $L$. Both suprema are taken in the extended reals $[-\infty, +\infty]$, so an unbounded supremum is $+\infty$ (never a junk finite value). On nonempty compact $A, B$ the supremum $\Gamma$ is a finite maximum.
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), (1) p. 4 and (3) p. 5

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Geometry
import Definitions.Def_HarmonicCalib_Principal_Hilbert

open scoped InnerProductSpace

namespace HarmonicCalib.Principal

/-! # The matrix discrepancy `Γ` and the geometric coefficient `γ`
(Fishelson–Mohri 2026, (1) p. 4 and (3) p. 5)

Both are suprema, valued in `EReal` so that an empty or unbounded supremum is `⊥`/`⊤`, never a
junk real value. -/

/-- `Γ^{(T)}_{A,B}(H) = sup_{a_0,…,a_{T-1} ∈ A, b_0,…,b_{T-1} ∈ B} ∑_{t,s<T} H_{ts} ⟨a_t, b_s⟩`
((1), p. 4). -/
noncomputable def Gamma {d : ℕ} (A B : Set (EuclideanSpace ℝ (Fin d))) (T : ℕ)
    (H : Matrix (Fin T) (Fin T) ℝ) : EReal :=
  ⨆ (a : Fin T → EuclideanSpace ℝ (Fin d)) (_ : ∀ t, a t ∈ A)
    (b : Fin T → EuclideanSpace ℝ (Fin d)) (_ : ∀ s, b s ∈ B),
    ((∑ t, ∑ s, H t s * ⟪a t, b s⟫_ℝ : ℝ) : EReal)

/-- The geometric coefficient `γ(Y, L) = sup_{T ≥ 1} Γ^{(T)}_{Ỹ, L°}(K_T) / T` ((3), p. 5), with
`Ỹ = Y - c_Y` and `L°` the polar of `L`. -/
noncomputable def gammaCoef {d : ℕ} (Y L : Set (EuclideanSpace ℝ (Fin d))) : EReal :=
  ⨆ (T : ℕ) (_ : 1 ≤ T), Gamma (centered Y) (polar L) T (hilbertK T) / (T : EReal)

end HarmonicCalib.Principal


