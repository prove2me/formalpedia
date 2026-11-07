-- Prove2me | Definitions.Def_StableVotingDistortion_offset
-- name    : StableVotingDistortion_offset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:42.279712+00:00
-- url     : https://prove2.me/theorems/0436ea82-eefe-4aa7-a2c4-7a54abf7ba09
-- title:
--   The offset slice (32) and the averaged potential (35): $A$, $\bar c$, $\tilde q_v$, $W$
-- statement:
--   With $s_v$ as above,
--   $$A=\mathbb E_v[\mathbf 1_{\{s_v<\lambda\}}\phi(s_v)],\qquad \bar c(p)=\frac{\mathbb E_v[\mathbf 1_{\{s_v<\lambda\}}c(p,s_v)]}{A},\qquad W(z)=\frac{\mathbb E_v[\mathbf 1_{\{s_v<\lambda\}}\phi(s_v)W_{s_v}(z)]}{A},$$
--   and
--   $$\tilde q_v(t)=q_v(t)+\beta(p_t)k_v(t)+\begin{cases}c(p_t,s_v),&s_v<\lambda,\\ \phi(s_v)\bar c(p_t),&s_v\ge\lambda.\end{cases}$$
--
--   **Formalization Note** $\bar c$ and $W$ divide by $A$. The paper uses them only under $A>0$, and so do the mission's statements.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (32), (35), p.29

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_voterMean
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- `A = E_v[1{s_v < λ} ϕ(s_v)]`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, p.29. -/
noncomputable def Aval {V C : Type} [Fintype V] [Fintype C] (lam : ℝ) (ϕ : ℝ → ℝ) (E : Election V C)
    (D : C → ℝ) (aStar : C) : ℝ :=
  voterMean (fun v => if sv E D aStar v < lam then ϕ (sv E D aStar v) else 0)

/-- `c̄(p) = E_v[1{s_v < λ} c(p, s_v)] / A`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (32), p.29.

**Formalization Note.** The paper uses this only under `A > 0`, and so does every statement here. -/
noncomputable def cbar {V C : Type} [Fintype V] [Fintype C] (lam : ℝ) (ϕ : ℝ → ℝ) (c : ℝ → ℝ → ℝ)
    (E : Election V C) (D : C → ℝ) (aStar : C) (p : ℝ) : ℝ :=
  voterMean (fun v => if sv E D aStar v < lam then c p (sv E D aStar v) else 0) / Aval lam ϕ E D aStar

/-- The offset slice
`q̃_v(t) = q_v(t) + β(p_t) k_v(t) + c(p_t, s_v)` if `s_v < λ`, and
`q̃_v(t) = q_v(t) + β(p_t) k_v(t) + ϕ(s_v) c̄(p_t)` if `s_v ≥ λ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (32), p.29. -/
noncomputable def qTilde {V C : Type} [Fintype V] [Fintype C] (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ)
    (E : Election V C) (D ρ : C → ℝ) (aStar : C) (v : V) (t : ℝ) : ℝ :=
  qv E D ρ v t + β (pt D ρ t) * kv E D ρ ϕ v t +
    if sv E D aStar v < lam then c (pt D ρ t) (sv E D aStar v)
    else ϕ (sv E D aStar v) * cbar lam ϕ c E D aStar (pt D ρ t)

/-- The potential `W(z) = E_v[1{s_v < λ} ϕ(s_v) W_{s_v}(z)] / A`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Equation (35), p.29.

**Formalization Note.** The paper uses this only under `A > 0`, and so does every statement here. -/
noncomputable def WAvg {V C : Type} [Fintype V] [Fintype C] (lam : ℝ) (ϕ : ℝ → ℝ) (E : Election V C)
    (D : C → ℝ) (aStar : C) (z : ℝ) : ℝ :=
  voterMean (fun v =>
      if sv E D aStar v < lam then ϕ (sv E D aStar v) * Wx lam ϕ (sv E D aStar v) z else 0) /
    Aval lam ϕ E D aStar

end StableVotingDistortion


