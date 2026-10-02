-- Prove2me | Definitions.Def_TeschlODE_HigherDim_IsInvariant
-- name    : TeschlODE_HigherDim_IsInvariant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:17:44.221543+00:00
-- url     : https://prove2.me/theorems/81a5c849-455d-4280-a633-48d86c746a01
-- title:
--   Invariant set of a flow
-- statement:
--   A set $\Lambda \subseteq M$ is **invariant** under the flow $\Phi$ (with maximal intervals $I_x$) if it contains the whole orbit $\gamma(x) = \Phi(I_x, x)$ of each of its points: $\Phi(t, x) \in \Lambda$ for all $x \in \Lambda$ and all $t \in I_x$ (both positively and negatively invariant).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 193, §6.3, definition of (σ) invariant sets

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §6.3, p. 193: a set `Λ ⊆ M` is invariant if it contains the orbit
`γ(x) = Φ(I_x, x)` of each of its points: `Φ t x ∈ Λ` for every `x ∈ Λ` and `t ∈ I x`. -/
def IsInvariant {E : Type*} (M : Set E) (I : E → Set ℝ) (Φ : ℝ → E → E) (Λ : Set E) :
    Prop :=
  Λ ⊆ M ∧ ∀ x ∈ Λ, ∀ t ∈ I x, Φ t x ∈ Λ

end TeschlODE.HigherDim


