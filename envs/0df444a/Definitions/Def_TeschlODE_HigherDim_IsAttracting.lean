-- Prove2me | Definitions.Def_TeschlODE_HigherDim_IsAttracting
-- name    : TeschlODE_HigherDim_IsAttracting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:20:54.17533+00:00
-- url     : https://prove2.me/theorems/67a5b505-4ad6-42a4-bf31-74bd9592241e
-- title:
--   Attracting set — $W^+(\Lambda)$ is a neighborhood of the invariant set $\Lambda$
-- statement:
--   An invariant set $\Lambda$ is called **attracting** if its stable set $W^+(\Lambda)$ (8.8) is a neighborhood of $\Lambda$, that is, $W^+(\Lambda)$ contains an open set containing $\Lambda$. In this case $W^+(\Lambda)$ is the **basin of attraction** of $\Lambda$.
--
--   **Formalization Note.** "Neighborhood of a set" is Mathlib's `nhdsSet`: $W^+(\Lambda) \in \mathcal{N}(\Lambda)$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 231, §8.1, definition of an attracting set

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsInvariant

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 231: an invariant set `Λ` is attracting if its stable set `W⁺(Λ)` (8.8)
is a neighborhood of `Λ` (`W⁺(Λ) ∈ 𝓝ˢ Λ`, i.e. contains an open set containing `Λ`). -/
def IsAttracting {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (Λ : Set E) : Prop :=
  IsInvariant M I Φ Λ ∧ stableSet M I Φ 1 Λ ∈ nhdsSet Λ

end TeschlODE.HigherDim


