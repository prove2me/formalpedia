-- Prove2me | Definitions.Def_LiftSAParity_IsStiflingInputs
-- name    : LiftSAParity_IsStiflingInputs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:31.033737+00:00
-- url     : https://prove2.me/theorems/9079a12f-db5f-453b-be3c-9bed90abf77e
-- title:
--   Stifling inputs $\gamma_{j,b}$ of a gadget
-- statement:
--   Let $g:\{0,1\}^\ell\to\{0,1\}$ be a gadget. A family of **stifling inputs** chooses, for each $j\in[\ell]$ and $b\in\{0,1\}$, an input $\gamma_{j,b}\in\{0,1,\star\}^\ell$ whose only unset coordinate is $j$, such that $g$ evaluates to $b$ on both completions of $\gamma_{j,b}$ (setting coordinate $j$ to $0$ or to $1$).
--
--   Such a family exists exactly when $g$ is 1-stifling. The measure $\mu$ of the lifting argument fixes the non-stifled coordinates of each selected block to $\gamma_{J_i,x_i}$, so that the block's gadget value is the sampled bit $x_i$.
--
--   **Formalization Note** $\gamma_{j,b}$ is a total input $\{0,1\}^\ell$ whose value at $j$ is never read; the unset coordinate $\star$ is encoded by that convention.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.1, p.13

import Mathlib

namespace LiftSAParity

/-- **Stifling inputs** `γ_{j,b}` (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree
to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §4.1, p.13): "For each
j ∈ [ℓ] and b ∈ {0, 1}, choose an input γ_{j,b} ∈ {0, 1, ⋆}^ℓ such that j is the only unset
coordinate and the gadget g evaluates to b on every completion of γ_{j,b} (i.e., by setting the jth
coordinate to 0 or to 1)."

`γ j b` is the input `γ_{j,b}`, and the specification is that `g` evaluates to `b` on both
completions `update (γ j b) j c`.

**Formalization Note** The unset coordinate `⋆` is encoded by a total input whose value at `j` is
never read: only the coordinates `k ≠ j` of `γ j b` are used (by `tildeProb`). Such a family exists
exactly when `g` is 1-stifling; the §4 milestones hold for every such choice. -/
def IsStiflingInputs {ℓ : ℕ} (g : (Fin ℓ → Bool) → Bool) (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) :
    Prop :=
  ∀ (j : Fin ℓ) (b c : Bool), g (Function.update (γ j b) j c) = b

end LiftSAParity


