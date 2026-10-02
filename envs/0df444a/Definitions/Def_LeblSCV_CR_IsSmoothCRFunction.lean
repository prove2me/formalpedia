-- Prove2me | Definitions.Def_LeblSCV_CR_IsSmoothCRFunction
-- name    : LeblSCV_CR_IsSmoothCRFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:18:34.035266+00:00
-- url     : https://prove2.me/theorems/43224eb3-e679-43b1-be7e-dcbf37de9c5e
-- title:
--   Definition 3.2.3 — smooth CR function; real-analytic CR function
-- statement:
--   Let $M \subset \mathbb{C}^n$ be a smooth real hypersurface. A smooth function $f : M \to \mathbb{C}$ (Definition 3.2.1) is a **smooth CR function** if
--   $$X_p f = 0 \qquad \text{for all } p \in M \text{ and all } X_p \in T^{(0,1)}_p M.$$
--   Here $X_p f$ means $X_p F$ for any smooth extension $F$ of $f$ near $p$; the value does not depend on the extension (the book's Exercise 3.2.3), and $T^{(0,1)}_pM$ does not depend on the defining function used to compute it. A **real-analytic CR function** is a smooth CR function that is real-analytic on $M$ in the sense of Definition 3.2.1.
--
--   **Formalization Note.** `IsSmoothCRFunction M f` consists of: $M$ is a smooth real hypersurface; $f$ is smooth on $M$; and for every $p \in M$, every defining function $r$ of $M$ at $p$, every smooth extension $F$ of $f$ on an open neighborhood of $p$, and every coefficient vector $a$ in `antiholTangent r p`, $\sum_k a_k\, \partial F/\partial \bar z_k(p) = 0$. The condition is imposed for every choice of $r$ and $F$; since the quantity is independent of the choice, this is equivalent to imposing it for one choice. `IsRealAnalyticCRFunction M f` is `IsRealAnalyticOnSet M f ∧ IsSmoothCRFunction M f`. Both are in this file.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 111, Definition 3.2.3

import Mathlib
import Definitions.Def_LeblSCV_CR_IsSmoothHypersurface
import Definitions.Def_LeblSCV_CR_IsSmoothOnSet
import Definitions.Def_LeblSCV_CR_antiholTangent

open scoped ContDiff

namespace LeblSCV.CR

/-- Definition 3.2.3 (Lebl, p. 111): for a smooth real hypersurface `M ⊂ ℂⁿ`, a smooth
`f : M → ℂ` (Definition 3.2.1) is a smooth CR function if `X_p f = 0` for all `p ∈ M` and all
`X_p = ∑ a_k ∂/∂z̄_k|_p ∈ T_p^{(0,1)} M`. `X_p f` is computed on a smooth extension `F` of `f`
near `p` and `T_p^{(0,1)} M` from a defining function `r` at `p`; both are independent of the
choice (Exercise 3.2.3, p. 64), and the condition is required for every such choice. -/
def IsSmoothCRFunction {n : ℕ} (M : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ) : Prop :=
  IsSmoothHypersurface M ∧ IsSmoothOnSet M f ∧
    ∀ p ∈ M, ∀ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ), IsLocalDefiningFunction M p V r →
      ∀ (U : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ), IsOpen U → p ∈ U → ContDiffOn ℝ ∞ F U →
        (∀ q ∈ M ∩ U, F q = f q) →
        ∀ a ∈ antiholTangent r p, ∑ k, a k * wirtingerZbar F k p = 0

/-- A real-analytic CR function (Lebl, pp. 111–115): a smooth CR function on `M` (Definition 3.2.3)
that is real-analytic on `M` in the sense of Definition 3.2.1. -/
def IsRealAnalyticCRFunction {n : ℕ} (M : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ) : Prop :=
  IsRealAnalyticOnSet M f ∧ IsSmoothCRFunction M f

end LeblSCV.CR


