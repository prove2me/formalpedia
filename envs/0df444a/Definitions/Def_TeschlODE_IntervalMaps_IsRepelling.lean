-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_IsRepelling
-- name    : TeschlODE_IntervalMaps_IsRepelling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:29:37.327844+00:00
-- url     : https://prove2.me/theorems/35bf0b11-3e86-4fa4-a21a-4b4f4547a5fa
-- title:
--   Repelling compact invariant set
-- statement:
--   Let $f : X \to X$ on a metric space. A set $\Lambda \subseteq X$ is **repelling** if it is compact, invariant in the sense $f(\Lambda) = \Lambda$, and there is a neighborhood $U$ of $\Lambda$ such that every $x \in U \setminus \Lambda$ eventually leaves $U$:
--   $$\exists n : f^n(x) \notin U .$$
--
--   **Formalization Note.** "Neighborhood of $\Lambda$" is Mathlib's `nhdsSet Λ`: $U$ contains an open set containing $\Lambda$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 307, §11.6

import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.6, p. 307: a compact invariant set `Λ`, `f(Λ) = Λ`, is repelling if there is a
neighborhood `U` of `Λ` (`U ∈ 𝓝ˢ Λ`: `U` contains an open set containing `Λ`) such that for all
`x ∈ U \ Λ` there is an `n` with `fⁿ(x) ∉ U`. -/
def IsRepelling {X : Type*} [MetricSpace X] (f : X → X) (Λ : Set X) : Prop :=
  IsCompact Λ ∧ f '' Λ = Λ ∧
    ∃ U ∈ nhdsSet Λ, ∀ x ∈ U \ Λ, ∃ n : ℕ, f^[n] x ∉ U

end TeschlODE.IntervalMaps


