-- Prove2me | Definitions.Def_TeschlQM_Herglotz_IsMinimalSupport
-- name    : TeschlQM_Herglotz_IsMinimalSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:01.20796+00:00
-- url     : https://prove2.me/theorems/16975997-a6de-4aee-b5a4-4c40ef475ace
-- title:
--   Minimal (essential) support of a measure
-- statement:
--   A support $M$ of a measure $\mu$ on $\mathbb{R}$ (so $\mu(\mathbb{R} \setminus M) = 0$) is a **minimal support**, also called an **essential support**, if every subset of $M$ that does not support $\mu$ is Lebesgue-null:
--   $$\mu(\mathbb{R}\setminus M) = 0 \quad\text{and}\quad \bigl(M_0 \subseteq M,\ \mu(M_0) = 0\bigr) \implies |M_0| = 0,$$
--   where $|M_0|$ is the Lebesgue measure of $M_0$.
--
--   **Formalization Note.** The subsets $M_0$ range over Borel sets (`MeasurableSet M₀`), the $\sigma$-algebra on which the book's measures are defined.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 286, Section A.8 (after Theorem A.38)

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 286 (after Theorem A.38): a support `M` of a measure `μ` on `ℝ` (`μ(ℝ \ M) = 0`)
is a **minimal support** if every (Borel) subset `M₀ ⊆ M` which does not support `μ`, i.e. with
`μ(M₀) = 0`, has Lebesgue measure zero. -/
def IsMinimalSupport (μ : Measure ℝ) (M : Set ℝ) : Prop :=
  μ Mᶜ = 0 ∧ ∀ M₀ : Set ℝ, MeasurableSet M₀ → M₀ ⊆ M → μ M₀ = 0 → volume M₀ = 0

end TeschlQM.Herglotz


