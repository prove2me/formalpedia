-- Prove2me | Definitions.Def_TeschlQM_Atomic_smoothCompactSupport
-- name    : TeschlQM_Atomic_smoothCompactSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:52:16.643847+00:00
-- url     : https://prove2.me/theorems/d0b3bb34-f2c7-46d9-910b-1d80e8a906f7
-- title:
--   C₀^∞(ℝⁿ) as a subspace of L²(ℝⁿ)
-- statement:
--   $C_0^\infty(\mathbb R^n)$ is the space of smooth ($C^\infty$) complex-valued functions on $\mathbb R^n$ with compact support, regarded as a subspace of $L^2(\mathbb R^n)$.
--
--   Theorem 11.1 asserts that it is a core for the $N$-body Hamiltonian.
--
--   **Formalization Note.** `smoothCompactSupport ι` is the `Submodule` of `Lp ℂ 2 volume` on `EuclideanSpace ℝ ι` spanned by the classes that have a representative $f$ with `ContDiff ℝ ∞ f` and `HasCompactSupport f`; these classes already form a subspace, so the span adds nothing.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 241, Theorem 11.1

import Mathlib

namespace TeschlQM.Atomic

open MeasureTheory
open scoped ContDiff

/-- `C₀^∞(ℝⁿ)` as a subspace of `L²(ℝⁿ)`: the elements of `L²` which have a representative that
is smooth (`C^∞`) and compactly supported. (The set of such classes is already a subspace; the
span only records it as a `Submodule`.) -/
noncomputable def smoothCompactSupport (ι : Type*) [Fintype ι] :
    Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :=
  Submodule.span ℂ {ψ | ∃ f : EuclideanSpace ℝ ι → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (ψ : EuclideanSpace ℝ ι → ℂ) =ᵐ[volume] f}

end TeschlQM.Atomic


