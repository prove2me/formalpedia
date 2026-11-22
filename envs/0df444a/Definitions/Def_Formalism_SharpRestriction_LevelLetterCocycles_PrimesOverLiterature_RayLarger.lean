-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayLarger
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_PrimesOverLiterature_RayLarger
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:15.557535+00:00
-- url     : https://prove2.me/theorems/8cdb658f-52a9-471c-aba3-287ac6c5c6ae
-- title:
--   Ray Larger
-- statement:
--   Definitions and structural lemmas for Ray Larger, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/PrimesOverLiterature/RayLarger.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.N.Lit.RayLarger
open NumberField IsDedekindDomain
abbrev Qb : Type := AlgebraicClosure ℚ
abbrev Fld : Type := IntermediateField ℚ Qb
def primesOver (L : Fld) (p : ℕ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}
def SplitsCompletely (L : Fld) (p : ℕ) : Prop :=
  (primesOver L p).ncard = Module.finrank ℚ L
def IsRayPrime (K : Fld) (m p : ℕ) : Prop :=
  p.Prime ∧ ∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (m : Qb)) ∧
    ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)
def Admissible (K : Fld) (m : ℕ) (L : Fld) : Prop :=
  K ≤ L ∧ FiniteDimensional ℚ L ∧ ∀ p, IsRayPrime K m p → SplitsCompletely L p
def Stmt : Prop :=
  ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∃ (p : ℕ) (L : Fld), p.Prime ∧ ¬ p ∣ m ∧
      (∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)) ∧
      Admissible K m L ∧ ¬ SplitsCompletely L p
example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide
end Formalism.MainNotions.N.Lit.RayLarger


