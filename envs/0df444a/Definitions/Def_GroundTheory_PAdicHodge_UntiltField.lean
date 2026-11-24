-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltField
-- name    : GroundTheory_PAdicHodge_UntiltField
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:50.958452+00:00
-- url     : https://prove2.me/theorems/4b1658e4-b547-458a-b188-4d7ff114fe07
-- title:
--   Untilt Field
-- statement:
--   Definitions and structural lemmas for Untilt Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
variable (K C p) in

def integerTilt (N : IntermediateField K♭ C♭) : Subring 𝒪C♭ :=
  N.toSubfield.toSubring.comap (algebraMap 𝒪C♭ C♭)
theorem mem_integerTilt (N : IntermediateField K♭ C♭) {a : 𝒪C♭} : a ∈ integerTilt K C p N ↔ algebraMap 𝒪C♭ C♭ a ∈ N :=
  Iff.rfl
variable (K C p) in

def untiltInteger (N : IntermediateField K♭ C♭) : Subring (normInteger C) :=
  (RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype)).range
variable (K C p) in

def untiltField (N : IntermediateField K♭ C♭) : IntermediateField K C :=
  IntermediateField.adjoin K ((↑) '' (untiltInteger K C p N : Set (normInteger C)))
section Perfect
theorem frobeniusEquiv_symm_mem_integerTilt {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) :
    (frobeniusEquiv 𝒪C♭ p).symm a ∈ integerTilt K C p N := by
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  have : PerfectField N := Algebra.IsAlgebraic.perfectField (K := K♭)
  have : CharP N p := charP_of_injective_algebraMap (algebraMap K♭ N).injective p
  have : PerfectRing N p := PerfectField.toPerfectRing p
  set y : N := (frobeniusEquiv N p).symm ⟨algebraMap 𝒪C♭ C♭ a, ha⟩
  have hy : (y : C♭) ^ p = algebraMap 𝒪C♭ C♭ a := by
    have := frobeniusEquiv_symm_pow_p (R := N) p ⟨algebraMap 𝒪C♭ C♭ a, ha⟩
    exact congrArg Subtype.val this
  have ha' : (algebraMap 𝒪C♭ C♭ ((frobeniusEquiv 𝒪C♭ p).symm a)) ^ p = algebraMap 𝒪C♭ C♭ a := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  have : algebraMap 𝒪C♭ C♭ ((frobeniusEquiv 𝒪C♭ p).symm a) = y :=
    frobenius_inj C♭ p (by simp only [frobenius_def]; rw [ha', hy])
  rw [mem_integerTilt, this]
  exact y.2
instance perfectRing_integerTilt (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PerfectRing (integerTilt K C p N) p :=
  PerfectRing.ofSurjective (integerTilt K C p N) p fun a =>
    ⟨⟨(frobeniusEquiv 𝒪C♭ p).symm a, frobeniusEquiv_symm_mem_integerTilt a.2⟩,
      Subtype.ext (by
        change ((frobeniusEquiv 𝒪C♭ p).symm (a : 𝒪C♭)) ^ p = a
        exact frobeniusEquiv_symm_pow_p (R := 𝒪C♭) p _)⟩
end Perfect
end GroundTheory.PAdicHodge


