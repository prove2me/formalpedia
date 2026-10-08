-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechNakayama_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CechNakayama_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:30:49.341849+00:00
-- url     : https://prove2.me/theorems/33c759f4-9834-4158-83a3-1fcdcb6e1f84
-- title:
--   FLT.Assumptions.MazurProof.N13CechNakayama source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CechNakayama

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CechNakayama
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalAbelLinearization_p0
import Mathlib.RingTheory.LocalRing.Module

set_option autoImplicit false




/-!
# The Nakayama step in the N13 nonspecial Čech lift

For a two-affine Čech complex over a local ring, surjectivity of the
special-fibre coboundary implies surjectivity of the integral coboundary
when its target is finite.  Moreover, any integral cochain whose
coboundary vanishes modulo the maximal ideal can be corrected, without
changing its reduction, to an actual cocycle.

These are the module-theoretic steps in lifting the canonical section of
the fixed nonspecial degree-two divisor.  The curve-specific work still
has to identify the two bounded-pole Čech modules and prove special-fibre
surjectivity.  No Picard scheme or representative-existence hypothesis is
used here.
-/

namespace MazurProof.N13CechNakayama

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {C0 : Type v} {C1 : Type w}
variable [AddCommGroup C0] [Module R C0]
variable [AddCommGroup C1] [Module R C1]

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- A linear map to a finite module is surjective when its range is
surjective after quotienting by the maximal ideal. -/
theorem surjective_of_residue_range_eq_top
    [Module.Finite R C1]
    (d : C0 →ₗ[R] C1)
    (hres :
      (LinearMap.range d).map
          (Submodule.mkQ
            (𝔪 • (⊤ : Submodule R C1))) = ⊤) :
    Function.Surjective d := by
  rw [← LinearMap.range_eq_top]
  exact (IsLocalRing.map_mkQ_eq_top).mp hres

/-- Čech cocycles lift across the residue map once the special-fibre
coboundary is surjective: an arbitrary cochain lift can be corrected by a
cochain in the maximal-ideal multiple. -/
theorem exists_kernel_lift_of_residue_range_eq_top
    [Module.Finite R C1]
    (d : C0 →ₗ[R] C1)
    (hres :
      (LinearMap.range d).map
          (Submodule.mkQ
            (𝔪 • (⊤ : Submodule R C1))) = ⊤)
    (x : C0)
    (hx : d x ∈ 𝔪 • (⊤ : Submodule R C1)) :
    ∃ z : C0,
      d z = 0 ∧
        x - z ∈ 𝔪 • (⊤ : Submodule R C0) := by
  have hd : Function.Surjective d :=
    surjective_of_residue_range_eq_top d hres
  have hrange : LinearMap.range d = ⊤ :=
    LinearMap.range_eq_top.mpr hd
  have hmap :
      (𝔪 • (⊤ : Submodule R C0)).map d =
        𝔪 • (⊤ : Submodule R C1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  have hxmap :
      d x ∈ (𝔪 • (⊤ : Submodule R C0)).map d := by
    rwa [hmap]
  obtain ⟨t, ht, htx⟩ := hxmap
  refine ⟨x - t, ?_, ?_⟩
  · rw [map_sub, htx, sub_self]
  · simpa using ht

/-- Nakayama in the form needed for a genuine module-valued Čech complex:
a finite module vanishes when its reduction modulo the maximal ideal
vanishes. -/
theorem subsingleton_of_residue_subsingleton
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q]
    (hres :
      Subsingleton
        (Q ⧸
          (𝔪 • (⊤ : Submodule R Q)))) :
    Subsingleton Q := by
  have hmax :
      𝔪 • (⊤ : Submodule R Q) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hres
  have htopBot :
      (⊤ : Submodule R Q) = ⊥ := by
    apply
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        𝔪 (⊤ : Submodule R Q) Module.Finite.fg_top
    · rw [hmax]
    · rw [IsLocalRing.jacobson_eq_maximalIdeal
        (⊥ : Ideal R) bot_ne_top]
  have hsubmodules :
      Subsingleton (Submodule R Q) :=
    subsingleton_iff_bot_eq_top.mp htopBot.symm
  exact (Submodule.subsingleton_iff R).mp hsubmodules

/-- A linear map is surjective if its cokernel is finite and its residue
cokernel vanishes.  Unlike `surjective_of_residue_range_eq_top`, this does
not require the overlap module itself to be finite; only the actual Čech
cokernel must be finite.  In particular the source may retain an arbitrary
invertible affine module rather than a chosen global generator. -/
theorem surjective_of_finite_cokernel_of_residue_subsingleton
    (d : C0 →ₗ[R] C1)
    [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (hres :
      Subsingleton
        ((C1 ⧸ LinearMap.range d) ⧸
          (𝔪 •
            (⊤ :
              Submodule R
                (C1 ⧸ LinearMap.range d))))) :
    Function.Surjective d := by
  have hcoker :
      Subsingleton (C1 ⧸ LinearMap.range d) :=
    subsingleton_of_residue_subsingleton hres
  have hrange :
      LinearMap.range d = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hcoker
  exact LinearMap.range_eq_top.mp hrange

/-- Cocycles lift in the finite-cokernel formulation as well.  This is the
module-valued replacement for choosing a principal generator on the affine
chart: once the actual Čech cokernel has zero special fibre, an arbitrary
cochain lift can be corrected inside the maximal-ideal multiple. -/
theorem exists_kernel_lift_of_finite_cokernel_of_residue_subsingleton
    (d : C0 →ₗ[R] C1)
    [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (hres :
      Subsingleton
        ((C1 ⧸ LinearMap.range d) ⧸
          (𝔪 •
            (⊤ :
              Submodule R
                (C1 ⧸ LinearMap.range d)))))
    (x : C0)
    (hx : d x ∈ 𝔪 • (⊤ : Submodule R C1)) :
    ∃ z : C0,
      d z = 0 ∧
        x - z ∈ 𝔪 • (⊤ : Submodule R C0) := by
  have hd : Function.Surjective d :=
    surjective_of_finite_cokernel_of_residue_subsingleton d hres
  have hrange : LinearMap.range d = ⊤ :=
    LinearMap.range_eq_top.mpr hd
  have hmap :
      (𝔪 • (⊤ : Submodule R C0)).map d =
        𝔪 • (⊤ : Submodule R C1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange]
  have hxmap :
      d x ∈ (𝔪 • (⊤ : Submodule R C0)).map d := by
    rwa [hmap]
  obtain ⟨t, ht, htx⟩ := hxmap
  refine ⟨x - t, ?_, ?_⟩
  · rw [map_sub, htx, sub_self]
  · simpa using ht

end

end MazurProof.N13CechNakayama


