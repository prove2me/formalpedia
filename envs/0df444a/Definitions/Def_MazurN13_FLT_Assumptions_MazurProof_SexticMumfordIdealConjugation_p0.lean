-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdealConjugation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdealConjugation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:59:55.807614+00:00
-- url     : https://prove2.me/theorems/72647f71-3214-4cf3-a832-fc3b01a05c20
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordIdealConjugation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticFunctionConjugation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordUnit_p0

set_option autoImplicit false




/-!
# Conjugation of Mumford ideals

Hyperelliptic conjugation sends `(u, Y-v)` to `(u, Y+v)`.  The following lifts
that elementary generator identity to integral and fractional ideals.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

theorem map_conjugate_mumfordIdeal (M : Model K) (u v : K[X]) :
    Ideal.map (conjugate M) (mumfordIdeal M u v) =
      mumfordIdeal M u (-v) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change conjugate M (xClass M u) ∈ mumfordIdeal M u (-v)
      rw [conjugate_xClass]
      exact xClass_mem_mumfordIdeal M u (-v)
    · change conjugate M (ySubClass M v) ∈ mumfordIdeal M u (-v)
      have htarget : ySubClass M (-v) ∈ mumfordIdeal M u (-v) :=
        ySubClass_mem_mumfordIdeal M u (-v)
      have heq :
          conjugate M (ySubClass M v) = -ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [heq]
      exact (mumfordIdeal M u (-v)).neg_mem htarget
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simpa using Ideal.mem_map_of_mem (conjugate M)
        (xClass_mem_mumfordIdeal M u v)
    · have hsource :
          -ySubClass M v ∈ mumfordIdeal M u v :=
        (mumfordIdeal M u v).neg_mem
          (ySubClass_mem_mumfordIdeal M u v)
      have hmap := Ideal.mem_map_of_mem (conjugate M) hsource
      have heq :
          conjugate M (-ySubClass M v) = ySubClass M (-v) := by
        simp [ySubClass]
        ring
      rw [← heq]
      exact hmap

def conjugateFractionalIdealEquiv (M : Model K) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) ≃+*
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) :=
  FractionalIdeal.ringEquivOfRingEquiv
    (FunctionField M) (FunctionField M) (conjugateEquiv M)

theorem conjugateFractionalIdealEquiv_coeIdeal
    (M : Model K) (I : Ideal (CoordinateRing M)) :
    conjugateFractionalIdealEquiv M
        (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (Ideal.map (conjugate M) I :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  ext x
  simp only [conjugateFractionalIdealEquiv,
    FractionalIdeal.ringEquivOfRingEquiv_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjugate M a, Ideal.mem_map_of_mem (conjugate M) ha, ?_⟩
    change algebraMap (CoordinateRing M) (FunctionField M)
        (conjugate M a) =
      functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a)
    exact (functionConjugateEquiv_algebraMap M a).symm
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_iff_of_surjective (conjugate M)
      (conjugate_involutive M).surjective] at hb
    obtain ⟨a, ha, hab⟩ := hb
    refine ⟨algebraMap (CoordinateRing M) (FunctionField M) a,
      FractionalIdeal.mem_coeIdeal_of_mem _ ha, ?_⟩
    change functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) a) =
      algebraMap (CoordinateRing M) (FunctionField M) b
    rw [functionConjugateEquiv_algebraMap, hab]

@[simp] theorem conjugateFractionalIdealEquiv_mumfordIdeal
    (M : Model K) (u v : K[X]) :
    conjugateFractionalIdealEquiv M
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M u (-v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  rw [conjugateFractionalIdealEquiv_coeIdeal,
    map_conjugate_mumfordIdeal]

@[simp] theorem conjugateFractionalIdealEquiv_spanSingleton
    (M : Model K) (z : FunctionField M) :
    conjugateFractionalIdealEquiv M
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰ z) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (functionConjugateEquiv M z) := by
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (FunctionField M) (FunctionField M) (conjugateEquiv M) z

def conjugateInvFrac (M : Model K) : InvFrac M →* InvFrac M :=
  Units.map (conjugateFractionalIdealEquiv M).toRingHom

@[simp] theorem conjugateInvFrac_principal
    (M : Model K) (z : (FunctionField M)ˣ) :
    conjugateInvFrac M
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) z) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (conjugateFunctionUnit M z) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      ((toPrincipalIdeal (CoordinateRing M) (FunctionField M) z :
        InvFrac M) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((toPrincipalIdeal (CoordinateRing M) (FunctionField M)
      (conjugateFunctionUnit M z) : InvFrac M) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    conjugateFractionalIdealEquiv_spanSingleton,
    conjugateFunctionUnit_val]

def conjugateSemiMumford (M : Model K) (D : SemiMumford M) :
    SemiMumford M where
  u := D.u
  v := -D.v
  nInf := D.nInf
  u_monic := D.u_monic
  v_reduced := by
    rw [← Polynomial.modByMonic_eq_mod (-D.v) D.u_monic,
      Polynomial.neg_modByMonic,
      Polynomial.modByMonic_eq_mod D.v D.u_monic,
      D.v_reduced]
  curve_dvd := by
    simpa only [neg_sq] using D.curve_dvd

@[simp] theorem conjugateSemiMumford_u (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).u = D.u := rfl

@[simp] theorem conjugateSemiMumford_v (M : Model K)
    (D : SemiMumford M) : (conjugateSemiMumford M D).v = -D.v := rfl

@[simp] theorem conjugateInvFrac_mumfordIdealUnit
    (M : Model K) (D : SemiMumford M) :
    conjugateInvFrac M (mumfordIdealUnit M D) =
      mumfordIdealUnit M (conjugateSemiMumford M D) := by
  apply Units.ext
  change conjugateFractionalIdealEquiv M
      (mumfordIdeal M D.u D.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    (mumfordIdeal M D.u (-D.v) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))
  rw [conjugateFractionalIdealEquiv_mumfordIdeal]

theorem conjugate_principal_relation
    (M : Model K) (D₁ D₂ : SemiMumford M)
    (z : (FunctionField M)ˣ)
    (h :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) z =
        mumfordIdealUnit M D₂) :
    mumfordIdealUnit M (conjugateSemiMumford M D₁) *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (conjugateFunctionUnit M z) =
        mumfordIdealUnit M (conjugateSemiMumford M D₂) := by
  have hmap := congrArg (conjugateInvFrac M) h
  simpa only [map_mul, conjugateInvFrac_mumfordIdealUnit,
    conjugateInvFrac_principal] using hmap

end

end MazurProof.SexticMumford


