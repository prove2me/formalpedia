-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdeal_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordIdeal_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:52:33.186987+00:00
-- url     : https://prove2.me/theorems/90365d01-5d79-41c8-9ae2-b55cab703011
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordIdeal source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordIdeal

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordIdeal
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0

set_option autoImplicit false




/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

abbrev MumfordResidue (D : SemiMumford M) : Type u :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

private theorem mumford_root_relation (D : SemiMumford M) :
    (curvePoly M).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 - M.f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := D.curve_dvd
  refine ⟨-w, ?_⟩
  calc
    D.v ^ 2 - M.f = -(M.f - D.v ^ 2) := by ring
    _ = -(D.u * w) := by rw [hw]
    _ = D.u * (-w) := by ring

def mumfordEval (D : SemiMumford M) :
    CoordinateRing M →+* MumfordResidue M D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation M D)

@[simp] theorem mumfordEval_xClass (D : SemiMumford M) (p : K[X]) :
    mumfordEval M D (xClass M p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval M D (AdjoinRoot.of (curvePoly M) p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation M D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford M) :
    mumfordEval M D (yClass M) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation M D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford M) :
    mumfordEval M D (ySubClass M D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford M) :
    mumfordIdeal M D.u D.v ≤ RingHom.ker (mumfordEval M D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval M D (xClass M D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · change mumfordEval M D (ySubClass M D.v) = 0
    rw [mumfordEval_ySubClass]

theorem ker_mumfordEval (D : SemiMumford M) :
    RingHom.ker (mumfordEval M D) = mumfordIdeal M D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 M z
    let q : K[X] := coeffY M z
    have hz' : mumfordEval M D
        (xClass M p + xClass M q * yClass M) = 0 := by
      rw [recompose M z]
      exact hz
    have hquot : Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass, map_add, map_mul] using hz'
    have hdvd : D.u ∣ p + q * D.v := by
      exact Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass M D.u ∈ mumfordIdeal M D.u D.v :=
      xClass_mem_mumfordIdeal M D.u D.v
    have hyv : ySubClass M D.v ∈ mumfordIdeal M D.u D.v :=
      Ideal.subset_span (by simp)
    have hbase : xClass M (p + q * D.v) ∈
        mumfordIdeal M D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M s) hu
    have hgraph : xClass M q * ySubClass M D.v ∈
        mumfordIdeal M D.u D.v :=
      Ideal.mul_mem_left (mumfordIdeal M D.u D.v) (xClass M q) hyv
    rw [← recompose M z]
    have hdecomp :
        xClass M p + xClass M q * yClass M =
          xClass M (p + q * D.v) + xClass M q * ySubClass M D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker M D

theorem mumfordEval_surjective (D : SemiMumford M) :
    Function.Surjective (mumfordEval M D) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨xClass M p, mumfordEval_xClass M D p⟩

/-- The graph quotient is canonically the monic polynomial quotient. -/
noncomputable def mumfordQuotientEquiv (D : SemiMumford M) :
    CoordinateRing M ⧸ mumfordIdeal M D.u D.v ≃+*
      MumfordResidue M D :=
  (Ideal.quotEquivOfEq (ker_mumfordEval M D).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (mumfordEval_surjective M D))

@[simp] theorem mumfordQuotientEquiv_apply_mk
    (D : SemiMumford M) (z : CoordinateRing M) :
    mumfordQuotientEquiv M D
        (Ideal.Quotient.mk (mumfordIdeal M D.u D.v) z) =
      mumfordEval M D z := by
  simp [mumfordQuotientEquiv]

/-- The graph quotient equivalence respects the coefficient field. -/
noncomputable def mumfordQuotientAlgEquiv (D : SemiMumford M) :
    (CoordinateRing M ⧸ mumfordIdeal M D.u D.v) ≃ₐ[K]
      MumfordResidue M D :=
  AlgEquiv.ofRingEquiv
    (f := mumfordQuotientEquiv M D)
    (by
      intro r
      change
        mumfordQuotientEquiv M D
            (Ideal.Quotient.mk
              (mumfordIdeal M D.u D.v) (xClass M (C r))) =
          Ideal.Quotient.mk
            (Ideal.span ({D.u} : Set K[X])) (C r)
      rw [mumfordQuotientEquiv_apply_mk,
        mumfordEval_xClass])

theorem mumfordIdeal_comap_base (D : SemiMumford M) :
    (mumfordIdeal M D.u D.v).comap (xClassHom M) =
      Ideal.span ({D.u} : Set K[X]) := by
  rw [← ker_mumfordEval]
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, xClassHom_apply,
    mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem]

end

end MazurProof.SexticMumford


