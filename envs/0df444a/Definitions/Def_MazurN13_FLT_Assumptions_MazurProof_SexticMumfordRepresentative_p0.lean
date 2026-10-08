-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordRepresentative_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordRepresentative_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:00:55.05097+00:00
-- url     : https://prove2.me/theorems/a33cdcf5-f5e8-4049-849d-79ac63d9bb42
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordRepresentative source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordRepresentative

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordRepresentative
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNormalForm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNorm_p0

set_option autoImplicit false




/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

/- Keep generated structure auxiliaries from expanding the coordinate-ring
presentation while comparing fields under independent parameters. These aliases
are reducible again immediately after the structure is generated. -/
private def IntegralRepIdeal : Type u := Ideal (CoordinateRing M)
private def IntegralRepUnit : Type u := InvFrac M
private def IntegralRepCoeEq (I : IntegralRepIdeal M) (z : IntegralRepUnit M) : Prop :=
  ((show InvFrac M from z) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
    ((show Ideal (CoordinateRing M) from I) :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

section
attribute [local irreducible] IntegralRepIdeal IntegralRepUnit

/-- An oriented representative whose finite component is an integral ideal.
The unit remembers that this ideal is invertible as a fractional ideal. -/
structure IntegralOrientedRep where
  ideal : IntegralRepIdeal M
  unit : IntegralRepUnit M
  coe_unit : IntegralRepCoeEq M ideal unit
  atInfinity : ℤ

end
attribute [reducible] IntegralRepIdeal IntegralRepUnit IntegralRepCoeEq

namespace IntegralOrientedRep

/-- The raw oriented fractional ideal underlying an integral representative. -/
def raw (R : IntegralOrientedRep M) : OrientedFrac M :=
  (R.unit, Multiplicative.ofAdd R.atInfinity)

/-- The oriented Picard class of an integral representative. -/
def picClass (R : IntegralOrientedRep M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range (R.raw M)

theorem ideal_ne_bot (R : IntegralOrientedRep M) : R.ideal ≠ ⊥ := by
  intro h
  have hzero :
      (R.unit :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 0 := by
    rw [R.coe_unit, h]
    rfl
  exact R.unit.ne_zero hzero

theorem ideal_isUnit (R : IntegralOrientedRep M) :
    IsUnit
      (R.ideal :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  exact ⟨R.unit, R.coe_unit⟩

end IntegralOrientedRep

/-- The affine coordinate ring is free of rank two over `K[X]`, with the
power basis `1,Y`.  The index is rewritten using the proved degree of the
quadratic equation rather than by computation. -/
def polynomialBasis :
    Module.Basis (Fin 2) K[X] (CoordinateRing M) :=
  (AdjoinRoot.powerBasis' (curvePoly_monic M)).basis.reindex
    (finCongr (curvePoly_natDegree M))

/-- Every nonzero integral ideal is a rank-two `K[X]`-lattice.  Mathlib's
PID structure theorem supplies compatible two-element bases for the ambient
coordinate ring and the ideal. -/
theorem ideal_exists_two_generator_smith_form
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    ∃ (bR : Module.Basis (Fin 2) K[X] (CoordinateRing M))
      (a : Fin 2 → K[X])
      (bJ : Module.Basis (Fin 2) K[X] J),
      ∀ i, (bJ i : CoordinateRing M) = a i • bR i := by
  exact Ideal.exists_smith_normal_form (polynomialBasis M) J hJ

/-- In particular, the integral ideal attached to every oriented
representative has a structural two-generator Smith presentation. -/
theorem IntegralOrientedRep.exists_two_generator_smith_form
    (R : IntegralOrientedRep M) :
    ∃ (bR : Module.Basis (Fin 2) K[X] (CoordinateRing M))
      (a : Fin 2 → K[X])
      (bJ : Module.Basis (Fin 2) K[X] R.ideal),
      ∀ i, (bJ i : CoordinateRing M) = a i • bR i := by
  exact ideal_exists_two_generator_smith_form M R.ideal
    (R.ideal_ne_bot M)

/-- Contract an integral ideal from the quadratic coordinate ring to its
polynomial subring. -/
def idealContraction (J : Ideal (CoordinateRing M)) : Ideal K[X] :=
  J.comap (xClassHom M)

/-- A nonzero ideal has nonzero contraction to `K[X]`.  The structural
reason is that the quadratic norm of any nonzero ideal element is a nonzero
polynomial lying in the contraction. -/
theorem idealContraction_ne_bot (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : idealContraction M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let p : K[X] :=
    (coeff0 M z) ^ 2 - (coeffY M z) ^ 2 * M.f
  have hconj : conjugate M z ≠ 0 := by
    intro hc
    apply hz
    calc
      z = conjugate M (conjugate M z) :=
        (conjugate_involutive M z).symm
      _ = 0 := by rw [hc, map_zero]
  have hnorm : norm M z ≠ 0 :=
    mul_ne_zero hz hconj
  have hp : p ≠ 0 := by
    intro hp
    apply hnorm
    rw [norm_eq_xClass_coeff]
    change xClass M p = 0
    rw [hp, xClass_zero]
  intro hbot
  have hpmem : p ∈ idealContraction M J := by
    change xClass M p ∈ J
    rw [← norm_eq_xClass_coeff]
    exact J.mul_mem_right (conjugate M z) hzJ
  rw [hbot, Ideal.mem_bot] at hpmem
  exact hp hpmem

/-- The canonical monic generator of the contraction of an integral ideal
to `K[X]`. -/
def contractionGenerator (J : Ideal (CoordinateRing M)) : K[X] := by
  classical
  exact normalize
    (Submodule.IsPrincipal.generator (idealContraction M J))

theorem contractionGenerator_monic (J : Ideal (CoordinateRing M))
    (hJ : J ≠ ⊥) : (contractionGenerator M J).Monic := by
  classical
  unfold contractionGenerator
  apply Polynomial.monic_normalize
  intro hgen
  exact idealContraction_ne_bot M J hJ
    ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (idealContraction M J)).mpr hgen)

theorem span_contractionGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contractionGenerator M J} : Set K[X]) =
      idealContraction M J := by
  classical
  unfold contractionGenerator
  calc
    Ideal.span
        ({normalize
          (Submodule.IsPrincipal.generator
            (idealContraction M J))} : Set K[X]) =
        Ideal.span
          ({Submodule.IsPrincipal.generator
            (idealContraction M J)} : Set K[X]) := by
      apply Ideal.span_singleton_eq_span_singleton.mpr
      exact (associated_normalize
        (Submodule.IsPrincipal.generator
          (idealContraction M J))).symm
    _ = idealContraction M J :=
      Ideal.span_singleton_generator (idealContraction M J)

theorem xClass_contractionGenerator_mem
    (J : Ideal (CoordinateRing M)) :
    xClass M (contractionGenerator M J) ∈ J := by
  change contractionGenerator M J ∈ idealContraction M J
  rw [← span_contractionGenerator M J]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- On an existing balanced Mumford ideal, the canonical contraction
generator recovers its `u`-polynomial. -/
theorem contractionGenerator_mumfordIdeal (D : Mumford M) :
    contractionGenerator M (mumfordIdeal M D.u D.v) = D.u := by
  apply Polynomial.eq_of_monic_of_associated
    (contractionGenerator_monic M _
      (mumfordIdeal_ne_bot M D))
    D.u_monic
  apply Ideal.span_singleton_eq_span_singleton.mp
  calc
    Ideal.span
        ({contractionGenerator M
          (mumfordIdeal M D.u D.v)} : Set K[X]) =
        idealContraction M (mumfordIdeal M D.u D.v) :=
      span_contractionGenerator M _
    _ = Ideal.span ({D.u} : Set K[X]) :=
      mumfordIdeal_comap_base M D.toSemi

/-- If an integral ideal has contraction `(u)` and contains one graph
generator `Y-v`, then it is exactly the corresponding Mumford ideal.  This
is the quadratic Hermite-normal-form step, proved from the rank-two
coefficient decomposition. -/
theorem mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    (J : Ideal (CoordinateRing M)) (u v : K[X])
    (hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]))
    (hgraph : ySubClass M v ∈ J) :
    mumfordIdeal M u v = J := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change u ∈ idealContraction M J
      rw [hcontraction]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact hgraph
  · intro w hw
    let q : K[X] := coeffY M w
    let r : CoordinateRing M :=
      w - xClass M q * ySubClass M v
    have hrJ : r ∈ J :=
      J.sub_mem hw (J.mul_mem_left (xClass M q) hgraph)
    have hrY : coeffY M r = 0 := by
      simp [r, q]
    have hrRecompose : xClass M (coeff0 M r) = r := by
      simpa [hrY] using recompose M r
    have hrContract :
        coeff0 M r ∈ idealContraction M J := by
      change xClass M (coeff0 M r) ∈ J
      rw [hrRecompose]
      exact hrJ
    rw [hcontraction, Ideal.mem_span_singleton] at hrContract
    obtain ⟨t, ht⟩ := hrContract
    have hrMumford : r ∈ mumfordIdeal M u v := by
      rw [← hrRecompose, ht, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left _ (xClass M t)
        (xClass_mem_mumfordIdeal M u v)
    have hgraphMumford :
        xClass M q * ySubClass M v ∈ mumfordIdeal M u v :=
      Ideal.mul_mem_left _ (xClass M q)
        (Ideal.subset_span (by simp))
    have hwdecomp :
        w = r + xClass M q * ySubClass M v := by
      simp [r]
    rw [hwdecomp]
    exact Ideal.add_mem _ hrMumford hgraphMumford

/-- An integral ideal is primitive when some element has `Y`-coefficient
one.  This is the exact algebraic hypothesis needed to put it in Mumford
graph form. -/
def IdealIsPrimitive (J : Ideal (CoordinateRing M)) : Prop :=
  ∃ z ∈ J, coeffY M z = 1

/-- A primitive nonzero integral ideal has a semireduced Mumford
presentation.  The `u`-polynomial is the canonical contraction generator,
and `v` is reduced modulo `u`.  No degree bound or class enumeration enters
the proof. -/
theorem exists_semiMumford_of_primitive
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥)
    (hprimitive : IdealIsPrimitive M J) (n : ℤ) :
    ∃ D : SemiMumford M,
      mumfordIdeal M D.u D.v = J ∧
      D.u = contractionGenerator M J ∧
      D.nInf = n := by
  obtain ⟨z, hzJ, hzY⟩ := hprimitive
  let u : K[X] := contractionGenerator M J
  let v0 : K[X] := -(coeff0 M z)
  let v : K[X] := v0 % u
  have huMonic : u.Monic :=
    contractionGenerator_monic M J hJ
  have hu : u ≠ 0 := huMonic.ne_zero
  have hcontraction :
      idealContraction M J = Ideal.span ({u} : Set K[X]) :=
    (span_contractionGenerator M J).symm
  have hgraph0 : ySubClass M v0 = z := by
    calc
      ySubClass M v0 =
          xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              simp [ySubClass, v0, hzY]
              ring
      _ = z := recompose M z
  have hvdecomp : v + u * (v0 / u) = v0 :=
    EuclideanDomain.mod_add_div v0 u
  have hgraph : ySubClass M v ∈ J := by
    have hpoly : v0 - v = u * (v0 / u) := by
      calc
        v0 - v = (v + u * (v0 / u)) - v :=
          congrArg (fun t : K[X] => t - v) hvdecomp.symm
        _ = u * (v0 / u) := by ring
    have hmultiple :
        xClass M (v0 - v) ∈ J := by
      rw [hpoly, xClass_mul, mul_comm]
      exact J.mul_mem_left (xClass M (v0 / u))
        (xClass_contractionGenerator_mem M J)
    have heq :
        ySubClass M v =
          ySubClass M v0 + xClass M (v0 - v) := by
      simp [ySubClass, xClass_sub]
    rw [heq]
    exact J.add_mem (hgraph0 ▸ hzJ) hmultiple
  have hcurve : u ∣ M.f - v ^ 2 := by
    have hprod :
        ySubClass M v * (yClass M + xClass M v) =
          xClass M (M.f - v ^ 2) := by
      simp only [ySubClass]
      calc
        (yClass M - xClass M v) *
            (yClass M + xClass M v) =
            yClass M ^ 2 - xClass M v ^ 2 := by ring
        _ = xClass M M.f - xClass M v ^ 2 := by
          rw [yClass_sq]
        _ = xClass M (M.f - v ^ 2) := by
          rw [xClass_sub, xClass_pow]
    have hmem :
        M.f - v ^ 2 ∈ idealContraction M J := by
      change xClass M (M.f - v ^ 2) ∈ J
      rw [← hprod]
      exact J.mul_mem_right (yClass M + xClass M v) hgraph
    rw [hcontraction, Ideal.mem_span_singleton] at hmem
    exact hmem
  let D : SemiMumford M :=
    { u := u
      v := v
      nInf := n
      u_monic := huMonic
      v_reduced := by
        rw [Polynomial.mod_eq_self_iff hu]
        exact EuclideanDomain.mod_lt _ hu
      curve_dvd := hcurve }
  refine ⟨D, ?_, rfl, rfl⟩
  exact mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem
    M J u v hcontraction hgraph

/-- Every raw oriented fractional ideal is equivalent, modulo a principal
oriented ideal, to one with an integral finite component. -/
theorem exists_integralRep_of_raw (I : InvFrac M)
    (n : Multiplicative ℤ) :
    ∃ R : IntegralOrientedRep M,
      QuotientGroup.mk' (principalOriented M O).range (I, n) =
        Additive.toMul (R.picClass M O) := by
  obtain ⟨a, J, ha, hI⟩ := invFrac_exists_integral_scaling M I
  have haMap :
      algebraMap (CoordinateRing M) (FunctionField M) a ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (show a ∈ (CoordinateRing M)⁰ from
        mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  let alpha : (FunctionField M)ˣ :=
    Units.mk0
      (algebraMap (CoordinateRing M) (FunctionField M) a) haMap
  let U : InvFrac M :=
    I * toPrincipalIdeal (CoordinateRing M) (FunctionField M) alpha
  have hU :
      (U :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = J := by
    simp only [U, Units.val_mul, coe_toPrincipalIdeal, alpha,
      Units.val_mk0]
    rw [hI]
    calc
      (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) *
          FractionalIdeal.spanSingleton (CoordinateRing M)⁰
            (algebraMap (CoordinateRing M) (FunctionField M) a) =
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ *
            FractionalIdeal.spanSingleton (CoordinateRing M)⁰
              (algebraMap (CoordinateRing M) (FunctionField M) a)) *
          (J :
            FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
              ac_rfl
      _ = J := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        simp [haMap]
  let R : IntegralOrientedRep M :=
    { ideal := J
      unit := U
      coe_unit := hU
      atInfinity :=
        Multiplicative.toAdd (n * O.ordPlus alpha) }
  refine ⟨R, ?_⟩
  change
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
      QuotientGroup.mk' (principalOriented M O).range
        (U, Multiplicative.ofAdd R.atInfinity)
  have hprincipal :
      QuotientGroup.mk' (principalOriented M O).range
          (principalOriented M O alpha) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff
      (principalOriented M O alpha)).2
      (MonoidHom.mem_range.mpr ⟨alpha, rfl⟩)
  calc
    QuotientGroup.mk' (principalOriented M O).range (I, n) =
        QuotientGroup.mk' (principalOriented M O).range
          ((I, n) * principalOriented M O alpha) := by
            rw [map_mul, hprincipal]
            exact (mul_one (QuotientGroup.mk'
              (principalOriented M O).range (I, n))).symm
    _ = QuotientGroup.mk' (principalOriented M O).range
          (U, Multiplicative.ofAdd R.atInfinity) := by
            rfl

/-- Every oriented Picard class has an integral invertible-ideal
representative.  No Dedekind-domain or class-number hypothesis is used. -/
theorem exists_integralRepresentative (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M, R.picClass M O = c := by
  change
    ∃ R : IntegralOrientedRep M,
      Additive.toMul (R.picClass M O) = Additive.toMul c
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (principalOriented M O).range
      (Additive.toMul c)
  obtain ⟨R, hR⟩ :=
    exists_integralRep_of_raw M O x.1 x.2
  exact ⟨R, hR.symm.trans hx⟩

/-- Integral ideal reduction is the only extra input needed for existence of
balanced Mumford representatives. -/
theorem classOf_surjective_of_integral_reduction
    (reduce :
      ∀ R : IntegralOrientedRep M,
        ∃ D : Mumford M, classOf M O D = R.picClass M O) :
    Function.Surjective (classOf M O) := by
  intro c
  obtain ⟨R, hR⟩ := exists_integralRepresentative M O c
  obtain ⟨D, hD⟩ := reduce R
  exact ⟨D, hD.trans hR⟩

end

end MazurProof.SexticMumford


