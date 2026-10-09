-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RepeatedRootSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RepeatedRootSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:02:24.944983+00:00
-- url     : https://prove2.me/theorems/cd12447d-2080-4c17-93d4-3f7bba567862
-- title:
--   FLT.Assumptions.MazurProof.N13RepeatedRootSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RepeatedRootSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RepeatedRootSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AllPointAffineSpread_p0

set_option autoImplicit false




/-!
# Integral spreads of repeated-root N13 graphs

A repeated horizontal root is a tangent divisor, not a degenerate case
requiring enumeration.  Smoothness forces the ordinate at that root to be
nonzero.  The tangent graph ideal is then exactly the square of the point
graph ideal, and the existing valuation-independent point spread can be
tensor-squared.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13RepeatedRootSpread

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K]

/-- At a repeated horizontal root of a Mumford graph on a smooth sextic,
the ordinate cannot vanish.  Otherwise the repeated linear factor divides
both `v²` and `f - v²`, hence its square divides the squarefree sextic. -/
theorem mumford_eval_ne_zero_of_square
    (M : SexticMumford.Model K)
    (D : SexticMumford.Mumford M)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    D.v.eval a ≠ 0 := by
  intro hz
  let p : K[X] := X - C a
  have hvdiv : p ∣ D.v := by
    have h :=
      X_sub_C_dvd_sub_C_eval (p := D.v) (a := a)
    simpa [p, hz] using h
  obtain ⟨s, hs⟩ := hvdiv
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hpSquareDvd : p ^ 2 ∣ M.f := by
    refine ⟨w + s ^ 2, ?_⟩
    calc
      M.f = (M.f - D.v ^ 2) + D.v ^ 2 := by ring
      _ = D.u * w + D.v ^ 2 := by rw [hw]
      _ = p ^ 2 * w + (p * s) ^ 2 := by
        rw [hfactor, hs]
      _ = p ^ 2 * (w + s ^ 2) := by ring
  have hpUnit : IsUnit p :=
    M.squarefree p (by simpa only [pow_two] using hpSquareDvd)
  exact
    (Polynomial.not_isUnit_of_natDegree_pos p
      (by simp [p])) hpUnit

/-- A repeated-root Mumford graph is the square of its point graph ideal.
The proof is the local tangent identity: modulo the point ideal the second
factor `Y + v` is the nonzero scalar `2 v(a)`, so the graph generator lies
in the ideal square. -/
theorem pointIdeal_sq_eq_mumfordIdeal_of_square
    (M : SexticMumford.Model K)
    (D : SexticMumford.Mumford M)
    (a : K)
    (hfactor : D.u = (X - C a) ^ 2) :
    SexticMumford.mumfordIdeal M
          (X - C a) (C (D.v.eval a)) ^ 2 =
      SexticMumford.mumfordIdeal M D.u D.v := by
  let p : K[X] := X - C a
  let z : K := D.v.eval a
  let I : Ideal (SexticMumford.CoordinateRing M) :=
    SexticMumford.mumfordIdeal M p D.v
  let J : Ideal (SexticMumford.CoordinateRing M) :=
    SexticMumford.mumfordIdeal M (p ^ 2) D.v
  let g : SexticMumford.CoordinateRing M :=
    SexticMumford.ySubClass M D.v
  let plus : SexticMumford.CoordinateRing M :=
    SexticMumford.yClass M + SexticMumford.xClass M D.v
  have hz : z ≠ 0 := by
    exact mumford_eval_ne_zero_of_square M D a hfactor
  have hdiv : p ∣ D.v - C z := by
    simpa [p, z] using
      (X_sub_C_dvd_sub_C_eval (p := D.v) (a := a))
  have hgraph :
      SexticMumford.mumfordIdeal M p D.v =
        SexticMumford.mumfordIdeal M p (C z) := by
    simpa [SexticMumford.mumfordIdeal,
      GeneralizedGraphIdealCore.graphIdeal,
      SexticMumford.ySubClass,
      GeneralizedGraphIdealCore.ySubClass,
      SexticMumford.xClassHom_apply] using
      (GeneralizedGraphIdealCore.graphIdeal_eq_of_dvd_sub
        (SexticMumford.xClassHom M)
        (SexticMumford.yClass M)
        p (C z) D.v hdiv)
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcurve : M.f - D.v ^ 2 = p ^ 2 * w := by
    rw [hfactor] at hw
    exact hw
  have hpI : SexticMumford.xClass M p ∈ I := by
    exact SexticMumford.xClass_mem_mumfordIdeal M p D.v
  have hgI : g ∈ I := by
    change g ∈ SexticMumford.mumfordIdeal M p D.v
    exact Ideal.subset_span (by simp [g])
  have hp2I :
      SexticMumford.xClass M (p ^ 2) ∈ I ^ 2 := by
    rw [SexticMumford.xClass_pow]
    simpa only [pow_two] using
      (Ideal.mul_mem_mul hpI hpI)
  have hggI : g * g ∈ I ^ 2 := by
    simpa only [pow_two] using
      (Ideal.mul_mem_mul hgI hgI)
  have hproduct :
      g * plus =
        SexticMumford.xClass M (p ^ 2) *
          SexticMumford.xClass M w := by
    calc
      g * plus =
          SexticMumford.yClass M ^ 2 -
            SexticMumford.xClass M D.v ^ 2 := by
        simp only [g, plus, SexticMumford.ySubClass]
        ring
      _ = SexticMumford.xClass M M.f -
            SexticMumford.xClass M (D.v ^ 2) := by
        rw [SexticMumford.yClass_sq,
          SexticMumford.xClass_pow]
      _ = SexticMumford.xClass M (M.f - D.v ^ 2) := by
        rw [SexticMumford.xClass_sub]
      _ = SexticMumford.xClass M (p ^ 2 * w) := by
        rw [hcurve]
      _ = SexticMumford.xClass M (p ^ 2) *
            SexticMumford.xClass M w := by
        rw [SexticMumford.xClass_mul]
  have hplusgI : plus * g ∈ I ^ 2 := by
    rw [mul_comm, hproduct]
    exact Ideal.mul_mem_right
      (SexticMumford.xClass M w) _ hp2I
  obtain ⟨s, hs⟩ := hdiv
  have hpgI :
      SexticMumford.xClass M p * g ∈ I ^ 2 := by
    simpa only [pow_two] using
      (Ideal.mul_mem_mul hpI hgI)
  have hdeltaG :
      SexticMumford.xClass M (D.v - C z) * g ∈ I ^ 2 := by
    rw [hs, SexticMumford.xClass_mul]
    convert
      Ideal.mul_mem_left (I ^ 2)
        (SexticMumford.xClass M s) hpgI using 1
    all_goals ring
  have htwo :
      2 * SexticMumford.xClass M (C z) =
        SexticMumford.xClass M (C (2 * z)) := by
    calc
      2 * SexticMumford.xClass M (C z) =
          SexticMumford.xClass M (C z) +
            SexticMumford.xClass M (C z) := by ring
      _ = SexticMumford.xClass M (C z + C z) := by
        rw [SexticMumford.xClass_add]
      _ = SexticMumford.xClass M (C (2 * z)) := by
        congr 1
        simp [two_mul]
  have htwoz : 2 * z ≠ 0 :=
    mul_ne_zero M.two_ne_zero hz
  have hscale :
      SexticMumford.xClass M (C ((2 * z)⁻¹)) *
          (2 * SexticMumford.xClass M (C z)) = 1 := by
    rw [htwo, ← SexticMumford.xClass_mul, ← C_mul,
      inv_mul_cancel₀ htwoz, C_1, SexticMumford.xClass_one]
  have hgSq : g ∈ I ^ 2 := by
    have h₁ :=
      Ideal.mul_mem_left (I ^ 2)
        (SexticMumford.xClass M (C ((2 * z)⁻¹)))
        hplusgI
    have h₂ :=
      Ideal.mul_mem_left (I ^ 2)
        (SexticMumford.xClass M (C ((2 * z)⁻¹)))
        hggI
    have h₃ :=
      Ideal.mul_mem_left (I ^ 2)
        (2 * SexticMumford.xClass M (C ((2 * z)⁻¹)))
        hdeltaG
    have hmem :=
      Ideal.sub_mem (I ^ 2)
        (Ideal.sub_mem (I ^ 2) h₁ h₂) h₃
    have heq :
        SexticMumford.xClass M (C ((2 * z)⁻¹)) *
              (plus * g) -
            SexticMumford.xClass M (C ((2 * z)⁻¹)) *
              (g * g) -
            (2 * SexticMumford.xClass M (C ((2 * z)⁻¹))) *
              (SexticMumford.xClass M (D.v - C z) * g) =
          g := by
      calc
        _ =
            (SexticMumford.xClass M (C ((2 * z)⁻¹)) *
              (2 * SexticMumford.xClass M (C z))) * g := by
                simp only [plus, g, SexticMumford.ySubClass,
                  SexticMumford.xClass_sub]
                ring
        _ = g := by rw [hscale, one_mul]
    rw [heq] at hmem
    exact hmem
  have hIJ : I ^ 2 = J := by
    apply le_antisymm
    · change
        SexticMumford.mumfordIdeal M p D.v ^ 2 ≤ J
      rw [pow_two, SexticMumford.mumfordIdeal,
        Ideal.span_pair_mul_span_pair]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hxJ : SexticMumford.xClass M (p ^ 2) ∈ J := by
        exact SexticMumford.xClass_mem_mumfordIdeal M (p ^ 2) D.v
      have hgJ : g ∈ J := by
        change g ∈ SexticMumford.mumfordIdeal M (p ^ 2) D.v
        exact Ideal.subset_span (by simp [g])
      rcases ht with rfl | rfl | rfl | rfl
      · change
          SexticMumford.xClass M p *
              SexticMumford.xClass M p ∈ J
        rw [← SexticMumford.xClass_mul, ← pow_two]
        exact hxJ
      · exact Ideal.mul_mem_left J (SexticMumford.xClass M p) hgJ
      · exact Ideal.mul_mem_right (SexticMumford.xClass M p) J hgJ
      · exact Ideal.mul_mem_left J g hgJ
    · change
        SexticMumford.mumfordIdeal M (p ^ 2) D.v ≤ I ^ 2
      rw [SexticMumford.mumfordIdeal]
      apply Ideal.span_le.mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hp2I
      · exact hgSq
  calc
    SexticMumford.mumfordIdeal M p (C z) ^ 2 =
        I ^ 2 := by
          change
            SexticMumford.mumfordIdeal M p (C z) ^ 2 =
              SexticMumford.mumfordIdeal M p D.v ^ 2
          rw [hgraph]
    _ = J := hIJ
    _ = SexticMumford.mumfordIdeal M D.u D.v := by
      change
        SexticMumford.mumfordIdeal M (p ^ 2) D.v =
          SexticMumford.mumfordIdeal M D.u D.v
      rw [hfactor]

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  N13AllPointAffineSpread.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13AllPointAffineSpread.Model

abbrev IntegralRing : Type :=
  N13AllPointAffineSpread.IntegralRing

abbrev IntegralFractionalIdeal : Type :=
  N13AllPointAffineSpread.IntegralFractionalIdeal

abbrev G : Type :=
  N13ConstructedHalfIntegralSpread.G

/-- Every balanced quadratic graph with one repeated two-adic root has an
invertible integral affine spread.  It is the tensor square of the
valuation-independent point spread at the corresponding tangent point. -/
theorem mumfordGraph_has_affineSpread_of_repeated_root
    (D : SexticMumford.Mumford Model)
    (x : Q₂)
    (hfactor : D.u = (X - C x) ^ 2) :
    ∃ J : Ideal IntegralRing,
      IsUnit (J : IntegralFractionalIdeal) ∧
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic J =
          SexticMumford.mumfordIdeal Model D.u D.v := by
  have hfactorMul :
      D.u = (X - C x) * (X - C x) := by
    simpa only [pow_two] using hfactor
  obtain ⟨hsextic, _⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x x hfactorMul
  let y :=
    N13TwoChartLineTensor.goodY x (D.v.eval x)
  have hcurve :
      N13GoodModelTwo.AffineEquation x y :=
    N13TwoChartLineTensor.goodY_onCurve
      x (D.v.eval x) hsextic
  let J :=
    N13AllPointAffineSpread.pairIdeal
      x y x y hcurve hcurve
  refine
    ⟨J,
      N13AllPointAffineSpread.pairIdeal_isUnit
        x y x y hcurve hcurve,
      ?_⟩
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13AllPointAffineSpread.pairIdeal
          x y x y hcurve hcurve) =
      SexticMumford.mumfordIdeal Model D.u D.v
  rw [N13AllPointAffineSpread.pairIdeal, Ideal.map_mul,
    (N13AllPointAffineSpread.pointSpread x y hcurve).map_ideal,
    N13TwoChartLineTensor.pointY_goodY,
    ← pow_two,
    pointIdeal_sq_eq_mumfordIdeal_of_square
      Model D x hfactor]

/-- Every selected quadratic graph with one repeated rational root has an
invertible integral affine spread.  It is the tensor square of the
valuation-independent point spread at the corresponding tangent point. -/
theorem selectedGraph_has_affineSpread_of_repeated_root
    (P : G)
    (x : ℚ)
    (hfactor :
      (N13ConstructedHalfIntegralSpread.normalizedGraphMumford P).u =
        (X - C x) ^ 2) :
    ∃ J : Ideal IntegralRing,
      IsUnit (J : IntegralFractionalIdeal) ∧
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic J =
          SexticMumford.mumfordIdeal Model
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).u
            (N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford
              P).v := by
  let D :=
    N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford P
  let x₂ : Q₂ :=
    N13ProperCurveReduction.ratToQ₂ x
  have hfactor₂ :
      D.u = (X - C x₂) ^ 2 := by
    have hmap :=
      congrArg
        (Polynomial.map N13InfinityBaseChange.ratToQ₂)
        hfactor
    simpa [D, x₂,
      N13ConstructedHalfIntegralSpread.twoAdicNormalizedGraphMumford]
      using hmap
  simpa [D] using
    (mumfordGraph_has_affineSpread_of_repeated_root
      D x₂ hfactor₂)

end

end MazurProof.N13RepeatedRootSpread


