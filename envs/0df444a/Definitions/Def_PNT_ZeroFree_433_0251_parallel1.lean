-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0251_parallel1
-- name    : PNT_ZeroFree_433_0251_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:32:32.475417+00:00
-- url     : https://prove2.me/theorems/93bd4f14-a821-4fe6-b89f-ca29175fc747
-- title:
--   Zero-free region foundations: Eisenstein.CorrespondencePullback [0251_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CorrespondencePullback
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondencePullback.lean#L178-L326

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondencePullback.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding


def coverEnergyDensity (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x=>(F x).re) p+
    euclideanScalarDirichletDensity (fun x=>(F x).im) p

def coverGradientAt (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j=>(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))

lemma coverEnergyDensity_nonneg (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    0≤coverEnergyDensity F p := by
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma coverGradientAt_norm_sq (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    ‖coverGradientAt F p‖^2=coverEnergyDensity F p := by
  have hr := (Complex.reCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x=>(F x).re) p=_ at hr
  change fderiv ℝ (fun x=>(F x).im) p=_ at hi
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑j:Fin 3,‖(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ‖fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2=
    (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).re^2+
      (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).im^2
  simpa only [Complex.normSq_apply,pow_two] using
    (Complex.normSq_eq_norm_sq (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))).symm


lemma coverGradientAt_sum {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverGradientAt (fun x=>∑i∈s,F i x) p=∑i∈s,coverGradientAt (F i) p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_fun_sum hF,_root_.sum_apply,
    WithLp.equiv_apply,Finset.mul_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma norm_sum_sq_le_card {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι→E) :
    ‖∑i∈s,f i‖^2≤(s.card:ℝ)*∑i∈s,‖f i‖^2 := by
  calc
    _ ≤ (∑i∈s,‖f i‖)^2 := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _=> (1:ℝ)) (fun i=>‖f i‖))

lemma coverEnergyDensity_sum_le {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x=>∑i∈s,F i x) p≤(s.card:ℝ)*∑i∈s,coverEnergyDensity (F i) p := by
  rw [←coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF),coverGradientAt_sum s F p hF]
  have hh := norm_sum_sq_le_card s (fun i=>coverGradientAt (F i) p)
  calc
    _ ≤ _ := hh
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)


end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_unipotent_upper (n:ℕ) :
    rationalEmbedding (ModularGroup.T^n)=unitCuspUpper (n:Eis) := by
  rw [←rationalUnipotent_nat]
  apply Subtype.ext
  change ( !![(1 : ℤ), (n : ℤ); 0, 1]).map (Int.castRingHom Eis) =
    !![1, (n : Eis); 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

lemma rational_cusp_lower_section (u:Eisˣ) (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
      integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv=
      integralComplexMatrix (unitCuspDiagonal (-u))*
        integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis))))*
          upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv := by
  have hm:=congrArg integralComplexMatrix (rational_cusp_lower_factor u (n:ℤ))
  simp only [map_mul,Int.cast_natCast] at hm
  have hu:integralComplexMatrix (unitCuspUpper (n:Eis))=rationalComplex (ModularGroup.T^n):=by
    rw [←rational_unipotent_upper]
    rfl
  rw [hu] at hm
  change rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
    integralComplexMatrix (lowerCuspMatrix (u:Eis))=_ at hm
  rw [hm,mul_assoc,unitCuspUpper_section]

lemma hyperbolicEisenstein_fixed_upper (g:SL(2,ℂ)) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    hyperbolicEisenstein s (g • upperPoint z v hv)=eisenstein (g*upperSection z v hv) s:=rfl

theorem sourceEisenstein_unit_lower (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        ∑n:Fin 3,eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n.val:Eis)*(u:Eis))))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_four_cusps]
  simp only [←mul_smul,hyperbolicEisenstein_fixed_upper]
  apply congrArg (fun c:ℂ=>(4:ℂ)⁻¹*(eisenstein
    (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+c))
  apply Finset.sum_congr rfl
  intro n hn
  rw [←mul_assoc,rational_cusp_lower_section]

theorem sourceEisenstein_primitive_lower_four (u t:Eisˣ)
    (hu:(u:Eis)^2+(u:Eis)+1=0)
    (ht:-(u:Eis)*(1+2*(u:Eis))=onceCuspScale t)
    (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)))*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_unit_lower,Fin.sum_univ_three]
  have h1:-(u:Eis)*(1+1*(u:Eis))=1:=by linear_combination -hu
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    zero_mul,add_zero,mul_one,h1,ht]
  ring


end


end CubicEisenstein

end

end OAI

end


