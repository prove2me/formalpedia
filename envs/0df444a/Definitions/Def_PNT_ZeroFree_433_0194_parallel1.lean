-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0194_parallel1
-- name    : PNT_ZeroFree_433_0194_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:25:52.934981+00:00
-- url     : https://prove2.me/theorems/4e34c335-0194-4f68-96da-9c6fcfb5490f
-- title:
--   Zero-free region foundations: MeanSquare.UnitRows [0194_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/UnitRows.lean#L83-L498

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0184_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/UnitRows.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CanonicalRowCompletion
local instance p2mAnonymous_PNT_ZeroFree_433_0194_parallel1_1 : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def unitRowFamily (Ψ : ActualEisensteinCubic.O→*ℂ) (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ}
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) : ActualEisensteinCubic.O→*ℂ :=
  rowTwist Ψ mask (idealGenerator f.val) (u.val*idealGenerator I)

lemma unitRowFamily_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ} (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) (x : ActualEisensteinCubic.O) :
    ‖unitRowFamily Ψ mask u f I x‖≤1 := rowTwist_norm Ψ hΨ _ _ _ _

lemma rowTwist_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (mask f z : ActualEisensteinCubic.O) (θ : ℝ) :
    rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ) mask f z =
      SecondPassArithmetic.normHeightTwist (rowTwist Ψ mask f z) θ := by
  unfold rowTwist
  exact (SecondPassArithmetic.normHeightTwist_mul Ψ _ θ).symm


end CompletedUnitRows

open scoped BigOperators Classical
namespace SecondPassArithmetic


open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem nonzeroRowFamily_le_center (labels : Finset (Ideal ActualEisensteinCubic.O))
    (P : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) (K scale B : ℝ) (zero tail : ℂ)
    (hK : 0<K) (hscale : 0<scale)
    (hcenter : ‖(scale:ℂ)⁻¹*((∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
      (‖P I z‖^2:ℝ))-zero-tail)‖≤B) :
    (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤
      ‖zero‖+‖tail‖+scale*B := by
  let total : ℂ := ∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)
  have hnonzero : (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤total.re := by
    simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
      Complex.re_sum,Complex.ofReal_re]
    change (∑I∈labels,(∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)).re)-
      ∑I∈labels,‖P I 0‖^2≤_
    have hz : 0≤∑I∈labels,‖P I 0‖^2 := Finset.sum_nonneg (fun I hI=>sq_nonneg _)
    dsimp only [total]
    rw [Complex.re_sum]
    linarith
  have hc : ‖total-zero-tail‖≤scale*B := by
    calc
      _ = scale*‖(scale:ℂ)⁻¹*(total-zero-tail)‖ := by
        rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcenter hscale.le
  apply hnonzero.trans
  calc
    total.re ≤ ‖total‖ := Complex.re_le_norm _
    _ = ‖(total-zero-tail)+zero+tail‖ := by congr 1; ring
    _ ≤ ‖total-zero-tail‖+‖zero‖+‖tail‖ := norm_add₃_le
    _ ≤ _ := by linarith


end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

lemma euclideanAxisPath_affine (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self (p : EuclideanSpatial) (j : Fin 3) :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.comp
        (euclideanAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr (f g : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

end CubicEisenstein


end

end OAI

end


