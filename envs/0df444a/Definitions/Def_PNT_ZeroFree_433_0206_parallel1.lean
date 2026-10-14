-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0206_parallel1
-- name    : PNT_ZeroFree_433_0206_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:01:43.288753+00:00
-- url     : https://prove2.me/theorems/5c6a4a42-7ba3-43cf-8dca-5d4bfd4154ba
-- title:
--   Zero-free region foundations: Eisenstein.SeedHeight [0206_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SeedHeight.lean#L269-L499

import Definitions.Def_PNT_ZeroFree_433_0034
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SeedHeight.lean
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

namespace CubicEisenstein


section
open Filter
open scoped BigOperators Classical Topology ContDiff

section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)

lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _

end PartialDerivatives
section

variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  apply contDiff_tsum (v := fun k i => ‖b i‖*C k) hprod
  · intro k hk
    exact hb.mul_right (C k)
  · intro k i x hk
    have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
        b i • iteratedFDeriv ℝ k (F (a i)) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := b i) (i := k) (x := x)
          ((hf i).contDiffAt.of_le (by first | simp | exact_mod_cast le_top)))
    rw [he,norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)

end

lemma rowEnergy_real_smul (r : ℝ) (u : Fin 2→ℂ) :
    rowEnergy (r • u)=r^2*rowEnergy u := by
  simp only [rowEnergy,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

def normalizedComplexRow (u : Fin 2→ℂ) : Fin 2→ℂ := (Real.sqrt (rowEnergy u))⁻¹ • u

lemma normalizedComplexRow_energy (u : Fin 2→ℂ) (hu : u≠0) :
    rowEnergy (normalizedComplexRow u)=1 := by
  rw [normalizedComplexRow,rowEnergy_real_smul,inv_pow,
    Real.sq_sqrt (rowEnergy_nonneg u),inv_mul_cancel₀ (rowEnergy_pos u hu).ne']

lemma rowEnergy_continuous : Continuous rowEnergy := by
  unfold rowEnergy
  fun_prop

lemma rowEnergy_unit_isCompact : IsCompact {u : Fin 2→ℂ | rowEnergy u=1} := by
  apply (isCompact_closedBall (0 : Fin 2→ℂ) 1).of_isClosed_subset
    (isClosed_eq rowEnergy_continuous continuous_const)
  intro u hu
  change rowEnergy u=1 at hu
  rw [Metric.mem_closedBall,dist_zero_right]
  simpa only [hu,Real.sqrt_one] using norm_le_sqrt_rowEnergy u

lemma rowEnergy_unit_ne_zero (u : Fin 2→ℂ) (hu : rowEnergy u=1) : u≠0 := by
  intro h
  simp [h,rowEnergy] at hu

def regularSpatialHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : ℝ :=
  deltaLoss*ConcreteCompactWeight.positiveExtension (p 2/deltaLoss)

lemma regularSpatialHeight_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) :
    0<regularSpatialHeight deltaLoss p :=
  mul_pos hδ (ConcreteCompactWeight.positiveExtension_pos _)

lemma regularSpatialHeight_contDiff (deltaLoss : ℝ) : ContDiff ℝ ∞ (regularSpatialHeight deltaLoss) := by
  unfold regularSpatialHeight
  exact contDiff_const.mul (ConcreteCompactWeight.positiveExtension_smooth.comp
    ((contDiff_apply ℝ ℝ 2).div_const deltaLoss))

lemma regularSpatialHeight_eq (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularSpatialHeight deltaLoss p=p 2 := by
  rw [regularSpatialHeight,ConcreteCompactWeight.positiveExtension_eq _ ((le_div_iff₀ hδ).mpr (by simpa using hp))]
  field_simp

def regularRowKernel (s : ℂ) (deltaLoss : ℝ) (u : Fin 2→ℂ) (p : SpatialCoordinates) : ℂ :=
  logRatioPower s (regularSpatialHeight deltaLoss p)
    (heightDenominator (spatialHorizontal p) (regularSpatialHeight deltaLoss p) u)

lemma regularRowDenominator_contDiff (deltaLoss : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates =>
      heightDenominator (spatialHorizontal p.2) (regularSpatialHeight deltaLoss p.2) p.1) := by
  have hc (j : Fin 2) : ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates => p.1 j) :=
    (contDiff_apply ℝ ℂ j).comp contDiff_fst
  have hz := spatialHorizontal_contDiff.comp (contDiff_snd (E := Fin 2→ℂ))
  have hv := (regularSpatialHeight_contDiff deltaLoss).comp (contDiff_snd (E := Fin 2→ℂ))
  have hw := ((hc 0).mul hz).add (hc 1)
  simp only [heightDenominator,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  exact (((Complex.reCLM.contDiff.comp hw).mul (Complex.reCLM.contDiff.comp hw)).add
    ((Complex.imCLM.contDiff.comp hw).mul (Complex.imCLM.contDiff.comp hw))).add
    ((((Complex.reCLM.contDiff.comp (hc 0)).mul (Complex.reCLM.contDiff.comp (hc 0))).add
      ((Complex.imCLM.contDiff.comp (hc 0)).mul (Complex.imCLM.contDiff.comp (hc 0)))).mul (hv.pow 2))

lemma regularRowKernel_contDiffAt (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) :
    ContDiffAt ℝ ∞ (Function.uncurry (regularRowKernel s deltaLoss)) (u,p) := by
  have hv : ContDiff ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => regularSpatialHeight deltaLoss q.2) :=
    (regularSpatialHeight_contDiff deltaLoss).comp contDiff_snd
  have hD := (regularRowDenominator_contDiff deltaLoss).contDiffAt (x := (u,p))
  have hv0 := regularSpatialHeight_pos deltaLoss hδ p
  have hD0 := heightDenominator_pos (spatialHorizontal p) (regularSpatialHeight deltaLoss p) hv0 u hu
  have hl := (hv.contDiffAt.log hv0.ne').sub (hD.log hD0.ne')
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (u,p) hl)).cexp

lemma heightDenominator_real_smul (z : ℂ) (v r : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (r•u)=r^2*heightDenominator z v u := by
  unfold heightDenominator
  have he : (r•u) 0*z+(r•u) 1=r•(u 0*z+u 1) := by
    simp only [Pi.smul_apply,smul_add,smul_mul_assoc]
  rw [he]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma heightDenominator_normalized (z : ℂ) (v : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (normalizedComplexRow u)=heightDenominator z v u/rowEnergy u := by
  rw [normalizedComplexRow,heightDenominator_real_smul,inv_pow,Real.sq_sqrt (rowEnergy_nonneg u)]
  ring

lemma regularRowKernel_eq (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (u : Fin 2→ℂ)
    (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularRowKernel s deltaLoss u p=rowSmoothPower s u p := by
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp]
  unfold rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  rfl

lemma normalized_row_summand (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    summand 1 s r*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p=
      smoothSummand s r p := by
  have hu := embeddedRow_ne_zero r
  have hE := rowEnergy_pos _ hu
  have hv : 0<p 2 := hδ.trans_le hp
  have hD := heightDenominator_pos (spatialHorizontal p) (p 2) hv (embeddedRow r) hu
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp,heightDenominator_normalized]
  rw [summand,rowOperator_one,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hE.ne'),
    ←Complex.ofReal_log hE.le]
  unfold smoothSummand rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  unfold logRatioPower
  rw [Real.log_div hD.ne' hE.ne',mul_assoc,←Complex.exp_add]
  congr 2
  unfold spatialHorizontal
  push_cast
  ring

theorem regular_eisenstein_compact_smooth (s : ℂ) (hs : 2<s.re)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ψ : SpatialCoordinates→ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p => ∑'r : CuspCosets,
      summand 1 s r*(ψ p*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p)) := by
  apply compact_smooth_family_tsum (fun u p => ψ p*regularRowKernel s deltaLoss u p)
    {u : Fin 2→ℂ | rowEnergy u=1} (tsupport ψ) rowEnergy_unit_isCompact hcψ
  · intro u hu p
    have hψp : ContDiffAt ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => ψ q.2) (u,p) :=
      hψ.contDiffAt.comp (u,p) contDiffAt_snd
    exact hψp.mul (regularRowKernel_contDiffAt s deltaLoss hδ u (rowEnergy_unit_ne_zero u hu) p)
  · intro u hu
    exact tsupport_mul_subset_left
  · intro r
    exact normalizedComplexRow_energy _ (embeddedRow_ne_zero r)
  · exact summable_norm_summand 1 s hs

theorem smoothEisenstein_contDiffAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (smoothEisenstein s) p := by
  let deltaLoss : ℝ:=p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates→ℂ:=fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  have hsum := regular_eisenstein_compact_smooth s hs deltaLoss hδ ψ hψ hcψ
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq
  unfold smoothEisenstein
  apply tsum_congr
  intro r
  have hψq : ψ q=1 := by simp [ψ,hχ]
  rw [hψq,one_mul]
  exact (normalized_row_summand s deltaLoss hδ r q hq.le).symm

end


end CubicEisenstein


end

end OAI

end


