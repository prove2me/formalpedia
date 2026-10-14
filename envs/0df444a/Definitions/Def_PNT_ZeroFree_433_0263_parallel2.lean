-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0263_parallel2
-- name    : PNT_ZeroFree_433_0263_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:21.006099+00:00
-- url     : https://prove2.me/theorems/322fb529-cbf6-4624-b164-ffec3455d389
-- title:
--   Zero-free region foundations: GaussSum.BesselReflection [0263_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.BesselReflection
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/BesselReflection.lean#L84-L659

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0231_parallel1
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1
import Definitions.Def_PNT_ZeroFree_433_0262
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/BesselReflection.lean
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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology

section
open CubicEisenstein

def completedBesselProfile (Ψ : ActualEisensteinCubic.O→*ℂ) (q : ℝ) : ℝ→ℂ :=
  radialBesselProfile completedMellinLength (completedMellinCoefficient Ψ) q


theorem completedBesselProfile_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    mellin (completedBesselProfile Ψ q) (2*s)=
      besselMellinFactor q s*completedDirichletSeries Ψ s := by
  let : Countable ActualEisensteinCubic.O :=
    ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) :=
    ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hsum := completedMellinCoefficient_summable Ψ hΨ (s.re-1/2) (by linarith)
  have he : -(s.re-1/2)=1/2-s.re := by ring
  simp only [he] at hsum
  exact radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) q hq s (by linarith) hsum


theorem completedDirichletSeries_eq_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    completedDirichletSeries Ψ s=
      inverseBesselMellinFactor q s*mellin (completedBesselProfile Ψ q) (2*s) := by
  rw [completedBesselProfile_mellin Ψ hΨ q hq s hs,←mul_assoc,
    inverseBesselMellinFactor_mul q hq s (by linarith),one_mul]

end


theorem continuedBesselDirichlet_eq_initial (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    continuedBesselDirichlet (completedBesselProfile Ψ q) q s=
      completedDirichletSeries Ψ s :=
  (completedDirichletSeries_eq_mellin Ψ hΨ q hq s hs).symm

end CompletedGauss


open scoped BigOperators Classical

namespace CompletedGauss

section
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


theorem primary_squarefree_cube_eq_iff {I J I' J':Ideal Eis}
    (hI:Squarefree I) (hI':Squarefree I')
    (hgI:primaryGenerator I≠0) (hgJ:primaryGenerator J≠0)
    (hgI':primaryGenerator I'≠0) (hgJ':primaryGenerator J'≠0) :
    primaryGenerator I*(primaryGenerator J)^3=
      primaryGenerator I'*(primaryGenerator J')^3 ↔ I=I' ∧ J=J' := by
  constructor
  · intro h
    have hleft:primaryGenerator (I*J^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI (pow_ne_zero _ hgJ)
    have hright:primaryGenerator (I'*J'^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI' (pow_ne_zero _ hgJ')
    have he:I*J^3=I'*J'^3:=by
      calc
        I*J^3=Ideal.span {primaryGenerator (I*J^3)}:=(primaryGenerator_spec _ hleft).1.symm
        _=Ideal.span {primaryGenerator (I'*J'^3)}:=by
          apply congrArg (fun z:Eis => (Ideal.span {z}:Ideal Eis))
          simpa only [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow] using h
        _=I'*J'^3:=(primaryGenerator_spec _ hright).1
    exact squarefree_cube_decomposition_unique
      (primaryGenerator_ne_zero_ideal J hgJ) (primaryGenerator_ne_zero_ideal J' hgJ') hI hI' he
  · rintro ⟨rfl,rfl⟩
    rfl

theorem primary_squarefree_cube_injective :
    Function.Injective (fun x:
      {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0} =>
        primaryGenerator x.1.val*(primaryGenerator x.2.val)^3) := by
  intro x y he
  have h:= (primary_squarefree_cube_eq_iff x.1.property.1 y.1.property.1
    x.1.property.2 x.2.property y.1.property.2 y.2.property).mp he
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff


theorem completedT_mellin_shift (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe : Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) (lo : ℝ) (hl : lo≤2)
    (hleft : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I))) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I) := by
  have hid (t : ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)=
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
    rw [besselSmoothingIntegrand,continuedBesselDirichlet_eq_initial Ψ hΨ q hq _ (by norm_num)]
    rw [show (2:ℂ)+t*Complex.I-1/2=3/2+t*Complex.I by ring]
  have hr : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)) := by
    simp only [hid]
    exact completedT_initial_mellin_integrable Ψ hΨ W a b ha hWs hW X hX
  have he := besselSmoothingIntegrand_contour_eq (completedBesselProfile Ψ q) q hq hF hFe
    (Vstar W) a b ha (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW)
    X hX lo 2 hl hleft hr
  rw [he]
  simpa only [Complex.ofReal_ofNat,hid] using
    completedT_initial_mellin Ψ hΨ W a b ha hWs hW X hX

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss
open CubicEisenstein


theorem continuedBesselDirichlet_reflection {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (s : ℂ) (hs : s.re<4/3)
    (ha : Summable (fun i=>‖a i‖*(r i)^(s.re-1/2))) :
    continuedBesselDirichlet F q s=
      (A*(Q:ℂ)^(2-2*s)*besselReflectionFactor q d s)*
        CubicReflectionKernel.gammaMultiplier (1/2-s)*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by
  have hs' : -(1/3)<(1-s).re := by simp;linarith
  have ha' : Summable (fun i=>‖a i‖*(r i)^(1/2-(1-s).re)) := by
    convert! ha using 1
    funext i
    congr 2
    simp
    ring
  have hm := radialBesselProfile_mellin r hr a d hd (1-s) hs' ha'
  have hc := cusp_mellin_reflection_of_identity F (radialBesselProfile r a d) A s Q hQ hreflect
  have hm' : mellin (radialBesselProfile r a d) (2-2*s)=
      besselMellinFactor d (1-s)*(∑'i,a i*(r i:ℂ)^(s-1/2)) := by
    calc
      _=mellin (radialBesselProfile r a d) (2*(1-s)) := by congr 1;ring
      _=_ := by simpa only [besselMellinFactor,show (1/2:ℂ)-(1-s)=s-1/2 by ring] using hm
  rw [hm'] at hc
  rw [continuedBesselDirichlet,hc]
  calc
    _=A*(Q:ℂ)^(2-2*s)*(inverseBesselMellinFactor q s*besselMellinFactor d (1-s))*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by ring
    _=_ := by rw [besselMellinFactor_reflection];ring

end CompletedGauss

end

end OAI

end


