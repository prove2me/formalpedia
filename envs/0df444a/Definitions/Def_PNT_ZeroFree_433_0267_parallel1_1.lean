-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0267_parallel1_1
-- name    : PNT_ZeroFree_433_0267_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:35:19.077021+00:00
-- url     : https://prove2.me/theorems/c5e679eb-bfe0-4be0-8bb7-da0d6551b0a7
-- title:
--   Zero-free region foundations: Eisenstein.EntireMellinProfile [0267_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/EntireMellinProfile.lean#L84-L214

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0258_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/EntireMellinProfile.lean
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
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_mellin_entire {ι : Type*} [Fintype ι] (f : ι→ℝ→ℂ) (weight : ι→ℂ)
    (hf : ∀i,(∀s:ℂ,MellinConvergent (f i) s) ∧ Differentiable ℂ (mellin (f i))) :
    (∀s:ℂ,MellinConvergent (fun v=>∑i,weight i*f i v) s) ∧
      Differentiable ℂ (mellin (fun v=>∑i,weight i*f i v)) := by
  have hs (s : ℂ) (i : ι) : MellinConvergent (fun v=>weight i*f i v) s := by
    simpa only [smul_eq_mul] using (hf i).1 s |>.const_smul (weight i)
  have hsi (s : ℂ) (i : ι) : IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(weight i*f i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using hs s i
  have he (s : ℂ) : mellin (fun v=>∑i,weight i*f i v) s=∑i,weight i*mellin (f i) s := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i hi=>hsi s i)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (f i) s (weight i)
  constructor
  · intro s
    change IntegrableOn (fun v:ℝ=>(v:ℂ)^(s-1)*(∑i,weight i*f i v)) (Set.Ioi 0)
    simpa only [IntegrableOn,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun i hi=>hsi s i)
  · rw [show mellin (fun v=>∑i,weight i*f i v)=(fun s=>∑i,weight i*mellin (f i) s) from funext he]
    exact Differentiable.fun_sum (fun i hi=>(hf i).2.const_mul (weight i))


end CubicEisenstein

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma mellin_eq_of_positive_eq (F G : ℝ→ℂ) (hFG : ∀v : ℝ,0<v→F v=G v) (s : ℂ) :
    mellin F s=mellin G s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hFG v hv]

lemma continuedBesselDirichlet_finite_sum {ι : Type*} [Fintype ι]
    (F : ι→ℝ→ℂ) (w : ι→ℂ) (q : ℝ) (s : ℂ)
    (hF : ∀i,MellinConvergent (F i) (2*s)) :
    continuedBesselDirichlet (fun v=>∑i,w i*F i v) q s=
      ∑i,w i*continuedBesselDirichlet (F i) q s := by
  have hi (i : ι) : IntegrableOn (fun v : ℝ=>(v:ℂ)^(2*s-1)*(w i*F i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using (hF i).const_smul (w i)
  have hm : mellin (fun v=>∑i,w i*F i v) (2*s)=∑i,w i*mellin (F i) (2*s) := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (F i) (2*s) (w i)
  rw [continuedBesselDirichlet,hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold continuedBesselDirichlet
  ring

lemma besselSmoothingIntegrand_finite_sum {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ)
    (hG : ∀i,MellinConvergent (G i) (2*s)) :
    besselSmoothingIntegrand F q V X s=
      ∑i,w i*besselSmoothingIntegrand (G i) q V X s := by
  have hm := mellin_eq_of_positive_eq F (fun v=>∑i,w i*G i v) hFG (2*s)
  have hd : continuedBesselDirichlet F q s=
      continuedBesselDirichlet (fun v=>∑i,w i*G i v) q s := by
    simp only [continuedBesselDirichlet,hm]
  rw [besselSmoothingIntegrand,hd,continuedBesselDirichlet_finite_sum G w q s hG,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold besselSmoothingIntegrand
  ring


end CompletedGauss


end

end OAI

end


