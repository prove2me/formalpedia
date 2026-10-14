-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
-- name    : PNT_ZeroFree_433_0265_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:27:30.730419+00:00
-- url     : https://prove2.me/theorems/6b6a0776-10d0-4316-91bc-95d469f38efa
-- title:
--   Zero-free region foundations: GaussSum.MellinSupport [0265_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MellinSupport.lean#L81-L317

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/MellinSupport.lean
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

open scoped BigOperators Classical

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

lemma completedMellinCoefficient_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:completedMellinCoefficient Ψ p≠0) :
    Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0 := by
  have hleft:Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 := by
    by_contra hh
    apply hp
    simp only [completedMellinCoefficient,columnWeight,squarefreeGaussCoefficient,
      dif_neg hh,zero_mul,zero_div]
  refine ⟨hleft.1,hleft.2,?_⟩
  intro hright
  apply hp
  rw [completedMellinCoefficient,cubeWeight_zero_of_primaryGenerator_zero Ψ _ hright,mul_zero]

lemma completedMellinCoefficient_zero_off_support (Ψ:Eis→*ℂ) (p:CompletedMellinIndex)
    (hp:¬(Squarefree p.1.val ∧ primaryGenerator p.1.val≠0 ∧ primaryGenerator p.2.val≠0)) :
    completedMellinCoefficient Ψ p=0 := by
  by_contra hn
  exact hp (completedMellinCoefficient_support Ψ p hn)

def primaryCubePairToMellinIndex
    (p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0})) : CompletedMellinIndex :=
  (⟨p.1.val,p.1.property.1.ne_zero⟩,
    ⟨p.2.val,primaryGenerator_ne_zero_ideal p.2.val p.2.property⟩)

lemma primaryCubePairToMellinIndex_injective : Function.Injective primaryCubePairToMellinIndex := by
  intro p q hpq
  exact Prod.ext
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.1.val) hpq))
    (Subtype.ext (congrArg (fun x:CompletedMellinIndex=>x.2.val) hpq))

theorem completedMellinCoefficient_tsum_primary_pairs (Ψ:Eis→*ℂ)
    (w:CompletedMellinIndex→ℂ) :
    (∑'p:CompletedMellinIndex,completedMellinCoefficient Ψ p*w p)=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        completedMellinCoefficient Ψ (primaryCubePairToMellinIndex p)*
          w (primaryCubePairToMellinIndex p) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p=>primaryCubePairToMellinIndex p.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro p hp
    change completedMellinCoefficient Ψ p*w p≠0 at hp
    have hc:completedMellinCoefficient Ψ p≠0 := by
      intro hz
      exact hp (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=completedMellinCoefficient_support Ψ p hc
    let q:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}):=(⟨p.1.val,hs,hI⟩,⟨p.2.val,hJ⟩)
    have hq:primaryCubePairToMellinIndex q=p := by
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨q,?_⟩,hq⟩
    change completedMellinCoefficient Ψ (primaryCubePairToMellinIndex q)*
      w (primaryCubePairToMellinIndex q)≠0
    simpa only [hq] using hp
  · intro p
    rfl


end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups


open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_triangular_right_cusp_ratio (g T:SL(2,ℂ)) (hT:T 1 0=0)
    (hc:(g*T) 1 0≠0) :
    g 1 0≠0 ∧ (g*T) 0 0/(g*T) 1 0=g 0 0/g 1 0 := by
  have hcol (i:Fin 2) : (g*T) i 0=g i 0*T 0 0 := by
    change (∑k:Fin 2,g i k*T k 0)=_
    rw [Fin.sum_univ_two,hT,mul_zero,add_zero]
  have hn:g 1 0*T 0 0≠0:=by rwa [hcol] at hc
  have hg: g 1 0≠0:=(mul_ne_zero_iff.mp hn).1
  have ht:T 0 0≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨hg,?_⟩
  rw [hcol,hcol]
  field_simp


lemma exists_integral_matrix_cusp_ratio (a c:Eis) (hc:c≠0) :
    ∃M:SL(2,Eis),M 1 0≠0 ∧
      eisEmbedding (M 0 0)/eisEmbedding (M 1 0)=eisEmbedding a/eisEmbedding c := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by
    intro hz
    exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by
    intro hz
    exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨u,v,huv⟩:=IsBezout.gcd_eq_sum a c
  change u*a+v*c=d at huv
  have hred:u*a'+v*c'=1:=by
    apply mul_left_cancel₀ hd
    calc
      d*(u*a'+v*c')=u*a+v*c:=by rw [ha,hc'];ring
      _=d:=huv
      _=d*1:=(mul_one d).symm
  let M:SL(2,Eis):=⟨!![a',-v;c',u],by
    rw [Matrix.det_fin_two_of]
    linear_combination hred⟩
  refine ⟨M,hcp,?_⟩
  change eisEmbedding a'/eisEmbedding c'=eisEmbedding a/eisEmbedding c
  rw [ha,hc',map_mul,map_mul]
  have hde:eisEmbedding d≠0:=eisEmbedding_ne_zero hd
  have hce:eisEmbedding c'≠0:=eisEmbedding_ne_zero hcp
  field_simp


end CubicEisenstein


end

end OAI

end


