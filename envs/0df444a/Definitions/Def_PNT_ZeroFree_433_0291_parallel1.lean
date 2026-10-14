-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0291_parallel1
-- name    : PNT_ZeroFree_433_0291_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:29:03.746124+00:00
-- url     : https://prove2.me/theorems/e5433c61-528a-424c-bd13-a694e74b44e4
-- title:
--   Zero-free region foundations: RowCompletion.BranchDecoding [0291_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/BranchDecoding.lean#L89-L476

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0276_parallel1
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1
import Definitions.Def_PNT_ZeroFree_433_0286_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/BranchDecoding.lean
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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O


lemma canonicalLabel_squarefree {X:ℝ} (f:idealRange X) : Squarefree f.val :=
  (mem_idealRange.mp f.property).1.2.1

lemma canonicalLabel_generator_ne_zero {X:ℝ} (f:idealRange X) :
    ConcretePrimeRowBridge.idealGenerator f.val≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero f.val (mem_idealRange.mp f.property).1.1


end

theorem finite_selected_branch_collection
    {H U B:Type*} {R:H→Type*} {E:B→Type*}
    [Fintype H] [Fintype U] [Fintype B]
    [∀h,Fintype (R h)] [∀b,Fintype (E b)]
    (f:(h:H)→R h→U→(b:B)→E b→ℂ)
    (g:H→U→(b:B)→E b→ℂ)
    (chosen:(h:H)→B→R h) (α:H→ℂ) (shape:H→B→ℂ) (w:B→ℂ)
    (hbranch:∀h r u b e,4*f h r u b e=
      if r=chosen h b then α h*shape h b*g h u b e else 0) :
    4*(∑h,∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑h,α h*∑b,w b*shape h b*∑u,∑e:E b,g h u b e := by
  have hpoint (h:H) (b:B) :
      4*(∑r:R h,∑u,∑e:E b,f h r u b e)=
        α h*shape h b*(∑u,∑e:E b,g h u b e) := by
    simp_rw [Finset.mul_sum,hbranch]
    calc
      _=∑r:R h,if r=chosen h b then
          α h*shape h b*(∑u,∑e:E b,g h u b e) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases he:r=chosen h b
        · simp only [he,ite_true,Finset.mul_sum]
        · simp only [he,ite_false,Finset.sum_const_zero]
      _=_:=by simp [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hswap : (∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑b,w b*(∑r:R h,∑u,∑e:E b,f h r u b e) := by
    calc
      _=∑r:R h,∑b,∑u,w b*∑e:E b,f h r u b e := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _=∑b,∑r:R h,∑u,w b*∑e:E b,f h r u b e := Finset.sum_comm
      _=_:=by simp_rw [Finset.mul_sum]
  rw [hswap,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _=w b*(4*(∑r:R h,∑u,∑e:E b,f h r u b e)) := by ring
    _=w b*(α h*shape h b*(∑u,∑e:E b,g h u b e)) := by rw [hpoint]
    _=_:=by ring

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff


namespace CanonicalRowCompletion.ActualFiber


open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance sourceUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]


end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators

namespace CompletedGauss
variable {α β γ ι:Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] in
lemma residualLabelVia_nonresidual_equiv (E:α⊕β≃ι) (T:β≃γ)
    (l:β→Fin 3) (l':γ→Fin 3) (hl:∀b,l' (T b)=l b) :
    residualLabelVia ((Equiv.sumCongr (Equiv.refl α) T.symm).trans E) l'=
      residualLabelVia E l := by
  let E':=((Equiv.sumCongr (Equiv.refl α) T.symm).trans E)
  funext i
  obtain ⟨a,rfl⟩:=E.surjective i
  cases a with
  | inl a=>
    have he:E (Sum.inl a)=E' (Sum.inl a):=rfl
    calc
      _=residualLabelVia E' l' (E' (Sum.inl a)):=by rw [he]
      _=0:=residualLabelVia_apply E' l' (Sum.inl a)
      _=_:=(residualLabelVia_apply E l (Sum.inl a)).symm
  | inr b=>
    have he:E (Sum.inr b)=E' (Sum.inr (T b)):=by simp [E']
    calc
      _=residualLabelVia E' l' (E' (Sum.inr (T b))):=by rw [he]
      _=l' (T b):=residualLabelVia_apply E' l' (Sum.inr (T b))
      _=l b:=hl b
      _=_:=(residualLabelVia_apply E l (Sum.inr b)).symm

end CompletedGauss

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O


lemma reflectionSixLabel_encode_at {β:Type*} [Fintype β]
    (B:Finset β) (l:B→Fin 3) (b:B) :
    reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b := by
  classical
  apply Fin.ext
  simp only [encodeReflectionSix,dif_pos b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hb:=(l b).isLt
  omega

end CanonicalRowCompletion.ActualFiber


end

end OAI

end


