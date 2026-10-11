-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
-- name    : PNT_ZeroFree_433_0244_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:31:48.163523+00:00
-- url     : https://prove2.me/theorems/a60d7f46-4510-454b-b558-290fb9a82058
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedCuspPhases [0244_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedCuspPhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedCuspPhases.lean#L304-L554

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0016
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel1
import Definitions.Def_PNT_ZeroFree_433_0132_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0222_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedCuspPhases.lean
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
open scoped BigOperators Classical MatrixGroups Matrix


open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def diagonalPrimitiveMap (u:Eisˣ) (v:PrimitiveRow) : PrimitiveRow :=
  ⟨![(u:Eis)^2*v.val 0,v.val 1],by
    refine ⟨?_,?_,v.2.2.2⟩
    · exact (isCoprime_mul_unit_left_left (u.isUnit.pow 2) _ _).mpr v.2.1
    · exact v.2.2.1.mul_left _⟩

def diagonalPrimitiveEquiv (u:Eisˣ) : PrimitiveRow≃PrimitiveRow where
  toFun:=diagonalPrimitiveMap u
  invFun:=diagonalPrimitiveMap u⁻¹
  left_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (↑u⁻¹:Eis)^2*((u:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl
  right_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (u:Eis)^2*((↑u⁻¹:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl


lemma rowEnergy_unit_smul (u:Eisˣ) (v:Fin 2→ℂ) :
    rowEnergy (eisEmbedding (u:Eis) • v)=rowEnergy v := by
  simp only [rowEnergy,Pi.smul_apply,smul_eq_mul,norm_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]


def rayEisenstein (r:Eis) (g:SL(2,ℂ)) (s:ℂ) : ℂ :=
  ∑'v:PrimitiveRow,eisEmbedding (symbol r (v.val 1))*summand g s (primitiveRowEquiv.symm v)


end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def affineLowerTerm (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:Eis) : ℂ :=
  (eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding (q*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s

lemma affineLowerTerm_mul_ray (q r t:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:PrimaryLower) :
    eisEmbedding (symbol t d.val)*affineLowerTerm q r z v s a.val d.val=
      affineLowerTerm q (t*r) z v s a.val d.val := by
  rw [affineLowerTerm,affineLowerTerm,symbol_mul_numerator _ _ _ (primaryLower_primary d),
    map_mul eisEmbedding (symbol t d.val) (symbol r d.val)]
  ring


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
local instance p2mAnonymous_PNT_ZeroFree_433_0244_parallel1_1_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance p2mAnonymous_PNT_ZeroFree_433_0244_parallel1_1_2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance p2mAnonymous_PNT_ZeroFree_433_0244_parallel1_1_3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def eisensteinCoordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) : Fin 2→ℝ :=
  ![(ActualEisensteinCoordinates.coords b).1 • x 0-(ActualEisensteinCoordinates.coords b).2 • x 1,
    (ActualEisensteinCoordinates.coords b).2 • x 0+
      ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • x 1]

def eisensteinTorusMul (b : ActualEisensteinCubic.O) : UnitAddTorus (Fin 2)→+UnitAddTorus (Fin 2) where
  toFun t :=
    ![(ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1,
      (ActualEisensteinCoordinates.coords b).2 • t 0+
        ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' t s := by ext i;fin_cases i <;> simp [smul_add] <;> abel

lemma eisensteinTorusMul_continuous (b : ActualEisensteinCubic.O) : Continuous (eisensteinTorusMul b) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1)
    fun_prop
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).2 • t 0+((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1)
    fun_prop

lemma periodVector_coordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) :
    periodVector (eisensteinCoordinateMul b x)=eisEmbedding b*periodVector x := by
  have hb : eisEmbedding b=((ActualEisensteinCoordinates.coords b).1:ℂ)+
      ((ActualEisensteinCoordinates.coords b).2:ℂ)*omega3 := by
    simpa only [ActualEisensteinCubic.eisEmbedding_eval] using (congrArg eisEmbedding (ActualEisensteinCoordinates.eval_coords b)).symm
  rw [periodVector_apply,periodVector_apply,hb]
  simp only [eisensteinCoordinateMul,Matrix.cons_val_zero,Matrix.cons_val_one,
    zsmul_eq_mul]
  push_cast
  linear_combination -(3*((ActualEisensteinCoordinates.coords b).2:ℂ)*(x 1:ℂ))*EisensteinEmbedding.omega3_sq

lemma eisensteinTorusMul_periodTorus (b : ActualEisensteinCubic.O) (z : ℂ) :
    eisensteinTorusMul b (periodTorus z)=periodTorus (eisEmbedding b*z) := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  rw [←periodVector_coordinateMul,periodTorus_periodVector,periodTorus_periodVector]
  ext i
  fin_cases i <;> rfl


end CubicEisenstein


end

end OAI

end


