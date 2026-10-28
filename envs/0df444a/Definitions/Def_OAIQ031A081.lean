-- Prove2me | Definitions.Def_OAIQ031A081
-- name    : OAIQ031A081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:24:34.791637+00:00
-- url     : https://prove2.me/theorems/3707b95a-f6c0-4ce8-895a-1b5202f549f5
-- title:
--   Definitions bundle OAIQ031A081 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 18 definitions, 4 instances and 23 theorems. The definitions and types are `OAI.ArExplicit.CocycleData.detector`, `OAI.ArExplicit.DualTensor.complexIso`, `OAI.ArExplicit.ModuleBar.cochain3`, `OAI.ArExplicit.ModuleBar.extClass3`, `OAI.ArExplicit.Resolution.ExceptionalHomology`, `OAI.ArExplicit.Resolution.cResolution_homology_zero`, `OAI.ArExplicit.Resolution.exceptionalBoundaryPreimage`, `OAI.ArExplicit.Resolution.exceptionalCycle`, `OAI.ArExplicit.Resolution.exceptionalCyclesMap`, `OAI.ArExplicit.Resolution.exceptionalShortComplex`, `OAI.ArExplicit.Resolution.exceptionalShortComplexIso`, `OAI.ArExplicit.Resolution.inflatedSimpleIso`, `OAI.ArExplicit.Resolution.leftEllPreimage`, `OAI.ArExplicit.Resolution.leftUPreimage`, `OAI.ArExplicit.Resolution.rightSimpleDualEquiv`, `OAI.ArExplicit.Resolution.tExtendedSequence`, `OAI.ArExplicit.Resolution.tInducedCochain`, `OAI.ArExplicit.Resolution.tInducedDerived`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_SimpleDual`, `AuslanderReiten_Bar_ModuleBarCochain`, `AuslanderReiten_Cocycles_CocycleDetector`, `AuslanderReiten_Duality_DualResolution`, `AuslanderReiten_Duality_DualTensorComplex`, `AuslanderReiten_Duality_DualTensorModule`, `AuslanderReiten_Duality_IdealDualComparison`, `AuslanderReiten_Duality_IdealDualComplex`, `AuslanderReiten_Duality_IdealDualHomology`, `AuslanderReiten_Homology_ExceptionalHomology`, `AuslanderReiten_Modules_TInducedHom`, `AuslanderReiten_Modules_TInductionHomology`, `AuslanderReiten_Modules_TInductionTriangle`.
--
--   **Imports.** It imports the bundles `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A065`, `OAIQ031A066` and `OAIQ031A067` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A094`, `OAIQ031A095` and `OAIQ031A106`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A065
import Definitions.Def_OAIQ031A066
import Definitions.Def_OAIQ031A067

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleDual
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] (q : k)
local notation "C" => BaseAlgebra k q

def rightSimpleDualEquiv (hq : 1 + q ≠ 0) : RightDual k C (Simple q) ≃ₗ[C] Simple q where
  toFun φ := φ.functional (generator q) • generator q
  invFun s := ⟨(simpleCoordinate q).smulRight (simpleCoordinate q s)⟩
  left_inv φ := by
    apply RightDual.ext
    apply LinearMap.ext
    intro s
    change simpleCoordinate q s * simpleCoordinate q
      (φ.functional (generator q) • generator q) = φ.functional s
    rw [map_smul, generator_coordinate, smul_eq_mul, mul_one, simple_expand q hq s]
    simp only [map_smul, smul_eq_mul, generator_coordinate, mul_one]
  right_inv s := by
    change (simpleCoordinate q (generator q) * simpleCoordinate q s) • generator q = s
    rw [generator_coordinate, one_mul]
    exact (simple_expand q hq s).symm
  map_add' φ ψ := by
    change (φ.functional (generator q) + ψ.functional (generator q)) • generator q = _
    exact add_smul _ _ _
  map_smul' c φ := by
    change φ.functional (c.coeff f • generator q) • generator q =
      c • (φ.functional (generator q) • generator q)
    apply simpleCoordinate_injective q hq
    simp [simpleCoordinate_smul, mul_comm]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem cochain3Linear_left (p : AbsoluteBar.Cochain3 k R) (a : R) (x : object k R M 4) :
    cochain3Linear k R M p (left k R M 4 a x) = a • cochain3Linear k R M p x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b x => exact mul_smul _ _ _

def cochain3 (p : AbsoluteBar.Cochain3 k R) :
    moduleObject k R M 4 →ₗ[R] moduleObject k R M 0 where
  toAddHom := (cochain3Linear k R M p).toAddHom
  map_smul' a x := cochain3Linear_left k R M p a x

theorem cochain3_boundary_tmul (p : AbsoluteBar.Cochain3 k R) (a b c d e : R) (m : M) :
    cochain3Linear k R M p (boundary k R M 4
      (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] m)))))) =
      (a * (b * p c d e + p (b * c) d e + p b (c * d) e +
        p b c (d * e) + p b c d * e)) • m := by
  simp only [boundary_succ_tmul k R M 3, boundary_succ_tmul k R M 2,
    boundary_succ_tmul k R M 1, boundary_succ_tmul k R M 0, boundary_zero_tmul k R M,
    left_tmul k R M 3, left_tmul k R M 2, left_tmul k R M 1, left_tmul k R M 0,
    TensorProduct.tmul_add, map_add, cochain3Linear_tmul k R M p,
    mul_smul, add_smul, smul_add]
  abel

theorem cochain3_closed (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (cochain3Linear k R M p).comp (boundary k R M 4) = 0 := by
  ext a b c d e m
  change cochain3Linear k R M p (boundary k R M 4
    (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] m)))))) = 0
  rw [cochain3_boundary_tmul, hp]
  simp

variable [CharP k 2]

theorem cochain3_cycle (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (complex k R M).d 4 3 ≫ ModuleCat.ofHom
      (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p) = 0 := by
  rw [complex_d k R M 3]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (cochain3_closed k R M p hp) x

def extClass3 (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    CategoryTheory.Abelian.Ext (moduleObject k R M 0) (moduleObject k R M 0) 3 :=
  (resolution k R M).extMk
    (ModuleCat.ofHom (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p))
    4 rfl (cochain3_cycle k R M p hp)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

def detector : ModuleBar.moduleObject k R S 4 :=
  q ^ 2 • ((1 : R) ⊗ₜ[k] (T.vector q (false, .t) ⊗ₜ[k]
    (T.vector q (false, .x) ⊗ₜ[k] (T.vector q (true, .j) ⊗ₜ[k] simpleGenerator q)))) +
  (1 : R) ⊗ₜ[k] (T.vector q (false, .t) ⊗ₜ[k]
    (T.vector q (false, .y) ⊗ₜ[k] (T.vector q (true, .j) ⊗ₜ[k] simpleGenerator q)))

theorem detector_evaluation (hq1 : 1 + q ≠ 0) :
    ModuleBar.cochain3 k R S (p q) (detector q) = q ^ 3 • simpleGenerator q := by
  change ModuleBar.cochain3Linear k R S (p q) (detector q) = _
  simp only [detector, map_add, map_smul]
  rw [ModuleBar.cochain3Linear_tmul k R S (p q),
    ModuleBar.cochain3Linear_tmul k R S (p q)]
  simp only [one_mul, p_txJ, p_tyJ, zero_smul, smul_zero, zero_add]
  rw [smul_assoc, vector_smul_simple q hq1]
  simp

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem evaluateE_precompose (r : k) (g : E q →ₗ[C] C) :
    evaluateE q (g.comp (dEll q r)) = leftEll q r (evaluateE q g) := by
  apply Subtype.ext
  change g (dEll q r (vertexE q)) = ell q r * g (vertexE q)
  have hd : dEll q r (vertexE q) = ell q r • vertexE q := by
    apply Subtype.ext
    change basisVector q e * ell q r = ell q r * basisVector q e
    rw [ell_right_e]
    ext i
    cases i <;> simp [ell, product]
  rw [hd, g.map_smul]
  rfl

theorem ell_mul_formula (r : k) (a : C) :
    ell q r * a = a.coeff e • ell q r +
      (r * a.coeff x + q * a.coeff y) • basisVector q z +
      ((1 + r) * a.coeff u) • basisVector q v := by
  ext i
  cases i <;> simp [ell, product] <;> ring

theorem rightF_expand (a : rightF q) : (a : C) =
    (a : C).coeff f • basisVector q f + (a : C).coeff t • basisVector q t +
    (a : C).coeff j • basisVector q j + (a : C).coeff n • basisVector q n := by
  ext i
  cases i <;> simp

theorem evaluate_precompose_dU (g : F q →ₗ[C] C) :
    evaluateE q (g.comp (dU q)) = leftU q (evaluateF q g) := by
  apply Subtype.ext
  change g (dU q (vertexE q)) = basisVector q u * g (vertexF q)
  have hd : dU q (vertexE q) = basisVector q u • vertexF q := by
    apply Subtype.ext
    change basisVector q e * basisVector q u = basisVector q u * basisVector q f
    simp [basis_mul, multiplicationTable]
  rw [hd, g.map_smul]
  rfl

theorem u_mul_formula (a : C) : basisVector q u * a =
    a.coeff f • basisVector q u + a.coeff t • (q • basisVector q x + basisVector q y) +
    a.coeff j • basisVector q z + a.coeff n • basisVector q v := by
  ext i
  cases i <;> simp [product]
  ring

theorem leftU_injective : Function.Injective (leftU q) := by
  apply (injective_iff_map_eq_zero (leftU q)).mpr
  intro a ha
  have hu := congrArg (fun b : rightE q => (b : C).coeff u) ha
  have hy := congrArg (fun b : rightE q => (b : C).coeff y) ha
  have hz := congrArg (fun b : rightE q => (b : C).coeff z) ha
  have hv := congrArg (fun b : rightE q => (b : C).coeff v) ha
  simp [product] at hu hy hz hv
  apply Subtype.ext
  rw [rightF_expand q a]
  simp [hu, hy, hz, hv]

def leftUPreimage (α β γ δ : k) : rightF q :=
  ⟨α • basisVector q f + β • basisVector q t + γ • basisVector q j + δ • basisVector q n, by
    change basisVector q f * _ = _
    simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

theorem leftUPreimage_spec (α β γ δ : k) :
    (leftU q (leftUPreimage q α β γ δ) : C) =
      α • basisVector q u + β • (q • basisVector q x + basisVector q y) +
      γ • basisVector q z + δ • basisVector q v := by
  rw [coe_leftU, u_mul_formula]
  simp [leftUPreimage]

variable [CharP k 2]

theorem ell_mul_eq_zero_iff (r : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0) (a : C) :
    ell q r * a = 0 ↔ a.coeff e = 0 ∧ a.coeff u = 0 ∧
      a.coeff y = r / q * a.coeff x := by
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff x) h
    have hz := congrArg (fun b : C => b.coeff z) h
    have hv := congrArg (fun b : C => b.coeff v) h
    simp [ell, product] at he hz hv
    have hu : (1 + r) * a.coeff u = 0 := by
      calc
        _ = a.coeff u + r * a.coeff u := by ring
        _ = 0 := hv
    refine ⟨he, (mul_eq_zero.mp hu).resolve_left hr, ?_⟩
    have hy : r * a.coeff x = q * a.coeff y := (CharTwo.add_eq_zero.mp hz).symm
    apply (mul_left_cancel₀ hq)
    calc
      q * a.coeff y = r * a.coeff x := hy.symm
      _ = q * (r / q * a.coeff x) := by field_simp
  · rintro ⟨he, hu, hy⟩
    rw [ell_mul_formula, he, hu, hy]
    have hcancel : r * a.coeff x + q * (r / q * a.coeff x) = 0 := by
      have hd : q * (r / q * a.coeff x) = r * a.coeff x := by field_simp
      rw [hd, CharTwo.add_self_eq_zero]
    simp [hcancel]

def leftEllPreimage (r α β γ : k) : rightE q :=
  ⟨α • basisVector q e + (β / q) • basisVector q y +
    (γ / (1 + r)) • basisVector q u, by
      change basisVector q e * _ = _
      simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem leftEllPreimage_spec (r α β γ : k) (hq : q ≠ 0) (hr : 1 + r ≠ 0) :
    (leftEll q r (leftEllPreimage q r α β γ) : C) =
      α • ell q r + β • basisVector q z + γ • basisVector q v := by
  rw [coe_leftEll, ell_mul_formula]
  have hβ : q * (β / q) = β := by rw [mul_comm, div_mul_cancel₀ _ hq]
  have hγ : (1 + r) * (γ / (1 + r)) = γ := by rw [mul_comm, div_mul_cancel₀ _ hr]
  simp [leftEllPreimage, hβ, hγ]

def exceptionalBoundaryPreimage (α β : k) : rightE q :=
  ⟨α • basisVector q e + (β / q) • basisVector q y, by
    change basisVector q e * _ = _
    simp [mul_add, Algebra.mul_smul_comm, basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem exceptionalBoundaryPreimage_spec (α β : k) (hq : q ≠ 0) :
    (leftEll q 1 (exceptionalBoundaryPreimage q α β) : C) =
      α • ell q 1 + β • basisVector q z := by
  rw [coe_leftEll, ell_mul_formula]
  have hβ : q * (β / q) = β := by rw [mul_comm, div_mul_cancel₀ _ hq]
  simp [exceptionalBoundaryPreimage, hβ]

def exceptionalCycle : rightE q := ⟨basisVector q v, by
  change basisVector q e * basisVector q v = basisVector q v
  simp [basis_mul, multiplicationTable]⟩

omit [CharP k 2] in
theorem exceptionalCycle_closed (r : k) : leftEll q r (exceptionalCycle q) = 0 := by
  apply Subtype.ext
  change ell q r * basisVector q v = 0
  rw [ell_mul_formula]
  simp

theorem exceptional_right_action (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (a : rightE q) (ha : leftEll q q a = 0) (b : C) :
    ((a : C) * b).coeff v = (a : C).coeff v * b.coeff f := by
  have hh : ell q q * (a : C) = 0 := congrArg Subtype.val ha
  obtain ⟨he, hu, hy⟩ := (ell_mul_eq_zero_iff q q hq hq1 (a : C)).mp hh
  simp only [div_self hq, one_mul] at hy
  simp [product, he, hu, hy, CharTwo.add_self_eq_zero, add_assoc]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.DualTensor
variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
variable [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

theorem moduleEvaluation_natural (a : V →ₗ[R] W)
    (z : BalancedTensor k R (Coinduced k R) V) :
    moduleEvaluation (BalancedTensor.mapRight (S := R) a z) =
      RightDual.map (precomposeRight a) (moduleEvaluation z) := by
  apply RightDual.ext
  ext f
  exact evaluation_natural a z f

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.DualTensor
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def complexIso [∀ n, Module.Finite R (P.X n)] [∀ n, Module.Projective R (P.X n)] :
    tensorComplex (k := k) P ≅ dualHomComplex (k := k) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleEvaluationEquiv (k := k) (R := R) (V := P.X n)).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := by simpa using hij.symm
      rw [dualHomComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (moduleEvaluation_natural (P.d (j + 1) j).hom z).symm)

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ExceptionalHomology
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

theorem exceptional_differential_comp : (leftEll q q).comp (leftEll q 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change ell q q * (ell q 1 * (a : C)) = 0
  rw [← mul_assoc, show ell q q * ell q 1 = 0 by simpa using ell_successor_mul q 1, zero_mul]

abbrev ExceptionalHomology := RightDualHomology.Homology
  (leftEll q 1) (leftEll q q) (exceptional_differential_comp q)

def exceptionalCyclesMap (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (leftEll q q) →ₗ[Cᵐᵒᵖ] Simple q where
  toFun a := (a.val : C).coeff v • generator q
  map_add' a b := add_smul _ _ _
  map_smul' c a := by
    change ((a.val : C) * c.unop).coeff v • generator q =
      c.unop.coeff f • ((a.val : C).coeff v • generator q)
    rw [exceptional_right_action q hq hq1 a.val a.property c.unop, mul_comm, mul_smul]

theorem exceptionalCyclesMap_surjective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    Function.Surjective (exceptionalCyclesMap q hq hq1) := by
  intro s
  let r := simpleCoordinate q s
  refine ⟨⟨r • exceptionalCycle q, ?_⟩, ?_⟩
  · change leftEll q q (r • exceptionalCycle q) = 0
    rw [LinearMap.map_smul_of_tower, exceptionalCycle_closed]
    exact @smul_zero k (rightE q) inferInstance inferInstance r
  · change ((r • (exceptionalCycle q : C)).coeff v) • generator q = s
    simpa [exceptionalCycle, r] using (simple_expand q hq1 s).symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

theorem idealDualComplex_d (n : ℕ) :
    (idealDualComplex q).d (n + 1) n = idealDualDifferential q n :=
  ChainComplex.of_d _ _ _

omit [CharP k 2] in
theorem idealDual_exact_zero : Function.Surjective (idealDualDifferential q 0) :=
  RightDual.map_surjective (k := k) (leftU q) (leftU_injective q)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualComparison
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
instance complex_scalarTower (n : ℕ) : IsScalarTower k C ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : IsScalarTower k C (F q))
  | succ n => exact (inferInstance : IsScalarTower k C (E q))

instance homETower : IsScalarTower k Cᵐᵒᵖ (E q →ₗ[C] C) where
  smul_assoc r c f := by
    apply LinearMap.ext
    intro a
    change f a * (r • c.unop) = r • (f a * c.unop)
    exact mul_smul_comm _ _ _

instance homFTower : IsScalarTower k Cᵐᵒᵖ (F q →ₗ[C] C) where
  smul_assoc r c f := by
    apply LinearMap.ext
    intro a
    change f a * (r • c.unop) = r • (f a * c.unop)
    exact mul_smul_comm _ _ _

instance cResolution_finite_terms (n : ℕ) : Module.Finite C ((complex q).X n) :=
  Module.Finite.of_restrictScalars_finite k C ((complex q).X n)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_IdealDualHomology
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

def exceptionalShortComplex : ShortComplex (ModuleCat C) :=
  ShortComplex.moduleCatMk (RightDual.map (k := k) (leftEll q q))
    (RightDual.map (k := k) (leftEll q 1)) (by
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q q (leftEll q 1 a)) = 0
      have h := LinearMap.congr_fun (exceptional_differential_comp q) a
      change leftEll q q (leftEll q 1 a) = 0 at h
      rw [h, map_zero])

def exceptionalShortComplexIso :
    (idealDualComplex q).sc' 3 2 1 ≅ exceptionalShortComplex q :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q q a) = φ.functional (leftEll q (q ^ 1) a)
      rw [pow_one])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q 1 a) = φ.functional (leftEll q (q ^ 0) a)
      rw [pow_zero])

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionHomology
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
local notation "T" => ArExplicit.T k q

def inflatedSimpleIso :
    (TrivialInduction.inflate (k := k)).obj (ModuleCat.of C (Simple q)) ≅
      ModuleCat.of T (Simple q) := Iso.refl _

def cResolution_homology_zero (h : NoPositivePowerOne q) :
    (complex q).homology 0 ≅ ModuleCat.of C (Simple q) := by
  letI := toSimple_quasiIso q h
  exact isoOfQuasiIsoAt (toSimple q) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInducedHom
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q

def tInducedCochain : CochainComplex (ModuleCat T) ℤ :=
  (TrivialInduction.inducedComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TInductionTriangle
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q

def tExtendedSequence : ShortComplex (CochainComplex (ModuleCat T) ℤ) :=
  (TrivialInduction.sequence (k := k) (complex q)).map
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat T))

theorem tExtendedSequence_shortExact : (tExtendedSequence q).ShortExact :=
  extend_shortExact _ _ (TrivialInduction.sequence_shortExact (complex q))

variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tInducedDerived : DerivedCategory (ModuleCat T) :=
  DerivedCategory.Q.obj (tInducedCochain q)

end ArExplicit.Resolution

end

end OAI
end


