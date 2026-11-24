-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:53.830412+00:00
-- url     : https://prove2.me/theorems/d9ed92ca-6e37-4f21-8ca1-2cc7fae624fe
-- title:
--   Orbit Locally Constant
-- statement:
--   Definitions and structural lemmas for Orbit Locally Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OrbitLocallyConstant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMemSBEqOneOnCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpECutOmEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_opE_SB_and_linear
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
namespace GlobalTheory.RootEx.Unfolding
section Basic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def omR {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k × GL b k) (SB (Matrix b a k)) where
  toFun gh :=
    { toFun := fun Φ => ⟨om μ gh.1 gh.2 Φ.1, om_mem_SB μ gh.1 gh.2 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext; funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun z Φ => by
        apply Subtype.ext; funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (om_mul μ g.1 h.1 g.2 h.2 Φ.1)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def cut (p : ℕ) (χ : (n' → k) → ℂ) (y : Matrix (n ⊕ Fin c) n' k) : ℂ :=
  ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) s) else 0
omit [Field k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem cut_lc (p : ℕ) {χ : (n' → k) → ℂ} (hχ : IsLocallyConstant χ) :
    IsLocallyConstant (cut (n := n) (c := c) p χ) := by
  have h : ∀ l : Fin c, IsLocallyConstant fun y : Matrix (n ⊕ Fin c) n' k => χ (fun s => y (Sum.inr l) s) :=
    fun l => hχ.comp_continuous (by fun_prop)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [eventually_all.2 fun l => (h l).eventually_eq x] with y hy
  simp only [cut, hy]
def cutL (p : ℕ) (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) :
    SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) where
  toFun Φ := ⟨fun y => cut p χ y.toCols₁ * Φ.1 y,
    ((cut_lc p hχ).comp_continuous (continuous_matrix fun i j => by
      simp only [toCols₁, Matrix.of_apply]; fun_prop)).mul Φ.2.1, Φ.2.2.mul_left⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' z Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
variable [MeasurableSpace k] [BorelSpace k]
def opL {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ) :
    SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n n' k) where
  toFun Φ := ⟨opE ψ ν p Φ.1, (opE_SB_and_linear k n n' c p ψ hψ ν).1 _ Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    have := (opE_SB_and_linear k n n' c p ψ hψ ν).2 1 _ Φ.2 _ Ψ.2
    simpa using this
  map_smul' z Φ := by
    apply Subtype.ext; funext x
    simp only [opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      integral_const_mul]
end Basic
section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ)
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) {π : Representation ℂ (GL n k) P} {π' : Representation ℂ (GL n' k) P'}
  (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A)
def fc (p : ℕ) (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (h : GL (n ⊕ Fin c) k) : ℂ :=
  b (θ φ (opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)))) (σ h F)
variable {μ σ θ b}
def ev {X : Type*} [TopologicalSpace X] (x : X) : SB X →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (SB X).subtype
end Step
end GlobalTheory.RootEx.Unfolding


