-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:18.078852+00:00
-- url     : https://prove2.me/theorems/dcbe1153-a902-434e-866b-0e2a6d7e8c26
-- title:
--   Core Iff Collapses With
-- statement:
--   Definitions and structural lemmas for Core Iff Collapses With, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
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
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.CollapseCompare
section Average
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]
end Average
section Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def omRep (μ : kˣ →* ℂˣ) : Representation ℂ (GL n' k × GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := omS μ g.1 g.2
      map_add' := fun Φ Ψ => Subtype.ext (funext fun x => by simp [omS, om, mul_add])
      map_smul' := fun z Φ => Subtype.ext (funext fun x => by simp [omS, om]; ring) }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (om_mul μ g.1 h.1 g.2 h.2 Φ.1)
variable [MeasurableSpace k] [BorelSpace k]
def Core (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (bas : GL (n ⊕ Fin c) k) (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ)
    (lam : J →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (κ : ℝ) : Prop :=
  ∀ (V' V A : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ),
    (∀ γ φ (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ 1 γ Ψ.1 → θ φ Ψ' = π γ (θ φ Ψ)) → IsPos ψ 1 π σ b →
    ∀ (φ : V') (v : A), (∀ h : J, σ (h : GL (n ⊕ Fin c) k) v = (lam h : ℂ) • v) →
    ∀ f : GL (n ⊕ Fin c) k → ℂ, (∀ h (Ψ : SB (Matrix n n' k)), Ψ.1 = flat ψ ν μ Φ 1 h → f h = b (θ φ Ψ) (σ h v)) →
    ∀ Ξ : SB (Matrix n n' k), Ξ.1 = xi ψ ν μ Φ J bas 1 1 →
    ∀ z : ℂ, IsQuotInt ν μX μG 1 f z ↔ z = (κ : ℂ) * b (θ φ Ξ) v
variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}
def untwist (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) : J →* ℂˣ :=
  lam * (μ.comp (Matrix.GeneralLinearGroup.det.comp J.subtype))⁻¹
end Pointwise
section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def cjG (t : GL (n ⊕ Fin c) k) : GL (n ⊕ Fin c) k ≃ₜ* GL (n ⊕ Fin c) k where
  toMulEquiv := MulAut.conj t
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const
def cjJ (t : GL (n ⊕ Fin c) k) (J : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL (n ⊕ Fin c) k) :=
  J.comap (MulAut.conj t).toMonoidHom
def cjLam (t : GL (n ⊕ Fin c) k) {J : Subgroup (GL (n ⊕ Fin c) k)} (lam : J →* ℂˣ) : cjJ t J →* ℂˣ :=
  lam.comp ((MulAut.conj t).toMonoidHom.subgroupComap J)
structure Adapted (t : GL (n ⊕ Fin c) k) : Prop where
  norm : t ∈ Subgroup.normalizer (N k n c 1 : Set (GL (n ⊕ Fin c) k))
  comm : ∀ g : GL n k, t * embX c g * t⁻¹ = embX c g
variable [MeasurableSpace k] [BorelSpace k]
end Transport
section Normalise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)
variable [MeasurableSpace k] [BorelSpace k]
end Normalise
section Main
def CollapseUniform : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
    ∀ (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)),
    ν.IsAddHaarMeasure → μX.IsHaarMeasure → μG.IsHaarMeasure →
    ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
      IsCompact (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (bas : GL (n ⊕ Fin c) k),
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
      ∀ (μ : kˣ →* ℂˣ) (lam : J →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
        HasTargetType μ J lam Φ.1 → OneCoset ψ ν μ Φ.1 J → Core ν μX μG J bas ψ μ lam Φ.1 κ
end Main
end GlobalTheory.CollapseCompare


