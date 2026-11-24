-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:01.720799+00:00
-- url     : https://prove2.me/theorems/8b00fb90-bdd4-4e8d-bcee-2f973866947e
-- title:
--   Is Open Ker Of Continuous
-- statement:
--   Definitions and structural lemmas for Is Open Ker Of Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenKerOfContinuous.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
namespace GlobalTheory.RootEx.UniformLattices
section Lattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
def ballLat (m : Type) (s : kˣ) : Submodule 𝒪[k] (m → k) where
  carrier := {x | ∀ i, x i ∈ cball s}
  add_mem' hx hy i := add_mem_cball (hx i) (hy i)
  zero_mem' i := by simp [cball]
  smul_mem' a x hx i := by
    show valuation k ((a : k) * x i) ≤ valuation k (s : k)
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp a.2)).trans (hx i)
variable {ψ : AddChar k Circle}
end Lattices
section Reps
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
end Reps
section Abstract
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
  {ψ : AddChar k Circle} {ν : Measure k} {V : Type} [AddCommGroup V] [Module ℂ V]
  {ω : Representation ℂ (GL (n ⊕ Fin c) k) V} {l : V →ₗ[ℂ] ℂ} {v : V}
end Abstract
section Target
open Unfolding
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} {ν : Measure k} {μ : kˣ →* ℂˣ}
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {π : Representation ℂ (GL n k) P}
  {π' : Representation ℂ (GL n' k) P'}
def omS {a : Type} (b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) := (omR μ).comp (MonoidHom.inl _ _)
def untw {m : Type} [Fintype m] [DecidableEq m] (η : kˣ →* ℂˣ) (σ : Representation ℂ (GL m k) A) :
    Representation ℂ (GL m k) A where
  toFun g := (((η (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) • σ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]
end Target
end GlobalTheory.RootEx.UniformLattices


