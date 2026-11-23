-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:27.72166+00:00
-- url     : https://prove2.me/theorems/577d5514-afe8-401d-96e5-a43136ee0ea6
-- title:
--   Support Exists Of
-- statement:
--   Definitions and structural lemmas for Support Exists Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/SupportExistsOf.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_GreenHCLabelOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
open scoped TensorProduct
namespace PI.GreenHCLabel
def SimpleIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrrRep τ.ρ
def ConstSymm : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V), Simple τ → (IsConstituent τ ρ ↔ ∃ ψ ∈ Intw ρ τ.ρ, ψ ≠ 0)
def CommonConst : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ V'),
    Simple τ → IsConstituent τ ρ → IsConstituent τ ρ' → ∃ φ ∈ Intw ρ ρ', φ ≠ 0
def ProdSimple : Prop :=
  ∀ (s : ℕ) (L : Fin s → Type) [∀ c, Group (L c)] [∀ c, Fintype (L c)] (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Nontrivial W] (ρ : Representation ℂ (∀ c, L c) W),
    ∃ (lam : ∀ c, FDRep ℂ (L c)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] W), (∀ c, Simple (lam c)) ∧ Φ ≠ 0 ∧
      ∀ g : ∀ c, L c, Φ ∘ₗ PiTensorProduct.map (fun c => (lam c).ρ (g c)) = ρ g ∘ₗ Φ
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
def Frob : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (τ : FDRep ℂ (GL ι K)) (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ), Φ ≠ 0 →
    (∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) → ∃ ψ ∈ Intw (hcRep K b lam) τ.ρ, ψ ≠ 0
def HCFin : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    FiniteDimensional ℂ (hcSpace K b lam)
def Jacquet : Prop :=
  ∀ (n : ℕ) (τ : FDRep ℂ (GL (Fin n) K)), Simple τ →
    ∃ (s : ℕ) (b : Fin n → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
      (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ),
      Function.Surjective b ∧ (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) ∧ Φ ≠ 0 ∧
      ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ
variable {K}
end PI.GreenHCLabel


