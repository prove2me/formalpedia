-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:39.250809+00:00
-- url     : https://prove2.me/theorems/eef67311-87f6-43ee-83a0-9a54afaba78d
-- title:
--   Basics
-- statement:
--   Definitions and structural lemmas for Basics, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/Basics.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
noncomputable section
namespace PI.GreenHCLabel
section BasicsAux
variable {Γ : Type} [Group Γ]
abbrev basicsLin {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) : σ →ₗ[ℂ] τ := f.hom.hom.hom
def basicsMk {σ τ : FDRep ℂ Γ} (φ : σ →ₗ[ℂ] τ) (hφ : ∀ g, φ ∘ₗ σ.ρ g = τ.ρ g ∘ₗ φ) : σ ⟶ τ where
  hom := InducedCategory.homMk (ModuleCat.ofHom φ)
  comm g := by
    apply FGModuleCat.hom_ext
    exact hφ g
def basicsRes {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : Representation ℂ Γ W where
  toFun g := (ρ g).restrict (hW g)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' _ _ := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Module.End.mul_apply]
def basicsIncl (τ : FDRep ℂ Γ) (W : Submodule ℂ τ) (hW : ∀ g, ∀ v ∈ W, τ.ρ g v ∈ W) :
    FDRep.of (basicsRes τ.ρ W hW) ⟶ τ :=
  basicsMk W.subtype (fun _ => LinearMap.ext fun _ => rfl)
end BasicsAux
end PI.GreenHCLabel


