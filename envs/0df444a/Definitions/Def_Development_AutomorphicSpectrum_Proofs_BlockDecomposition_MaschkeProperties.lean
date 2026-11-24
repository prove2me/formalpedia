-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:22.9188+00:00
-- url     : https://prove2.me/theorems/e49fe169-1bde-483a-9fa1-478ae8b91cfd
-- title:
--   Maschke Properties
-- statement:
--   Definitions and structural lemmas for Maschke Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MaschkeProperties.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFin.Maschke
section Avg
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
def avg (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g ∘ₗ f ∘ₗ ρ g⁻¹
end Avg
section Schur
variable {Γ : Type} [Group Γ]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Schur
section Main
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Main
end GlobalTheory.CompanionTheory.TyFin.Maschke


