-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:44.131102+00:00
-- url     : https://prove2.me/theorems/068d9d26-1355-4274-a3a4-e4ce2dbe92d8
-- title:
--   Exists Smul Eq Map Of Is Compact Of Is Quasi Separated
-- statement:
--   Definitions and structural lemmas for Exists Smul Eq Map Of Is Compact Of Is Quasi Separated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resModule_smul
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
namespace GlobalTheory.QCoh.Qcqs
section Glue
variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)
end Glue
section Sheaf
variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}
end Sheaf
section BasicOpen
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
def resLinearOver (hW : W ≤ U) (hV : V ≤ U) (h : V ≤ W) :
    letI := resModule F hW
    letI := resModule F hV
    Γ(F, W) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F hW
  letI := resModule F hV
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ by
      rw [resModule_smul, F.map_smul, res_res_ring]; rfl }
variable [F.IsQuasicoherent]
end BasicOpen
section Hom
variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}
def appLinearOver (h : V ≤ U) :
    letI := resModule F h
    letI := resModule G h
    Γ(F, V) →ₗ[Γ(X, U)] Γ(G, V) :=
  letI := resModule F h
  letI := resModule G h
  { toFun := φ.app V
    map_add' := map_add _
    map_smul' := fun _ s ↦ φ.app_smul _ s }
end Hom
end GlobalTheory.QCoh.Qcqs


