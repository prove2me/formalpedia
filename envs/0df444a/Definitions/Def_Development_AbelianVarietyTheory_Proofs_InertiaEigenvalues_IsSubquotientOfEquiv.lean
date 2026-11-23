-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:34.338+00:00
-- url     : https://prove2.me/theorems/a915c6e5-37db-412e-867b-e1da1fa6a145
-- title:
--   Is Subquotient Of Equiv
-- statement:
--   Definitions and structural lemmas for Is Subquotient Of Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.JacStages
section Rel
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
def relUnipD (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)
def relEmbD (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)
theorem relEmbD_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmbD k f g ∈ Subgroup.normalizer (relUnipD k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)
def relDeltaHalfD (c : ∀ i, β i → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)
variable {k}
def relJacD (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnipD k f)) :=
  twist (jacquet ρ (relUnipD k f) (relEmbD k f) (relEmbD_mem_normalizer k f)) (relDeltaHalfD k c)⁻¹
end Rel
section Flat
variable {s : ℕ} {t : Fin s → ℕ}
def refinePlace {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun p : Σ a, Fin (t a) => Fin (d' p.1 p.2)) finSigmaFinEquiv.symm).trans
    ((Equiv.sigmaAssoc fun a b => Fin (d' a b)).trans ((Equiv.sigmaCongrRight e').trans e))
def flatHom (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    (∀ a b, Γ a b) →* ∀ c : Fin (∑ a, t a), Γ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 where
  toFun g c := g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  map_one' := rfl
  map_mul' _ _ := rfl
end Flat
section Pull
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Pull
end GlobalTheory.JacStages


