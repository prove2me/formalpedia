-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:36.277143+00:00
-- url     : https://prove2.me/theorems/60195502-84a8-4e99-8f96-20e1478dd0af
-- title:
--   Hida Setting
-- statement:
--   Definitions and structural lemmas for Hida Setting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def tensF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    Fin n → Fin n → Module.End ℂ (Fin n → M) :=
  cond dual (tensVd E) (tensV E)
def eeF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (Fin n → M) :=
  cond dual (eeVd E) (eeV E)
def poleF (dual : Bool) (lam : Fin n → ℝ) : Fin n → ℂ := cond dual (poleVd lam) (poleV lam)
def ratioF (dual : Bool) (lam : Fin n → ℝ) : Fin n → ℝ := cond dual (ratioVd lam) (ratioV lam)
def shiftF (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) : Fin n → ℝ :=
  cond dual (lam - Pi.single s 1) (lam + Pi.single s 1)
def tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) : Submodule ℂ (Fin n → M) :=
  Submodule.pi Set.univ fun _ => S
section Ambient
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def kDiag (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (k : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • σ k (f d)
variable {D : Submodule ℂ H}
def IsGKEndo (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S : Submodule ℂ D) (A : Module.End ℂ (Fin n → D)) : Prop :=
  (∀ f ∈ tensSub S, A f ∈ tensSub S) ∧
    (∀ a b, ∀ f ∈ tensSub S, A (tensF dual E a b f) = tensF dual E a b (A f)) ∧
    ∀ k ∈ Kset ε, ∀ f ∈ tensSub S, ∀ f' ∈ tensSub S,
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
        (fun c => ((A f' c : D) : H)) = kDiag dual σ k (fun c => ((A f c : D) : H))
def IsGKEmb (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (E : Fin n → Fin n → Module.End ℂ D) (S S' : Submodule ℂ D) (ι : D →ₗ[ℂ] (Fin n → D)) : Prop :=
  (∀ x ∈ S', ι x ∈ tensSub S) ∧ (∀ x ∈ S', ι x = 0 → x = 0) ∧
    (∀ a b, ∀ x ∈ S', ι (E a b x) = tensF dual E a b (ι x)) ∧
    ∀ k ∈ Kset ε, ∀ x ∈ S', ∀ x' ∈ S', (x' : H) = σ k (x : H) →
      (fun c => ((ι x' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H))
end Ambient
end ReciprocityTheory.ChartRestriction.DS


