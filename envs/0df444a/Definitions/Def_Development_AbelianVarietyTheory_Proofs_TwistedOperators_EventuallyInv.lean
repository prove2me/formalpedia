-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:32.114717+00:00
-- url     : https://prove2.me/theorems/25699c76-6cba-4afe-817b-6ac304b8d76d
-- title:
--   Eventually Inv
-- statement:
--   Definitions and structural lemmas for Eventually Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyInv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
namespace GlobalTheory.SmGL.Stages
section Abstract
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
def mkInd {P : Subgroup G} (σ : Representation F P W) (f : G → W)
    (h1 : ∀ (p : P) (g : G), f (p * g) = σ p (f g)) (h2 : ∀ᶠ u in 𝓝 (1 : G), ∀ x, f (x * u) = f x) :
    smoothPart (ind P σ) :=
  ⟨⟨f, h1⟩, mem_smoothPart_of_nhds (h2.mono fun _ hu => Subtype.ext (funext hu))⟩
def evalAt {P : Subgroup M} (σ : Representation F P W) (m : M) : smoothPart (ind P σ) →ₗ[F] W where
  toFun f := f.1.1 m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Abstract
section Blocks
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c ab bc n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype ab] [DecidableEq ab] [Fintype bc] [DecidableEq bc] [Fintype n] [DecidableEq n]
  {W V₁ V₂ V₃ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
def pr {R : Type} [CommRing R] (e : a ⊕ b ≃ n) : parab R (two e) →* GL a R × GL b R :=
  (leviTwo R a b).symm.toMonoidHom.comp (leviProj R (two e))
def sec {R : Type} [CommRing R] (e : a ⊕ b ≃ n) : GL a R × GL b R →* parab R (two e) :=
  (emb₂ R e).codRestrict _ fun _ => leviEmb_mem_parab R _ _
def dl (e : a ⊕ b ≃ n) : parab k (two e) →* ℂˣ := (deltaHalf k (Two a b)).comp (leviProj k (two e))
def dat (e : a ⊕ b ≃ n) (ρ : Representation ℂ (GL a k × GL b k) W) :
    Representation ℂ (parab k (two e)) W :=
  (twist (ρ.comp (leviTwo k a b).symm.toMonoidHom) (deltaHalf k (Two a b))).comp (leviProj k (two e))
def tauSnd (e : a ⊕ b ≃ n) (π : Representation ℂ (GL b k) W) : Representation ℂ (parab k (two e)) W :=
  twist (π.comp ((MonoidHom.snd _ _).comp (pr e))) (dl e)
def tauFst (e : a ⊕ b ≃ n) (π : Representation ℂ (GL a k) W) : Representation ℂ (parab k (two e)) W :=
  twist (π.comp ((MonoidHom.fst _ _).comp (pr e))) (dl e)
end Blocks
end GlobalTheory.SmGL.Stages


