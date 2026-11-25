-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RestrictHomApply
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RestrictHomApply
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:50:41.837037+00:00
-- url     : https://prove2.me/theorems/6217b9b8-b382-571a-9c30-551346d1f372
-- title:
--   Restrict Hom Apply
-- statement:
--   Definitions and structural lemmas for Restrict Hom Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RestrictHomApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
namespace GlobalTheory.WeilDeligne.PrimDecomp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
def IsSubWD (a : WDRep h V) (S : Submodule ℂ V) : Prop :=
  (∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) ∧ ∀ v ∈ S, a.N v ∈ S
def restrictHom (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    Representation ℂ (Weil h) S where
  toFun σ := (a.ρ σ).restrict (hS σ)
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp
@[simp] theorem restrictHom_apply (a : WDRep h V) (S : Submodule ℂ V)
    (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) (σ : Weil h) (v : S) :
    ((restrictHom a S hS σ v : S) : V) = a.ρ σ v := rfl
def restrict (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) : WDRep h S where
  ρ := restrictHom a S hS.1
  N := a.N.restrict hS.2
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS.1 σ))
    (a.semisimple σ)
  nilpotent := by
    obtain ⟨k, hk⟩ := a.nilpotent
    have hp : ∀ (j : ℕ) (v : S), (((a.N.restrict hS.2) ^ j) v : V) = (a.N ^ j) v := by
      intro j
      induction j with
      | zero => intro v; simp
      | succ j ih =>
        intro v
        rw [pow_succ', End.mul_apply, pow_succ', End.mul_apply, ← ih]
        rfl
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [hp, hk]
    rfl
  comm σ := by
    ext v
    simp [restrictHom, a.comm_apply]
@[simp] theorem restrict_ρ_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S)
    (σ : Weil h) (v : S) : (((restrict a S hS).ρ σ v : S) : V) = a.ρ σ v := rfl
@[simp] theorem restrict_N_apply (a : WDRep h V) (S : Submodule ℂ V) (hS : IsSubWD a S) (v : S) :
    (((restrict a S hS).N v : S) : V) = a.N v := rfl
def restrictρ (a : WDRep h V) (S : Submodule ℂ V) (hS : ∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) :
    WDRep h S where
  ρ := restrictHom a S hS
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by
    ext v; simp [restrictHom, hσ]
  semisimple σ := End.IsSemisimple.restrict (f := a.ρ σ) ((End.mem_invtSubmodule _).mpr (hS σ))
    (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp
def wtSpace (a : WDRep h V) (k : ℤ) : Submodule ℂ V :=
  absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((k : ℝ) / 2))
def strand (N : End ℂ V) (S : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (m + 1), S.map (N ^ (j : ℕ))
def lowPart (U : ℤ → Submodule ℂ V) (N : End ℂ V) (m : ℕ) : Submodule ℂ V :=
  ⨆ k : ℤ, U k ⊓ LinearMap.ker (N ^ (((m : ℤ) - k + 1) / 2).toNat)
example (a : WDRep h V) : IsSubWD a ⊤ ∧ IsSubWD a ⊥ :=
  ⟨⟨fun _ _ _ => trivial, fun _ _ => trivial⟩, ⟨fun _ v hv => by simp_all, fun v hv => by simp_all⟩⟩
end GlobalTheory.WeilDeligne.PrimDecomp


