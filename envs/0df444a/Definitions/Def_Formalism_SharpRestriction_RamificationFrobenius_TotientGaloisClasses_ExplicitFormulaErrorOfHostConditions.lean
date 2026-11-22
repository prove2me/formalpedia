-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:29.025417+00:00
-- url     : https://prove2.me/theorems/1fc3b820-3f47-4622-ab52-35e63d13310c
-- title:
--   Explicit Formula Error Of Host Conditions
-- statement:
--   Definitions and structural lemmas for Explicit Formula Error Of Host Conditions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.HC
structure Level extends KSet where
  o : ℕ
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0
def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)
def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even
def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True
namespace Level
variable (Λ : Level)
def ZeroFreeAbove (θ : ℝ) : Prop := ∀ ψ ∈ Λ.KEPT, ψ.ZeroFreeAbove θ
def ZeroFreeLevel : Prop := Λ.ZeroFreeAbove (1 / 2)
def IsEven : Prop := ∀ ψ ∈ Λ.KEPT, ψ.χ.Even
open Classical in

def Nt : Finset PChar := Λ.KEPT.erase PChar.one
open Classical in

def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹
def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re
def ChebyshevGrowthImpliesZeroFree : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y0 : ℝ, (∀ y ≥ y0, Λ.Gm y ≤ y ^ θ) → Λ.ZeroFreeAbove θ
end Level
theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive)
    (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl
theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  haveI : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one
theorem pchar_mk_eq_of_changeLevel_eq_of_level_eq {M d e : ℕ} [NeZero M] [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d) (φ : DirichletCharacter ℂ e)
    (hd : d ∣ M) (he' : e ∣ M) (hde : d = e) (hψ : DirichletCharacter.changeLevel hd ψ = χ)
    (hφ : DirichletCharacter.changeLevel he' φ = χ) (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) :
    PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl
theorem conductor_inv_dvd_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor ∣ χ.conductor := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹,
    by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]⟩
theorem conductor_inv_eq_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor = χ.conductor := by
  apply Nat.dvd_antisymm (conductor_inv_dvd_conductor χ)
  simpa using conductor_inv_dvd_conductor χ⁻¹
theorem PChar.of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : PChar.of χ⁻¹ = (PChar.of χ).inv := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  haveI : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_of_level_eq χ⁻¹ χ⁻¹.primitiveCharacter χ.primitiveCharacter⁻¹ χ⁻¹.conductor_dvd_level
    χ.conductor_dvd_level (conductor_inv_eq_conductor χ) χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _
open Classical in

def Level.ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem := Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  inv_mem := by
    intro ψ h
    obtain ⟨χ, h1, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨χ⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.inv_mem (Finset.mem_filter.1 h1).2⟩, PChar.of_inv χ⟩
  psK := none
  psK_spec := fun _ h => by cases h
  o := Nat.card Ξ
def Level.cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)
namespace Frame
variable (φ : Frame)
open Classical in

def lam (γ : φ.A) : ℝ := (if γ ∈ φ.A0 then 4 else 3) / (3 * (φ.o : ℝ) + 1)
open Classical in

def Shares (TT : Finset φ.A) (δ : ℝ) : Prop :=
  ∀ γ : φ.A, |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - φ.lam γ * (TT.card : ℝ)| ≤ δ * (TT.card : ℝ)
end Frame
structure EAtH (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A) (x eps C : ℝ) : Prop where
  o_eq : φ.o = Λ.o
  kept : H.KeptInXp Λ.KEPT
  ps : H.ExceptionalCharacterKept Λ.KEPT Λ.psK
  shares : φ.Shares TT (x ^ (-1 + eps))
  bdG : H.BoundedCharsPointwise Λ.KEPT x eps
  bdL : ∀ θ ∈ H.Bounded Λ.KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log x
def HType.level (T : HType) (o : ℕ) : Level := ⟨T.toKSet, o⟩
end Formalism.HC
end


