-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:48.693354+00:00
-- url     : https://prove2.me/theorems/a2b56a9f-11cd-4601-9f39-4c96b1db45ef
-- title:
--   Col Dict Val C
-- statement:
--   Definitions and structural lemmas for Col Dict Val C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ColDictValC.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
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
namespace Formalism.L2.SG.Pf.ColDictPf
open Formalism.BasicNotions Matrix
open scoped ComplexOrder
section Copies
variable {ι : Type} [Fintype ι]
def tenV {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)
def CSpanV {n : ℕ} (lam : ι → DomWeight n) : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ delSq ℂ n (lam τ)) ∧ p = tenV f}
variable {n : ℕ}
def FramesV (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}
def fnOfV (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] (FramesV G → ℂ) where
  toFun P := fun y => (∏ τ, (M τ * y.1 τ).det ^ s τ) *
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P
  map_add' P Q := by funext y; simp [mul_add]
  map_smul' c P := by funext y; simp [MvPolynomial.smul_eval]; ring
def shiftOfV (lam : ι → DomWeight n) : ι → ℤ := fun τ => (lam τ).detShift
def ValCV (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : Submodule ℂ (FramesV G → ℂ) :=
  (CSpanV lam).map (fnOfV G (shiftOfV lam) 1)
end Copies
def ValCIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ, (G τ).PosDef ∨ (-G τ).PosDef) →
    ∀ (lam : ι → DomWeight n) (W : Submodule ℂ (FramesV G → ℂ)), W ≤ ValCV G lam → W ≠ ⊥ →
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
        ∀ F ∈ W, ∃ F' ∈ W, ∀ y y' : FramesV G, (∀ τ, y'.1 τ = g τ * y.1 τ) → F' y = F y') →
      W = ValCV G lam
end Formalism.L2.SG.Pf.ColDictPf


