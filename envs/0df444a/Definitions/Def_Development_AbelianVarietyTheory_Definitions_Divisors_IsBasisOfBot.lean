-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsBasisOfBot
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsBasisOfBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:28.583824+00:00
-- url     : https://prove2.me/theorems/44db93bc-cf19-456e-83ce-3b7ce4816eee
-- title:
--   Is Basis Of Bot
-- statement:
--   Definitions and structural lemmas for Is Basis Of Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsBasisOfBot.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsDetEltOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
namespace GlobalTheory.DetInv
def IsBasisOf {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] {h n : ℕ}
    (L : Submodule O (Fin h → C)) (x : Fin n → Fin h → C) : Prop :=
  LinearIndependent C x ∧ Submodule.span O (Set.range x) = L
def incl {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] (h : ℕ) :
    (Fin h → O) →ₗ[O] (Fin h → C) := (Algebra.linearMap O C).compLeft (Fin h)
def eigPart {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] {Λ : Type} [CommRing Λ]
    {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (L : Submodule O (Fin h → O)) :
    Submodule O (Fin h → C) :=
  (eig C ρ τ).restrictScalars O ⊓
    (L.map (incl C h) ⊔ (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1).restrictScalars O)
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
def lieSub (D : Datum ε h Λ) (τ : Λ →+* O) : Submodule O (Fin h → C) :=
  (D.Lie ⊓ D.Tsub τ).map (incl C h)
def wQuot (D : Datum ε h Λ) (τ : Λ →+* O) : Submodule O (Fin h → C) :=
  eigPart C (actT D) τ ⊤ ⊓ (LinearMap.ker (alC C D)).restrictScalars O
def alQuot (D : Datum ε h Λ) (τ : Λ →+* O) : Submodule O (Fin h → C) :=
  (eigPart C (actT D) τ ⊤).map ((alC C D).restrictScalars O)
def filQuot (D : Datum ε h Λ) (τ : Λ →+* O) : Submodule O (Fin h → C) :=
  eigPart C (actH D) τ D.Fil
def IsShift (v : Valuation C NNReal) (D : Datum ε h Λ) (τ : Λ →+* O) (r : NNReal) : Prop :=
  ∀ (a b : ℕ) (x : Fin a → Fin h → C) (g : Matrix (Fin a) (Fin a) C)
    (m : Fin b → Fin h → C) (k : Matrix (Fin b) (Fin b) C),
    IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) (fun i => ∑ j, g i j • x j) →
    IsBasisOf C (filQuot C D τ) m → IsBasisOf C (alQuot C D τ) (fun i => ∑ j, k i j • m j) →
    v g.det * v k.det = r
end GlobalTheory.DetInv


