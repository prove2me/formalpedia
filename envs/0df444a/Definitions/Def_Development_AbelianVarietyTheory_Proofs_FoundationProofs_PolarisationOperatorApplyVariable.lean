-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:18:42.60153+00:00
-- url     : https://prove2.me/theorems/1f25bd65-2987-4b8d-b876-4791406ed8dd
-- title:
--   Polarisation Operator Apply Variable
-- statement:
--   Definitions and structural lemmas for Polarisation Operator Apply Variable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
namespace GlobalTheory.MinorNorm
section Capelli
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
def pol (i j : Fin k) : Derivation ℂ R R := ∑ r, x r i • d r j
noncomputable def iterD (m : ℕ) : (Fin m → Fin k) → (Fin m → Fin k) → R → R :=
  Nat.rec (motive := fun m => (Fin m → Fin k) → (Fin m → Fin k) → R → R) (fun _ _ P => P)
    (fun _ f ρ J P => d (ρ 0) (J 0) (f (Fin.tail ρ) (Fin.tail J) P)) m
variable {x d}
def eps (ρ : Fin k → Fin k) : ℤ := (Matrix.of fun t s => if ρ t = s then (1 : ℤ) else 0).det
end Capelli
section Weight
variable {R : Type} [CommRing R] [Algebra ℂ R] {k : ℕ} {x : Fin k → Fin k → R}
  {d : Fin k → Fin k → Derivation ℂ R R}
end Weight
section Fock
variable {σ : Type}
end Fock
section Partition
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
def addCol (a : Fin l → ℕ) (K : Fin l) : Fin l → ℕ := fun i => a i + if i ≤ K then 1 else 0
variable {σ : Type} (v : Fin l → Fin l → σ)
def minor (i : Fin l) : MvPolynomial σ ℂ :=
  (Matrix.of fun r c : Fin (i + 1) => X (v (Fin.castLE i.2 r) (Fin.castLE i.2 c))).det
def del (a : Fin l → ℕ) : MvPolynomial σ ℂ := ∏ i, minor v i ^ (a i - nextPart a i)
variable {v}
end Partition
end GlobalTheory.MinorNorm


