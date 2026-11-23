-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:25.705001+00:00
-- url     : https://prove2.me/theorems/11822011-fb1f-42cf-8bd8-8f1138685bb4
-- title:
--   Iwahori Factorisation
-- statement:
--   Definitions and structural lemmas for Iwahori Factorisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
def IsUU {m : ℕ} (U : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)
def IsLU {m : ℕ} (L : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)
def border {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O) :
    Matrix (Fin (n+1)) (Fin (n+1)) O := fun i j =>
  Fin.lastCases (motive := fun _ => O) (Fin.lastCases (motive := fun _ => O) x row j)
    (fun i' => Fin.lastCases (motive := fun _ => O) (col i') (A i') j) i
section
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]
end
end GlobalTheory.UnipotentBorder


