-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QuotSetU
-- name    : Formalism_PeriodIntegrals_QuotSetU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:34.715403+00:00
-- url     : https://prove2.me/theorems/9fed5477-6cf5-4bce-b7e2-b05f06863609
-- title:
--   Quot Set U
-- statement:
--   Definitions and structural lemmas for Quot Set U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QuotSetU.lean

import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI
namespace QuotSetU
def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)
def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}
def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩
def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩
def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0
def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1
def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0
def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re
def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}
def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}
def Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | ∃ h ∈ UWset k r z, ∃ m ∈ Nset k r, s = h * m}
end QuotSetU
open QuotSetU in

def QuotSetU : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsMatGroup (UH (Hpk k r)) ∧ IsMatGroup (Sset k r z) ∧ Sset k r z ⊆ UH (Hpk k r) ∧
    (∀ μG : Measure (MtM (2 * r + k + 1)), IsHaarOnM (UH (Hpk k r)) μG → IsRightInvM (UH (Hpk k r)) μG) ∧
    (∀ μS : Measure (MtM (2 * r + k + 1)), IsHaarOnM (Sset k r z) μS → IsRightInvM (Sset k r z) μS)
end PI
end


