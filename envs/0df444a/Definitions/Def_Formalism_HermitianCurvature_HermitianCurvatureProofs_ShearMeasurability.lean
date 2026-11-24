-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:48:54.354093+00:00
-- url     : https://prove2.me/theorems/bfe5fe25-8fdf-4261-a08e-cf6e51d6a134
-- title:
--   Shear Measurability
-- statement:
--   Definitions and structural lemmas for Shear Measurability, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
namespace ShearMeasurability
section Shear
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def lvl (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (n : ℕ) (x : ι → ℂ) : ι → ℂ :=
  fun q => if ρ q = n then F x q else x q
def upto (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) (n : ℕ) (x : ι → ℂ) : ι → ℂ :=
  fun q => if ρ q < n then F x q else x q
def ShearCond (ρ : ι → ℕ) (F : (ι → ℂ) → ι → ℂ) : Prop :=
  ∀ q (x y : ι → ℂ), (∀ p, ρ p < ρ q → x p = y p) → F x q - x q = F y q - y q
end Shear
section Low
variable {m : ℕ} (w : Equiv.Perm (Fin m))
def gap (q : C2.Lidx m) : ℕ := q.1.1.val - q.1.2.val
def splitEquiv : C2.Lidx m ≃ C2.LPidx w ⊕ C2.Lstidx w where
  toFun q := if h : w.symm q.1.2 < w.symm q.1.1 then Sum.inl ⟨q.1, q.2, h⟩
    else Sum.inr ⟨q.1, q.2, lt_of_le_of_ne (not_lt.mp h)
      (fun e => (ne_of_lt q.2) (w.symm.injective e).symm)⟩
  invFun := Sum.elim (fun q => ⟨q.1, q.2.1⟩) (fun q => ⟨q.1, q.2.1⟩)
  left_inv q := by
    by_cases h : w.symm q.1.2 < w.symm q.1.1 <;> simp [h]
  right_inv s := by
    rcases s with q | q
    · simp [q.2.2]
    · simp [not_lt.mpr (le_of_lt q.2.2)]
noncomputable def eSplit : (C2.Lidx m → ℂ) ≃ᵐ (C2.LPidx w → ℂ) × (C2.Lstidx w → ℂ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ => ℂ) (splitEquiv w).symm).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ))
def mulMap (p : (C2.LPidx w → ℂ) × (C2.Lstidx w → ℂ)) : C2.Lidx m → ℂ := fun q =>
  (C2.lowOf (fun q : C2.LPidx w => q.1) p.1 * C2.lowOf (fun q : C2.Lstidx w => q.1) p.2) q.1.1 q.1.2
def aX (x : C2.Lidx m → ℂ) (i k : Fin m) : ℂ :=
  if h : k < i ∧ w.symm k < w.symm i then x ⟨(i, k), h.1⟩ else 0
def bX (x : C2.Lidx m → ℂ) (k j : Fin m) : ℂ :=
  if h : j < k ∧ w.symm k < w.symm j then x ⟨(k, j), h.1⟩ else 0
end Low
end ShearMeasurability
open ShearMeasurability
end Formalism.FourierDecayAlt.P


