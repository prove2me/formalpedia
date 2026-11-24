-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:36.874661+00:00
-- url     : https://prove2.me/theorems/e6cf00f4-ab92-4ab4-8b43-64d97bade347
-- title:
--   Jac Rev
-- statement:
--   Definitions and structural lemmas for Jac Rev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/JacRev.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DualSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
def W1 : Prop := ∀ (R : Type) [CommRing R] (k M : ℕ) (a b : Fin k) (j : ℕ) (f f' : MvPolynomial (Fin k × Fin k) R),
  a ≠ b → Rel R k M f f' → Rel R k M (rowDiv R a b j f) ((-1) ^ j * rowDiv R b a j f')
def MHhw : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ), MH R (hw R (le_refl k) ν)
def MHdiv : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (a b : Fin k) (j : ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  MH R f → MH R (rowDiv R a b j f)
def Diag : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (a : Fin k) (j d : ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  IsWeightedHomogeneous (rowW a) f d → rowDiv R a a j f = (d.choose j : MvPolynomial (Fin k × Fin k) R) * f
def HomW : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (f : MvPolynomial (Fin k × Fin k) R),
  f ∈ weyl R k k (le_refl k) ν → IsHomogeneous f (degW ν)
def LowMem : Prop := ∀ (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ), low R ν ∈ weyl R k k (le_refl k) ν
def JacId : Prop := ∀ (R : Type) [CommRing R] (k s : ℕ) (hs : s + 1 ≤ k), ∃ u : R, (u = 1 ∨ u = -1) ∧
  dualSub R k (pMinor R 1 (s + 1) hs) =
    C u * (genM R k).det ^ s * pMinor R Fin.revPerm (k - 1 - s) (by omega)
def JacRev : Prop := ∀ (R : Type) [CommRing R] (k s : ℕ) (hs : s + 1 ≤ k), ∃ u : R, (u = 1 ∨ u = -1) ∧
  dualSub R k (pMinor R Fin.revPerm (s + 1) hs) =
    C u * (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega)
def W4hw : Prop := ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
  ∃ u : R, (u = 1 ∨ u = -1) ∧
    Rel R (m + 1) (expM lam) (hw R (le_refl _) (nuOf lam)) (C u * low R (nuOf (lamStar lam)))
def W4low : Prop := ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
  ∃ u : R, (u = 1 ∨ u = -1) ∧
    Rel R (m + 1) (expM lam) (low R (nuOf lam)) (C u * hw R (le_refl _) (nuOf (lamStar lam)))
def Bk : Prop := ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
  lam (Fin.last m) + lamStar lam (Fin.last m) + (degW (nuOf (lamStar lam)) : ℤ) = (expM lam : ℤ)
def EV : Prop := ∀ (K : Type) [Field K] (m : ℕ) (e e' : ℤ) (D M : ℕ)
  (F F' : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
  e + e' + (D : ℤ) = (M : ℤ) → Rel K (m + 1) M F F' → IsHomogeneous F' D →
  ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
    z.det ^ e * eval (fun x => z x.1 x.2) F =
      (revCol (z⁻¹)ᵀ).det ^ e' * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) (C (sgnK K m ^ e') * F')
def Uniq : Prop := ∀ (K : Type) [Field K] (k d : ℕ) (G : MvPolynomial (Fin k × Fin k) K),
  IsHomogeneous G d → dualSub K k G = 0 → G = 0
def DualB : Prop := ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (m : ℕ)
  (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit g.det → IsUnit g'.det →
  colSpan O g = colSpan O g' → colSpan O (g⁻¹)ᵀ = colSpan O (g'⁻¹)ᵀ
def SgnPM : Prop := ∀ (K : Type) [Field K] (m : ℕ), sgnK K m = 1 ∨ sgnK K m = -1
def GStep : Prop := ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
  (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K), IsUnit g.det →
  lam (Fin.last m) + lamStar lam (Fin.last m) + (degW (nuOf (lamStar lam)) : ℤ) = (expM lam : ℤ) →
  (∀ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)), IsHomogeneous f' (degW (nuOf (lamStar lam)))) →
  (∀ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel O (m + 1) (expM lam) f f') →
  ∀ F ∈ deltaLTw O K m lam g, ∃ F' ∈ deltaLTw O K m (lamStar lam) (g⁻¹)ᵀ,
    Rel K (m + 1) (expM lam) F F' ∧ IsHomogeneous F' (degW (nuOf (lamStar lam)))
end PI.OddDualWeyl


