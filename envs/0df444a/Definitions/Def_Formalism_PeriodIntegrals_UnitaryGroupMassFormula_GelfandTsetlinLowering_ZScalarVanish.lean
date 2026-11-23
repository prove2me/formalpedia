-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:57.568262+00:00
-- url     : https://prove2.me/theorems/61097d4d-8bdf-4408-a40f-9c0ee8b14a2c
-- title:
--   ZScalar Vanish
-- statement:
--   Definitions and structural lemmas for ZScalar Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ZScalarVanish.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions MvPolynomial
def IsEqv {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
  ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)
def LastWeight {n N : ℕ} (lam : DomWeight N) (sg : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  ∀ (a : ℂˣ), ∀ s ∈ nablaSq ℂ n sg,
    sqAct ℂ N lam (lastGL ℂ N a) (φ s) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • φ s
def zScalar {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (Rset h lam sg i).erase (sg.w i), ∏ j : Fin n, ((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ))
def Numbers : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    cBr h lam sg ≠ 0 ∧ |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg ∧
    degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg
def ZScalarVanish : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n), Interlace h lam sg →
    Interlace h lam mu → mu.w ≠ sg.w → wsum mu = wsum sg → zScalar h lam sg mu = 0
def XiFacts : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    xi ℂ h lam sg ≠ 0 ∧ xi ℂ h lam sg ∈ nablaSq ℂ N lam ∧
    (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg) ∧
    (∀ t : Fin n → ℂˣ, sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) (xi ℂ h lam sg) =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • xi ℂ h lam sg) ∧
    (∀ a : ℂˣ, sqAct ℂ N lam (lastGL ℂ N a) (xi ℂ h lam sg) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg) ∧
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ,
      ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1)
def IoExists : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 ∧ io0 (extremal ℂ n sg) = xi ℂ h lam sg ∧ LastWeight lam sg io0
def IoIntegral : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg → LastWeight lam sg io0 →
      ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
        io0 (((cBr h lam sg : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) s) =
          MvPolynomial.map (Int.castRingHom ℂ) f
def CapelliZ : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∃ Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      (∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
        Z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f') ∧
      ∀ (mu : DomWeight n), Interlace h lam mu →
        ∀ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ, IsEqv h mu lam φ →
          ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s
def OtherPart {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ⨆ (mu : DomWeight n) (_ : Interlace h lam mu) (_ : mu.w ≠ sg.w) (_ : wsum mu = wsum sg)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (_ : IsEqv h mu lam φ),
    (nablaSq ℂ n mu).map φ
def LiftMod : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg → LastWeight lam sg io0 →
      ∀ s ∈ nablaSq ℤ n sg, ∃ m ∈ nablaSq ℤ N lam,
        MvPolynomial.map (Int.castRingHom ℂ) m - io0 (MvPolynomial.map (Int.castRingHom ℂ) s) ∈ OtherPart h lam sg
def BrRest {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) : Prop :=
  (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) ∧
  (∃ f ∈ delSq ℂ N lam, br f ≠ 0) ∧
  (∀ (g : GL (Fin n) ℂ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (embGL ℂ n N h g) f) = sqAct ℂ n sg g (br f)) ∧
  (∀ (a : ℂˣ), ∀ f ∈ delSq ℂ N lam,
    br (sqAct ℂ N lam (lastGL ℂ N a) f) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • br f) ∧
  (∀ f ∈ delSq ℂ N lam,
    (normFock sg (br f) (br f)).re ≤ brBd h lam sg ^ 2 * (normFock lam f f).re)
def AdjointBr : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h sg lam io → io (extremal ℂ n sg) = ((cBr h lam sg : ℤ) : ℂ) • xi ℂ h lam sg →
      LastWeight lam sg io →
      (∀ s ∈ nablaSq ℂ n sg, (normFock lam (io s) (io s)).re ≤ brBd h lam sg ^ 2 * (normFock sg s s).re) ∧
      ∃ br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ,
        BrRest h lam sg br ∧ IsTranspose lam sg io br
def BrIntegral : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
      (∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
        io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f) →
      (∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam) →
      (∀ f ∈ delSq ℂ N lam, br f ∈ delSq ℂ n sg) →
      IsTranspose lam sg io br →
      ∀ f ∈ delSq ℤ N lam, ∃ g ∈ delSq ℤ n sg,
        br (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) g
end PI.WGL


