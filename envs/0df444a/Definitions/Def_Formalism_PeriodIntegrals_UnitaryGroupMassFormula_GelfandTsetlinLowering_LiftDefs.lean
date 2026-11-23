-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:26.442169+00:00
-- url     : https://prove2.me/theorems/17ea5387-63bd-47cd-a353-eb5669303e89
-- title:
--   Lift Defs
-- statement:
--   Definitions and structural lemmas for Lift Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def eRow {n N : ℕ} (h : n + 1 = N) (a : Fin n) : Fin N := ⟨a.1, by omega⟩
def lastW (N : ℕ) : Fin N × Fin N → ℕ := fun v => if v.1.1 + 1 = N then 1 else 0
def dLast {n N : ℕ} (lam : DomWeight N) (mu : DomWeight n) : ℕ := (degZ lam mu - lam.detShift).toNat
def liftWt {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) : Fin N → ℕ :=
  fun a => if ha : a.1 < n then ω ⟨a.1, ha⟩ + (mu.detShift - lam.detShift).toNat else dLast lam mu
def liftWord {n N : ℕ} (h : n + 1 = N) (w : List (Fin n × Fin n × ℕ)) : List (Fin N × Fin N × ℕ) :=
  w.map fun x => (eRow h x.1, eRow h x.2.1, x.2.2)
def OffDiag {r : ℕ} (w : List (Fin r × Fin r × ℕ)) : Prop := ∀ x ∈ w, x.1 ≠ x.2.1
def tupCnt {n K : ℕ} {sz : Fin K → ℕ} (I : ∀ k, Fin (sz k) → Fin n) (a : Fin n) : ℕ :=
  ∑ k, (Finset.univ.filter fun p : Fin (sz k) => I k p = a).card
def EqvDiv : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ s ∈ nablaSq ℂ n mu,
      φ (rowDiv ℂ a b k s) = rowDiv ℂ (eRow h a) (eRow h b) k (φ s)
def EqvRowWt : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ (ω : Fin n → ℕ), ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (rowW n n) s ω →
      IsWeightedHomogeneous (rowW N N) (φ s) (liftWt h lam mu ω)
def EqvLast : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n), Interlace h lam mu →
    ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, IsWeightedHomogeneous (lastW N) (φ s) (dLast lam mu)
def Decomp : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) ≠ 0 →
      ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
        ∃ u ∈ nablaSq ℂ n sg, f - io0 u ∈ OtherPart h lam sg
def ZComm : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
    (∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∃ z : ℂ, ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) →
    (∀ f ∈ nablaSq ℂ N lam, Z f ∈ nablaSq ℂ N lam) ∧
    (∀ (a b : Fin n), a ≠ b → ∀ (k : ℕ), ∀ f ∈ nablaSq ℂ N lam,
      Z (rowDiv ℂ (eRow h a) (eRow h b) k f) = rowDiv ℂ (eRow h a) (eRow h b) k (Z f)) ∧
    (∀ (ω : Fin N → ℕ), ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (rowW N N) f ω →
      IsWeightedHomogeneous (rowW N N) (Z f) ω)
def FockDetect : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (io0 : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      IsEqv h sg lam io0 → io0 (extremal ℂ n sg) = xi ℂ h lam sg →
      ∀ u ∈ nablaSq ℂ n sg,
        (∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
          Formalism.REAL.fockF (applyWord ℂ (liftWord h w) (io0 u)) (xi ℂ h lam sg) = 0) →
        io0 u = 0
def TupleCore : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∃ M : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℤ,
      (∀ I, M I ∈ nablaSq ℤ N lam ∧
        IsWeightedHomogeneous (rowW N N) (M I) (liftWt h lam sg (tupCnt I)) ∧
        IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I)) ∧
      (∀ I, ∀ w : List (Fin n × Fin n × ℕ), OffDiag w →
        ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
          applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
          applyWord ℤ (liftWord h w) (M I) = d.sum (fun J c => c • M J)) ∧
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ M J = ε • xi ℤ h lam sg) ∧
      (∃ J0, tupCnt J0 = sg.natW ∧ bideterminant ℤ sz hsz J0 = extremal ℤ n sg ∧ M J0 = xi ℤ h lam sg)
end PI.WGL


