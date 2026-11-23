-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:36.544617+00:00
-- url     : https://prove2.me/theorems/ae2c938a-4eb1-4852-ac8a-a0864e8034ae
-- title:
--   Unitary Det Class
-- statement:
--   Definitions and structural lemmas for Unitary Det Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UnitaryDetClass.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Lattices
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
def IsUnitary (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map (IsCMField.complexConj E)).transpose * γ = 1
def Carries (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) : Prop :=
  ∀ v' : Fin n → E, v' ∈ Λ'.La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v'
def CongrAt (Q : ℕ) (u v : Fin n → E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k Q ∧ ∀ j, ∃ s : 𝓞 E, (k : E) * (u j - v j) = (Q : E) * (s : E)
abbrev StdMod (E : Type) [Field E] [NumberField E] (n Q : ℕ) : Type :=
  Fin n → 𝓞 E ⧸ Ideal.span {(Q : 𝓞 E)}
def IsMarking (Q : ℕ) (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q) : Prop :=
  Function.Surjective κ ∧
  (∀ v : Λ.La, κ v = 0 ↔ ∃ u : Λ.La, v = Q • u) ∧
  ∀ (v w : Λ.La) (x y : Fin n → 𝓞 E),
    (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) → (∀ j, κ w j = Ideal.Quotient.mk _ (y j)) →
      ∃ s : 𝓞 E, ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j -
        ∑ j, IsCMField.complexConj E (x j : E) * (y j : E) = (Q : E) * (s : E)
def IsRepOf (bad Q : ℕ) (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q) (Λ' : GenLat E n) : Prop :=
  Λ'.TrivAt bad ∧ Λ'.TrivAt Q ∧
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUnitary γ ∧ Carries γ Λ Λ' ∧
    ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) →
      CongrAt Q (γ.mulVec v) fun j => (x j : E)
def ExistsRep (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Prop :=
  ∀ (Q bad : ℕ), 0 < Q → 0 < bad → ∀ (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q),
    Λ.Unimod → IsMarking Q Λ κ → ∃ Λ' : GenLat E n, IsRepOf bad Q Λ κ Λ'
def IsTrivRep (bad Q : ℕ) (Λ : GenLat E n) : Prop := Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt Q
def SameClass (bad Q : ℕ) (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) : Prop :=
  IsTrivRep bad Q Λ ∧ IsTrivRep bad Q Λ' ∧ IsUnitary γ ∧ Carries γ Λ Λ' ∧
    ∀ v ∈ Λ.La, CongrAt Q (γ.mulVec v) v
example : IsUnitary (1 : Matrix (Fin n) (Fin n) E) := by
  simp [IsUnitary, Matrix.map_one]
example (Λ : GenLat E n) : Carries 1 Λ Λ := fun v => by simp
example (Q : ℕ) (v : Fin n → E) : CongrAt Q v v := ⟨1, by simp, fun _ => ⟨0, by simp⟩⟩
end Lattices
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def push {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ : LtN Dw n => letB c ℓ.1 ℓ.2.1 fun k => γ k ℓ.2.2
example {n : ℕ} (ℓ : LtN Dw n) : push c (1 : Matrix (Fin n) (Fin n) E) (X ℓ) = X ℓ := by
  obtain ⟨σ, i, j⟩ := ℓ
  simp [push, letB, Matrix.one_apply, apply_ite, ite_mul]
def PushOnto (Dw : Datum H) (n : ℕ) : Prop :=
  ∀ (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) (a : (E →+* ℂ) × ℕ → ℕ),
    IsUnitary γ → Carries γ Λ Λ' → push (Dw := Dw) c γ '' harmL c Λ a = harmL c Λ' a
def IsBeta (Dw : Datum H) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β
def ThEq (nab : NabV Xo c) {n : ℕ} (ζ : c.F) (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (β : c.F)
    (Λ' : GenLat E n) (β' : c.F) : Prop :=
  ∀ (w : (Fin n → LevQ Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (N N' : ℕ),
    P ∈ harmL c Λ a → Λ.LevOK N l.M → Λ'.LevOK N' l.M →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ v : k,
      (∀ x : k, ShortValAt Xo c nab w Λ β N P y x ↔ x = v) ∧
      ∀ x : k, ShortValAt Xo c nab w Λ' β' N' (push c γ P) y x ↔ x = algebraMap c.F k ζ * v
open Classical in

def detChar {n : ℕ} (d : (E →+* ℂ) → ℤ) (γ : Matrix (Fin n) (Fin n) E) : c.F :=
  ∏ τ ∈ Finset.univ.filter (InPsi H), embF c τ γ.det ^ d τ
def RepIdentity (nab : NabV Xo c) {n : ℕ} (bad Q : ℕ) (u : GenLat E n → c.F) (d : (E →+* ℂ) → ℤ) : Prop :=
  ∀ (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n), SameClass bad Q γ Λ Λ' →
    u Λ ≠ 0 ∧ u Λ' ≠ 0 ∧
    ThEq Xo c nab (u Λ / (u Λ' * detChar c d γ)) γ Λ (betaH (Dw := Dw) c Λ) Λ' (betaH (Dw := Dw) c Λ')
open Classical in

def ScalarLaw (Dw : Datum H) {n : ℕ} (bad Q : ℕ) (u : GenLat E n → c.F) (e : (E →+* ℂ) → ℤ) : Prop :=
  u ⟨stdLat E n⟩ = betaH (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) ∧
  ∀ Λ : GenLat E n, IsTrivRep bad Q Λ →
    (∀ σ : c.F →+* ℂ, ‖σ (u Λ)‖ = 1) ∧
    Submodule.span (𝓞 c.F) {u Λ} * ∏ τ ∈ Finset.univ.filter (InPsi H), idealAt c Λ.La τ ^ (-e τ).toNat =
      ∏ τ ∈ Finset.univ.filter (InPsi H), idealAt c Λ.La τ ^ (e τ).toNat
def IsSubLevel (bad M Q : ℕ) : Prop := 0 < Q ∧ M ∣ Q ∧ ∃ j : ℕ, Q ∣ (bad * M) ^ j
def ChangeIdentity (nab : NabV Xo c) (n bad : ℕ) : Prop :=
  ∃ (Q : ℕ) (u : GenLat E n → c.F) (d : (E →+* ℂ) → ℤ), IsSubLevel bad l.M Q ∧ RepIdentity Xo c nab bad Q u d
def ChangeIdentityUnit (nab : NabV Xo c) (n bad : ℕ) : Prop :=
  ∃ (Q : ℕ) (u : GenLat E n → c.F) (e d : (E →+* ℂ) → ℤ), IsSubLevel bad l.M Q ∧
    RepIdentity Xo c nab bad Q u d ∧ ScalarLaw c Dw bad Q u e ∧ ∀ τ, InPsi H τ → e τ + d τ = 0
def RootOfUnityChange (nab : NabV Xo c) (n bad : ℕ) : Prop :=
  ∀ (γ : Matrix (Fin n) (Fin n) E) (Λ Λ' : GenLat E n) (β β' : c.F), SameClass bad l.M γ Λ Λ' →
    IsBeta c Dw Λ β → IsBeta c Dw Λ' β' →
      ∃ ζ : c.F, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ThEq Xo c nab ζ γ Λ β Λ' β'
def spanO (s : Set (Rul Xo c)) : AddSubgroup (Rul Xo c) :=
  AddSubgroup.closure {g | ∃ (o : 𝓞 c.F) (f : Rul Xo c), f ∈ s ∧ ∀ p y, g p y = algebraMap c.F p.R (o : c.F) * f p y}
def thSet (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n)
    (a : (E →+* ℂ) × ℕ → ℕ) : Set (Rul Xo c) :=
  {f | f ∈ sec Xo c a n ∧ ∃ (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), Λ.LevOK N l.M ∧ P ∈ harmL c Λ a ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
      ShortValAt Xo c nab w Λ (betaH (Dw := Dw) c Λ) N P y (evR Xo c f y)}
def SpanOfPair (nab : NabV Xo c) (n bad : ℕ) : Prop :=
  ∀ (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n l.M) (Λ₁ Λ₂ : GenLat E n),
    Λ.Unimod → IsMarking l.M Λ κ → IsRepOf bad l.M Λ κ Λ₁ → IsRepOf bad l.M Λ κ Λ₂ →
      ∀ (w : (Fin n → LevQ Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ),
        spanO Xo c (thSet Xo c nab w Λ₁ a) = spanO Xo c (thSet Xo c nab w Λ₂ a)
def shortSet {n : ℕ} (dδ : DeltaDat Xo c n) (x0 : Fin n → Dw.La) (Λ : GenLat E n)
    (a : (E →+* ℂ) × ℕ → ℕ) : Set (Rul Xo c) :=
  {f | f ∈ sec Xo c a n ∧ ∃ (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), Λ.LevOK N dδ.l₂.M ∧ P ∈ harmL c Λ a ∧
    IsShortRule Xo c dδ Λ N x0 P f}
def SpanOfPairCover {n : ℕ} (dδ : DeltaDat Xo c n) (bad : ℕ) : Prop :=
  ∀ (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n dδ.l₂.M) (Λ₁ Λ₂ : GenLat E n),
    Λ.Unimod → IsMarking dδ.l₂.M Λ κ → IsRepOf bad dδ.l₂.M Λ κ Λ₁ → IsRepOf bad dδ.l₂.M Λ κ Λ₂ →
      ∀ (x0 : Fin n → Dw.La) (a : (E →+* ℂ) × ℕ → ℕ),
        spanO Xo c (shortSet Xo c dδ x0 Λ₁ a) = spanO Xo c (shortSet Xo c dδ x0 Λ₂ a)
def HidaSetting (Dw : Datum H) (n bad : ℕ) : Prop :=
  IsGalois ℚ E ∧ Even n ∧ Odd (Dw.p + Dw.q) ∧ KPsiIn (Dw := Dw) c ∧ 0 < bad ∧
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * discr E → p ∣ bad
def ChangeOfRepresentative [StarRing (𝓞 E)] (n bad : ℕ) : Prop :=
  ExistsRep E n ∧ PushOnto c Dw n ∧
  (HidaSetting c Dw n bad →
    (∀ nab : NabV Xo c, IsNab Xo c nab →
      ChangeIdentity Xo c nab n bad ∧ ChangeIdentityUnit Xo c nab n bad ∧
      RootOfUnityChange Xo c nab n bad ∧ SpanOfPair Xo c nab n bad) ∧
    ∀ dδ : DeltaDat Xo c n, dδ.IsLev → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → SpanOfPairCover Xo c dδ bad)
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass


