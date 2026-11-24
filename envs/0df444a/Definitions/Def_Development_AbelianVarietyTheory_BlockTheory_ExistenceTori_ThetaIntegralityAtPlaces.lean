-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ThetaIntegralityAtPlaces
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ThetaIntegralityAtPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:34.854908+00:00
-- url     : https://prove2.me/theorems/b446b79d-1465-435c-a28a-1edf3d46c9be
-- title:
--   Theta Integrality At Places
-- statement:
--   Definitions and structural lemmas for Theta Integrality At Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ThetaIntegralityAtPlaces.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def badInt (E : Type) [Field E] [NumberField E] : ℕ := 2 * (NumberField.discr E).natAbs
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def Admissible (l : Level H) {n : ℕ} (Λ : GenLat E n) (N : ℕ) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt (badInt E) ∧ Λ.TrivAt l.M ∧ Λ.LevOK N l.M
def IsBeta (Dw : Datum H) (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β
def IsThValue (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) {n : ℕ}
    (phat : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab (fun q => (Nat.card (Fin n → LevQ Dw l) : c.F) * phat q) Λ β N P y v
def GoodPlace (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (ℓ N : ℕ) : Prop :=
  ℓ.Prime ∧ (ℓ : 𝓞 c.F) ∈ la.asIdeal ∧ Nat.Coprime ℓ l.M ∧ Nat.Coprime ℓ (badInt E) ∧ Nat.Coprime N ℓ
def ThIntegralAt (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (phat : (Fin n → LevQ Dw l) → c.F)
    (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ),
    Admissible l Λ N → IsBeta Dw c Λ β → GoodPlace c la ℓ N → Λ.TrivAt ℓ →
    P ∈ harmL c Λ a → (∀ q, la.valuation c.F (phat q) ≤ 1) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      (∀ (τ : E →+* ℂ) (x : 𝓞 E), io (embK c τ x) ∈ (algebraMap T.V T.Fr).range) →
      ∀ (y : IntFr Xo c T io), y.IsAlg → ∀ v : T.Fr,
        (letI := io.toAlgebra; IsThValue Xo c nab phat Λ β N P y.1 v) → 0 ≤ nval T.V e v
end
def ThIntegral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c),
    IsNab Xo c nab → ThIntegralAt Xo c nab
example (E : Type) [Field E] [NumberField E] (n k : ℕ) : GenLat.TrivAt (⟨stdLat E n⟩ : GenLat E n) k :=
  ⟨1, Nat.coprime_one_left k, by simp, by simp⟩
example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (la : HeightOneSpectrum (𝓞 c.F)) (ℓ N : ℕ) (h : GoodPlace c la ℓ N) : ℓ ≠ 2 := by
  rintro rfl
  have := h.2.2.2.1
  exact absurd (Nat.Coprime.eq_one_of_dvd this (Dvd.intro _ rfl)) (by decide)
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces


