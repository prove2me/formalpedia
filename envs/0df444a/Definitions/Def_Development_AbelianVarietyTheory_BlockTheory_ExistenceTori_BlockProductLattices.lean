-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:23.022802+00:00
-- url     : https://prove2.me/theorems/0d02810a-7682-42d4-a254-6e00d97f49e6
-- title:
--   Block Product Lattices
-- statement:
--   Definitions and structural lemmas for Block Product Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/BlockProductLattices.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Lat
variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}
def blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) where
  La := Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))
end Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def LatOK {n : ℕ} (bad M : ℕ) (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt M
def blockDat {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F) :
    (Fin (n₁ + n₂) → LevQ Dw l) → c.F :=
  fun q => w₁ (fun b => q (Fin.castAdd n₂ b)) * w₂ (fun b => q (Fin.natAdd n₁ b))
def blockPol {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) :
    MvPolynomial (LtN Dw (n₁ + n₂)) c.F :=
  rename (fun ℓ : LtN Dw n₁ => (⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₁ *
    rename (fun ℓ : LtN Dw n₂ => (⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₂
def IndepN [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N N' : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    LatOK bad l.M Λ → Λ.LevOK N l.M → Λ.LevOK N' l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ β N' P y v' → v = v'
def BlockHarm (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPol c P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂)
def BlockVal [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F)
    (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F) (β β₁ β₂ : c.F),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ → β ≠ 0 → β₁ ≠ 0 → β₂ ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v₁ v₂ : S),
      ShortValAt Xo c nab (blockDat c w₁ w₂) (blockLat Λ₁ Λ₂) β N (blockPol c P₁ P₂) y v →
      ShortValAt Xo c nab w₁ Λ₁ β₁ N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ β₂ N P₂ y v₂ →
        algebraMap c.F S β * v = (algebraMap c.F S β₁ * v₁) * (algebraMap c.F S β₂ * v₂)
def BlockBeta (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  KPsiIn (Dw := Dw) c →
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
      (∃ ζ : c.F, (∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) ∧
        betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = ζ * (betaH (Dw := Dw) c Λ₁ * betaH (Dw := Dw) c Λ₂)) ∧
      (Λ₁.La = stdLat E n₁ → betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = betaH (Dw := Dw) c Λ₂)
def BlockProd [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  BlockHarm Dw c bad ∧ BlockVal Xo c nab bad ∧ BlockBeta Dw c bad
def LevMove [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La)
    (κ : LevQ Dw l ≃ₗ[𝓞 E] LevQ Dw l),
    LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    (∀ x : Dw.La, κ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (gM x)) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (v v' : S),
      levR (gM, gA) y y' →
      ShortValAt Xo c nab w Λ β N P y' v' →
      ShortValAt Xo c nab (fun q => w fun b => κ.symm (q b)) Λ β N P y v → v' = v
abbrev FunQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)
def funDat {n : ℕ} (φ : (Fin n → FunQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → FunQ Dw l, φ x * x0Dat c (fun b => qRep (x b)) q
def LevMoveFun [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (φ : (Fin n → FunQ Dw l) → c.F) (β : c.F) (k : Sim Dw) (κ' : FunQ Dw l ≃ₗ[𝓞 E] FunQ Dw l),
    LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    (l.M : ℤ) ∣ k.ν l.M - 1 →
    (∀ x : Dw.La, κ' (Submodule.Quotient.mk x) = Submodule.Quotient.mk (k.f l.M x)) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (v v' : S),
      levR (k.f l.M, k.f l.A) y y' →
      ShortValAt Xo c nab (funDat c φ) Λ β N P y' v' →
      ShortValAt Xo c nab (funDat c fun x => φ fun b => κ'.symm (x b)) Λ β N P y v → v' = v
def ShortLaws [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IndepN Xo c nab bad ∧ BlockProd Xo c nab bad ∧ LevMove Xo c nab bad
end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices


