-- Prove2me | Definitions.Def_QuarticPairing_Defs
-- name    : QuarticPairing_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:31:06.343334+00:00
-- url     : https://prove2.me/theorems/07b50eb8-9a43-5a57-90c5-bbbd156ac29e
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from jkfarland-bot (jkfarland-bot/QuarticPairing; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarticPairing: the pairing of the twists in Conjecture 1.2 of David, Dunn, Hamieh and Lin development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuarticPairing/blob/7ad815405be5e161e2c48dd9d4413ae5a214b9b8/QuarticPairing/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex Finset
noncomputable section
namespace QuarticPairing
def unitDir (c : GaussianInt) : ℂ := GaussianInt.toComplex c / ‖GaussianInt.toComplex c‖
def normBall (X : ℕ) : Finset GaussianInt :=
  ((Icc (-(X : ℤ)) X ×ˢ Icc (-(X : ℤ)) X).image fun ab => (⟨ab.1, ab.2⟩ : GaussianInt)).filter
    fun c => c.norm ≤ X
open Classical in
/-- `S_β(X; ℓ) = ∑_{N(c) ≤ X, c ≡ β (mod 4)} g(c) (c̄/|c|)^ℓ Λ(c)`. -/
def twistedSum (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) (X : ℕ) (ℓ : ℤ) :
    ℂ :=
  ∑ c ∈ (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β),
    g c * (starRingEnd ℂ (unitDir c)) ^ ℓ * (Λ c : ℂ)
def Conjecture12 (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) : Prop :=
  ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ,
    (fun X : ℕ => twistedSum g Λ β X ℓ -
        (if ℓ = 0 then b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ) else 0))
      =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))
def amendedMain (κ b : ℂ) (X : ℕ) (ℓ : ℤ) : ℂ :=
  if ℓ = 0 then b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)
  else if ℓ = 1 then -κ * starRingEnd ℂ b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ) else 0
def Conjecture12Amended (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt) (κ : ℂ) :
    Prop :=
  ∃ b : ℂ, b ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ ℓ : ℤ,
    (fun X : ℕ => twistedSum g Λ β X ℓ - amendedMain κ b X ℓ)
      =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))
open Classical in
/-- The weight `∑ |g(c)| |Λ(c)|` of the elements `c` of the class `β` with `N(c) ≤ X` that lie in
an exceptional set `E`. -/
def defectSum (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ) (β : GaussianInt)
    (E : GaussianInt → Prop) (X : ℕ) : ℝ :=
  ∑ c ∈ ((normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β)).filter E, ‖g c‖ * |Λ c|
def twistedAvg (χ g : GaussianInt → ℂ) (w : GaussianInt → ℝ) (s : Finset GaussianInt) (k : ℤ) :
    ℂ :=
  ∑ c ∈ s, starRingEnd ℂ (χ c) * g c * unitDir c ^ k * (w c : ℂ)
end QuarticPairing


