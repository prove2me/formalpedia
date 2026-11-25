-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:35.194622+00:00
-- url     : https://prove2.me/theorems/0b69c2d0-5934-49df-a9b9-0c621919eaba
-- title:
--   Of Kills One
-- statement:
--   Definitions and structural lemmas for Of Kills One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
def Fr.InFF (R : Fr l O) (m : ℕ) (up : ℕ → Fin R.e → Bool) (b : ℕ → Fin R.e → ℕ) (Sn : ℕ)
    (f : R.EE) : Prop :=
  (∃ a : O⟦X⟧, R.ι (∏ s ∈ Finset.range m, ∏ τ, if up s τ then R.pt s τ ^ b s τ else 1) * f = R.ι a) ∧
    ∀ s < m, ∀ τ, up s τ = false → R.ConstMod (R.pt s τ) ((b s τ : ℤ) + Sn) f
def Sys.InXNL (S : Sys R n r) (c' : ZMod n) (m : ℕ) (Λ : O⟦X⟧) (g : Fin r → R.EE) : Prop :=
  Sys.InMul X (R.N0 r) (Λ • g) ∧ S.InNN c' m g
def Sys.InIL (S : Sys R n r) (c' : ZMod n) (m : ℕ) (Λ : O⟦X⟧) (g : Fin r → R.EE) : Prop :=
  Λ • g ∈ R.N0 r ∧ S.InXNL c' m Λ (R.γv g - g)
structure Typed {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Fin R.e → Bool)
    (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  good : F.Good
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m
def lamC (l H : ℕ) : ℝ := Real.logb l (2 * H) + 1
def aC (l H : ℕ) : ℕ := ⌊(H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l H⌋₊
def EC (l h Sn η : ℕ) : ℕ := ⌊(3 * aC l (h + η) + Sn + 2 * η : ℝ) / (l - 1) + lamC l (h + η)⌋₊
def secondSignatureConstant (l H : ℕ) : ℕ := 2 * H / (l - 1) ^ 2 + 1
def cDC (l H : ℕ) : ℕ := (H + 1) / (l - 1) + 1
def MC (l h : ℕ) : ℕ := h / (l - 1) + 1
def sigC (l h η : ℕ) : ℕ := (MC l h + η) / (l - 1) + 1
def e2C (l h Sn η : ℕ) : ℕ :=
  ⌊(h : ℝ) / (l * (l - 1)) + (Sn + 1 : ℝ) / (l - 1) + Sn + EC l h Sn η + 2 * secondSignatureConstant l (h + η) + 3 +
    lamC l (h + η)⌋₊
structure CHyp {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (b : ZMod n → ℕ) (Sn η m h : ℕ) :
    Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  even : Even n
  typed : Typed F (fun i _ => decide (Odd i.val)) (fun i _ => b i) Sn η m h
  big : ∀ i, 2 * ((h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l (h + η)) + η + 1 ≤ b i
  half : ∀ i, h ≤ 2 * b i
  kills : ∀ i, F.Kills i (R.E ^ aC l (h + η))
def SgB (l h w Sn η : ℕ) : ℝ := (h : ℝ) / (l : ℝ) ^ 2 + (w + Sn + η : ℝ) / l + Real.logb l (2 * h) + 1
def Band (l : ℕ) {n : ℕ} (sz : ZMod n → ℕ) (b w h Sn η : ℕ) (Cb : ℝ) : Prop :=
  ∃ i, sz i ≤ w ∧ (b ≤ sz (i + 1) ∨ b ≤ sz (i - 1)) ∧
    |(l * sz i : ℝ) - b| ≤ Cb * (l * η + l * Sn + (b : ℝ) / l + sz i + l * Real.logb l (2 * h))
def MB (l h : ℕ) : ℕ := 2 * h / (l - 1) + 1
def sigB (l h G : ℕ) : ℕ := ⌈((2 * G + MB l h : ℕ) : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊
def rrB (l h w Sn η : ℕ) : ℕ :=
  ⌊2 * (w + Sn + η : ℝ) / l + 2 * h / (l : ℝ) ^ 2 + 2 * Real.logb l (2 * h) + 3⌋₊
def Fr.LamB (R : Fr l O) (m G h : ℕ) : O⟦X⟧ := R.pp m (fun s => if s + 1 = m then G else h)
structure BHyp {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Bool)
    (sz : ZMod n → ℕ) (b w Sn η m h : ℕ) (A ρ : ZMod n → ℕ) : Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  typed : Typed F (fun i _ => up i) (fun i _ => sz i) Sn η m h
  w_pos : 1 ≤ w
  small : 20 * w ≤ b ∧ 20 * η ≤ b ∧ 20 * Sn ≤ b
  thick_or : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) ∨ sz i ≤ w
  some_thin : ∃ i, sz i ≤ w
  h_def : ((∃ i, b ≤ sz i) → h = b + η + Sn) ∧ ((∀ i, sz i ≤ w) → h = w + Sn)
  killX : ∀ i, F.Kills i (X ^ A i)
  killL : ∀ i, F.Kills i ((l : O⟦X⟧) ^ ρ i)
  killCut : ∀ i, sz (i + 1) ≤ w → F.Kills i ((l : O⟦X⟧) ^ rrB l h w Sn η)
  A_le : ∀ i, (A i : ℝ) ≤ (h + η : ℝ) / (l - 1) + 1
  a_le : ∀ i, (A i + ρ i : ℝ) ≤ (h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l (2 * h)
  A_next : ∀ i, (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 5 / 2 * SgB l h w Sn η
  A_cut : ∀ i, sz (i + 2) ≤ w → (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 2 * SgB l h w Sn η
def ArcLifts {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Fin R.e → Bool)
    (b : ZMod n → Fin R.e → ℕ) (Sn : ℕ) (c' : ZMod n) (m : ℕ) (Λ : O⟦X⟧) (e : ℕ) : Prop :=
  ∀ (f : R.EE) (a : Fin r → O),
    R.InFF m (fun s => up (c' + ((m - s : ℕ) : ZMod n))) (fun s => b (c' + ((m - s : ℕ) : ZMod n))) Sn f →
    (∀ s < m, ∀ τ, up (c' + ((m - s : ℕ) : ZMod n)) τ = true →
      R.toD a ∈ S.FilArc c' m s τ (b (c' + ((m - s : ℕ) : ZMod n)) τ)) →
    F.LiftsAt c' m Λ e (f • R.cst a)
structure TypedOnto {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S)
    (up : ZMod n → Fin R.e → Bool) (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  onto : F.Onto
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m
structure CSet {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (b : ZMod n → ℕ) (Sn η m h : ℕ) :
    Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  n_pos : 0 < n
  even : Even n
  typed : TypedOnto F (fun i _ => decide (Odd i.val)) (fun i _ => b i) Sn η m h
  big : ∀ i, 2 * ((h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lamC l (h + η)) + η + 1 ≤ b i
  half : ∀ i, h ≤ 2 * b i
structure BSet {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Bool)
    (sz : ZMod n → ℕ) (b w Sn η m h : ℕ) : Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  n_pos : 0 < n
  typed : TypedOnto F (fun i _ => up i) (fun i _ => sz i) Sn η m h
  w_pos : 1 ≤ w
  small : 20 * w ≤ b ∧ 20 * η ≤ b ∧ 20 * Sn ≤ b
  thick_or : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) ∨ sz i ≤ w
  some_thin : ∃ i, sz i ≤ w
  h_def : ((∃ i, b ≤ sz i) → h = b + η + Sn) ∧ ((∀ i, sz i ≤ w) → h = w + Sn)
def AltWord {n : ℕ} (up : ZMod n → Bool) (sz : ZMod n → ℕ) (b : ℕ) : Prop :=
  (∀ i, up (i + 1) = !up i) ∧ ∀ i, ¬ (b ≤ sz i ∧ b ≤ sz (i + 1) ∧ b ≤ sz (i + 2))
def OneWord {n : ℕ} (up : ZMod n → Bool) (sz : ZMod n → ℕ) (b ρ : ℕ) : Prop :=
  (∀ i j, up i = up j) ∧ 1 ≤ ρ ∧ ∀ i, ∃ k < ρ, sz (i + (k : ZMod n)) < b
def cW (l H : ℕ) : ℕ := ⌈1 + Real.logb l (H + 1)⌉₊
def eW (l H : ℕ) : ℕ := ⌈(H : ℝ) * l / ((l : ℝ) - 1) ^ 2⌉₊ + cW l H
def CokBound {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (Hw : ZMod n → ℕ) (H : ℕ) : Prop :=
  ∃ s : ZMod n → ℕ, (∀ i, s i ≤ H) ∧
    (∀ i, (s (i - 1) : ℝ) ≤ Hw i + cW l H + 3 + (s i : ℝ) / (l - 1)) ∧
    (∀ i, F.Kills i (X ^ ⌈(s i : ℝ) / (l - 1)⌉₊)) ∧
    ∀ i, F.Kills i ((l : O⟦X⟧) ^ (⌊(s i : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ + cW l H))
def CutBounds {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (sz : ZMod n → ℕ)
    (w Sn η h : ℕ) (A ρ : ZMod n → ℕ) : Prop :=
  (∀ i, F.Kills i (X ^ A i)) ∧ (∀ i, F.Kills i ((l : O⟦X⟧) ^ ρ i)) ∧
  (∀ i, sz (i + 1) ≤ w → F.Kills i ((l : O⟦X⟧) ^ rrB l h w Sn η)) ∧
  (∀ i, (A i : ℝ) ≤ (h + η : ℝ) / (l - 1) + 1) ∧
  (∀ i, (A i + ρ i : ℝ) ≤
    (h + η : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l (2 * h)) ∧
  (∀ i, (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 5 / 2 * SgB l h w Sn η) ∧
  ∀ i, sz (i + 2) ≤ w → (A i : ℝ) ≤ (sz (i + 1) + Sn + η : ℝ) / l + 2 * SgB l h w Sn η
def s1C (l h Sn η : ℕ) : ℕ :=
  ⌊(2 * aC l (h + η) + 2 * η + Sn : ℝ) / (l - 1) + lamC l (h + η)⌋₊
def eTotC (l h Sn η : ℕ) : ℕ :=
  s1C l h Sn η + 2 * sigC l h η + e2C l h Sn η + Sn + EC l h Sn η + secondSignatureConstant l (h + η)
def kapB (l m Sn h : ℕ) : ℕ :=
  ⌊(m : ℝ) + m * (m + 1) * Sn + m * ((Sn : ℝ) / (l - 1) + Real.logb l (2 * h))⌋₊
section Rel
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}
end Rel
example : AltWord (n := 2) (fun i => decide (i = 1)) (fun i => if i = 1 then 20 else 1) 20 := by
  unfold AltWord; decide
example : OneWord (n := 3) (fun _ => true) (fun i => if i = 0 then 1 else 20) 20 3 ∧
    ¬ OneWord (n := 3) (fun _ => true) (fun i => if i = 0 then 1 else 20) 20 2 := by
  unfold OneWord; decide
example (up : ZMod 3 → Bool) (sz : ZMod 3 → ℕ) (b : ℕ) : ¬ AltWord up sz b := by
  rintro ⟨h, -⟩
  have h0 : up 1 = !up 0 := h 0
  have h1 : up 2 = !up 1 := h 1
  have h2 : up 0 = !up 2 := h 2
  revert h0 h1 h2
  cases up 0 <;> cases up 1 <;> cases up 2 <;> simp
example : cW 11 10 = 2 := by
  unfold cW
  have : Real.logb ((11 : ℕ) : ℝ) (((10 : ℕ) : ℝ) + 1) = 1 := by
    norm_num
  rw [this]; norm_num
example : secondSignatureConstant 11 100 = 3 ∧ cDC 11 100 = 11 ∧ MC 11 100 = 11 ∧ sigC 11 100 0 = 2 ∧
    MB 11 100 = 21 := by decide
end GlobalTheory.NB


