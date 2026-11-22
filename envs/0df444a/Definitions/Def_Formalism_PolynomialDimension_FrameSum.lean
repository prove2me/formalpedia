-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_FrameSum
-- name    : Formalism_PolynomialDimension_FrameSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:11.759278+00:00
-- url     : https://prove2.me/theorems/0afdf0df-7f69-4c5e-90c1-efcb5a180e1e
-- title:
--   Frame Sum
-- statement:
--   Definitions and structural lemmas for Frame Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/FrameSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Formalism.CountingSumsFrames
def LocTelescope : Prop :=
  ∀ (p J n' : ℕ) (z : ℕ → ℕ), (∀ j < J, z j ≤ z (j + 1)) → z J = z 0 + n' →
    (∑ j ∈ range J, (p : ℤ) ^ z j * ((p : ℤ) ^ (z (j + 1) - z j) - 1) = (p : ℤ) ^ z 0 * ((p : ℤ) ^ n' - 1)) ∧
      ∏ j ∈ range J, p ^ (z (j + 1) - z j) = p ^ n'
def swapCol (r k : ℕ) (h : r ≤ k) (i : Fin r) (c : Fin k) : Fin r → Fin k :=
  Function.update (Fin.castLE h) i c
abbrev IIdx (r k : ℕ) := Fin r × {c : Fin k // r ≤ c.val}
def GraphMinor : Prop :=
  ∀ (F : Type) [Field F] (r k : ℕ) (h : r ≤ k) (H : Matrix (Fin r) (Fin k) F),
    (H.submatrix id (Fin.castLE h)).det ≠ 0 → (∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ H i c ≠ 0) →
      ∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ (H.submatrix id (swapCol r k h i c)).det ≠ 0
def frameRow (p r k : ℕ) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A) (a : ℕ) (t : Fin r → A) :
    Fin k → A :=
  t ᵥ* H.map (fun x => x ^ p ^ a)
def piMinor (p r k : ℕ) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A) (pos : Fin r → ℕ)
    (t : Fin r → Fin r → A) (zj : ℕ) (cols : Fin r → Fin k) : A :=
  (Matrix.of fun l c' => (frameRow p r k H (pos l) (t l) (cols c')) ^ p ^ (zj - pos l)).det
def localizer (p r k J : ℕ) (h : r ≤ k) {A : Type} [CommRing A] (H : Matrix (Fin r) (Fin k) A)
    (pos : ℕ → Fin r → ℕ) (t : ℕ → Fin r → Fin r → A) (z : ℕ → ℕ) : A :=
  piMinor p r k H (pos 0) (t 0) (z 0) (Fin.castLE h) *
    ∏ I : IIdx r k,
      (∏ j ∈ range J, piMinor p r k H (pos j) (t j) (z j) (Fin.castLE h) ^ (p ^ (z (j + 1) - z j) - 1) -
        ∏ j ∈ range J, piMinor p r k H (pos j) (t j) (z j) (swapCol r k h I.1 I.2.1) ^ (p ^ (z (j + 1) - z j) - 1))
def LocalizerVanishes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p] (n' r k J : ℕ) (h : r ≤ k),
    Fintype.card F = p ^ n' →
    ∀ z : ℕ → ℕ, (∀ j < J, z j ≤ z (j + 1)) → z J = z 0 + n' →
    ∀ (pos : ℕ → Fin r → ℕ), (∀ j < J, ∀ l, pos j l ≤ z j) →
    ∀ H : Matrix (Fin r) (Fin k) F, (∃ (i : Fin r) (c : Fin k), r ≤ c.val ∧ H i c ≠ 0) →
    ∀ (A : Type) [CommRing A] [Algebra F A] (t : ℕ → Fin r → Fin r → A),
      localizer p r k J h (H.map (algebraMap F A)) pos t z = 0
def LocExpand : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (J : ℕ) (Del : ℕ → R) (piI : ι → ℕ → R)
    (Q : ℕ → ℕ), 1 ≤ J →
    Del 0 * ∏ I, (∏ j ∈ range J, Del j ^ (Q j - 1) - ∏ j ∈ range J, piI I j ^ (Q j - 1)) =
      ∑ S : Finset ι, (-1) ^ S.card *
        (∏ j ∈ range J, Del j ^ ((if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1))) *
          ∏ I ∈ S, ∏ j ∈ range J, piI I j ^ (Q j - 1)
def NormalMinor : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (r k : ℕ) (h : r ≤ k) (M : Matrix (Fin r) (Fin k) R),
    (∀ (i : Fin r) (c : Fin k), r ≤ c.val → M i c ∈ I) →
      ∀ (i : Fin r) (c : Fin k), r ≤ c.val → (M.submatrix id (swapCol r k h i c)).det ∈ I
def borderedMatrix {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R) (T : Matrix (Fin r) (Fin r) R)
    (b : Fin r → R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of (Fin.cons (α := fun _ => Fin (r + 1) → R) (Fin.snoc (α := fun _ => R) ts u)
    (fun l => Fin.snoc (α := fun _ => R) (T l) (b l)))
def BorderedDetLinear : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (ts : Fin r → R) (T : Matrix (Fin r) (Fin r) R),
    ∃ c : Fin r → R, ∀ (u : R) (b : Fin r → R),
      (borderedMatrix r ts u T b).det = (-1) ^ r * u * T.det + ∑ l, b l * c l
def DetMulEqSumAdjugate : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (T : Matrix (Fin r) (Fin r) R) (s : Fin r → R) (a : Fin r),
    T.det * s a = ∑ l, (T *ᵥ s) l * T.adjugate a l
def KeyVanish : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] (r k : ℕ) (h : Matrix (Fin k) (Fin k) F),
    IsUnit h.det → ∀ s : ℕ,
    (∀ (A : Fin (r + 1) → ℕ) (t : Fin (r + 1) → Fin k → F) (cols : Fin (r + 1) → Fin k),
      (∀ l, A l ≤ s) → (∀ l (i : Fin k), r ≤ i.val → t l i = 0) →
        (Matrix.of fun l c => ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)).det = 0) ∧
    (∀ (a : ℕ) (t v : Fin k → F), a ≤ s → (∀ i : Fin k, r ≤ i.val → t i = 0) → (∀ i : Fin k, i.val < r → v i = 0) →
      ∑ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) *
        (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) c = 0)
def CleanInduction : Prop :=
  ∀ (M : Type) [AddCommGroup M] (Deg : AddSubgroup M) (FF FF' : ℕ → AddSubgroup M), Antitone FF → Antitone FF' →
    ∀ (τ : Type) (level : τ → ℕ) (spare : τ → ℤ × ℤ) (sym raw : τ → M) (o c' Q : ℕ),
    (∀ x, sym x ∈ Deg ∧ raw x ∈ Deg) →
    (∀ x, sym x ∈ FF (level x)) →
    (∀ x, raw x ∈ FF' (level x + c')) →
    (∀ x, level x < o + c' →
      (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - level x) ≤ (spare x).1 → ((o : ℤ) + c' - 1 - level x) ≤ (spare x).2 →
        ∃ (ch : Finset τ) (ρ : M), ρ ∈ FF (o + c') ∧ ρ ∈ Deg ∧ raw x - sym x = ∑ y ∈ ch, sym y + ρ ∧
          ∀ y ∈ ch, level x < level y ∧ level y < o + c' ∧
            spare y = ((spare x).1 - (2 * (Q : ℤ) + 1) * ((level y : ℤ) - level x),
              (spare x).2 - ((level y : ℤ) - level x))) →
    ∀ S : Finset τ, (∀ x ∈ S, o ≤ level x ∧ spare x = ((((2 * Q + 3) * c' : ℕ) : ℤ), (c' : ℤ))) →
      ∃ f : M, f ∈ Deg ∧ f - ∑ x ∈ S, sym x ∈ FF (o + c') ∧ f ∈ FF' (o + c')
def CleanArith : Prop :=
  (∀ (j v o e' Q : ℕ), j + v = o + e' → o ≤ 2 * Q → 1 ≤ e' → j ≤ (2 * Q + 1) * e') ∧
    (∀ (e c' Q : ℕ), e < c' → (2 * Q + 1) * e ≤ (2 * Q + 3) * c' ∧ e ≤ c')
def PowerSplit : Prop :=
  ∀ (R : Type) [CommRing R] (D h π : R) (P n c : ℕ), 1 ≤ P →
    (D ^ P + π * h) ^ n ∈ Ideal.span {D ^ (n - c)} ⊔ Ideal.span {π ^ c}
def Lemma4Geom : Prop :=
  ∀ (p a B : ℝ) (D0 : ℕ) (S : Finset ℕ) (d : ℕ → ℝ), 13 ≤ p → 0 < a → a / p ^ D0 ≤ B →
    (∀ m ∈ S, 1 ≤ m ∧ 0 ≤ d m ∧ d m ≤ 2.02 * a / p ^ (D0 + 2 * m)) →
      ∑ m ∈ S, d m ≤ 2.02 * B / (p ^ 2 - 1) ∧ 2.02 * B / (p ^ 2 - 1) ≤ B / 80
def Lemma4Arith : Prop :=
  ∀ (B B' sl mstar val : ℝ), 0 ≤ B → B' ≤ B / 80 → sl ≤ B / 100 → mstar ≤ sl → B / 2 - sl ≤ val →
    B / 4 + mstar ≤ val - B' ∧ mstar ≤ B / 4
def Lemma4Count : Prop :=
  ∀ (N1 ntops m kQ c' al : ℕ), ntops ≤ N1 →
    ntops * (m + kQ + c') + (c' * al + 2 * c') ≤ (N1 + 1) * (m + kQ + c' * al + 3 * c')
def factProd {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : ℕ := ∏ i, (α i).factorial
def vG {σ : Type} (p : ℕ) (F : MvPolynomial σ ℚ) : WithTop ℝ :=
  F.support.inf fun α => (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ)
def vBB {σ : Type} [Fintype σ] (p : ℕ) (F : MvPolynomial σ ℚ) : WithTop ℝ :=
  F.support.inf fun α =>
    ((((padicValRat p (F.coeff α) : ℤ) : ℝ) + (padicValNat p (factProd α) : ℝ) / 2 : ℝ) : WithTop ℝ)
def IsLetterHom {σ Z : Type} [Fintype σ] [DecidableEq Z] (letter : σ → Z) (d : Z → ℕ)
    (F : MvPolynomial σ ℚ) : Prop :=
  ∀ α ∈ F.support, ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z
def FockGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ Z : Type) [Fintype σ] [DecidableEq σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ), 0 ≤ a →
    Fintype.card σ ≤ N * k → (∀ z, (d z : ℝ) ≤ 2 * a) →
    ∀ F : MvPolynomial σ ℚ, IsLetterHom letter d F →
      vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 -
          (N * k * (Real.logb p (2 * a + k) + 1)) / 2 : ℝ) : WithTop ℝ) ≤ vBB p F ∧
        vBB p F ≤ vG p F + (((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2 : ℝ) : WithTop ℝ)
def FrameSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Z : Type) [Fintype Z] [DecidableEq Z] (Fr : Finset Z) (r N k : ℕ) (a : ℝ)
    (d : Z → ℕ) (M : Z → Fin r → ℕ), 0 ≤ a →
    Fr.card ≤ N → r + 1 ≤ k → (∀ z, (d z : ℝ) ≤ 2 * a) → (∀ z ∈ Fr, ∑ i, M z i ≤ d z) →
      (∀ z ∈ Fr, (padicValNat p ((d z).factorial / ((d z - ∑ i, M z i).factorial * ∏ i, (M z i).factorial)) : ℝ) ≤
          (r + 1) * (Real.logb p (2 * a + k) + 1)) ∧
      2 * ((padicValNat p (∏ z, (d z).factorial) : ℝ) / 2) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        2 * ((padicValNat p (∏ z, (if z ∈ Fr then d z - ∑ i, M z i else d z).factorial) : ℝ) / 2) +
          (padicValNat p (∏ z ∈ Fr, ∏ i, (M z i).factorial) : ℝ)
end Formalism.CountingSumsFrames


