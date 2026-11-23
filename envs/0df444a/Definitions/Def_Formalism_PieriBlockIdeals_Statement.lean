-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- name    : Formalism_PieriBlockIdeals_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:28.628942+00:00
-- url     : https://prove2.me/theorems/1fdd7b71-ed64-423d-863d-82644a55a5c3
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/Statement.lean

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
open Finset Polynomial
namespace Formalism.CohomologicalDescent
open Classical
def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l
def diagBinom (R : Type) [CommRing R] (n : ℕ) : (Fin (n + 1) → R) →ₗ[R] (Fin (n + 1) → R) :=
  LinearMap.pi fun i => ((n.choose i : ℕ) : R) • LinearMap.proj i
def BinomialDiagonalCokernel : Prop :=
  ∀ (R : Type) [CommRing R] (l n : ℕ), l.Prime → (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    ∀ y : Fin (n + 1) → R, (l : R) ^ maxVal l n • y ∈ LinearMap.range (diagBinom R n)
def CompTwo : Prop :=
  ∀ (R : Type) [CommRing R] (A B C : Type) [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (l : R) (a b : ℕ),
    (∀ y : B, l ^ a • y ∈ LinearMap.range f) → (∀ z : C, l ^ b • z ∈ LinearMap.range g) →
    ∀ z : C, l ^ (a + b) • z ∈ LinearMap.range (g ∘ₗ f)
def ValuationProdBound : Prop :=
  ∀ (l H : ℕ) (s : Finset ℕ), l.Prime → (∀ x ∈ s, 0 < x ∧ x ≤ H) →
    (padicValNat l (∏ x ∈ s, x) : ℝ) ≤ (H : ℝ) / ((l : ℝ) - 1)
def ValuationProdBoundInt : Prop :=
  ∀ (l H : ℕ) (s : Finset ℤ), l.Prime → H < l ^ 2 → (∀ x ∈ s, x ≠ 0 ∧ |x| ≤ (H : ℤ)) →
    (padicValInt l (∏ x ∈ s, x) : ℝ) ≤ (H : ℝ) / ((l : ℝ) - 1) + 6
def ContentColumn : Prop :=
  ∀ (r p : ℕ) (lam tau : ℕ → ℕ), Antitone lam → Antitone tau → (∀ a, lam a ≤ tau a) →
    (∀ col : ℕ, ((Finset.range r).filter (fun a => lam a ≤ col ∧ col < tau a)).card ≤ p) →
    ∀ c : ℤ, ((Finset.range r).filter
      (fun a => (lam a : ℤ) ≤ (a : ℤ) + c ∧ (a : ℤ) + c < (tau a : ℤ))).card ≤ p
def ContentsBelow : Prop :=
  ∀ (r w : ℕ) (lam tau : ℕ → ℕ), Antitone lam → Antitone tau → (∀ a, lam a ≤ tau a) →
    lam 0 ≤ w → 0 < r → (∀ a < r, ¬ (lam a ≤ a + w ∧ a + w < tau a)) →
    ∀ a < r, ∀ col : ℕ, lam a ≤ col → col < tau a → (col : ℤ) - (a : ℤ) < (w : ℤ)
def vl (l : ℕ) (n : ℤ) : ℕ := padicValInt l n
def IlInd (l : ℕ) (xm xp mB : ℤ) : ℝ :=
  if ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB then 1 else 0
def d0 (l : ℕ) (D : ℤ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)}
def labelLHS (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - mB) : ℝ)) +
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)
def labelSumBound (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))
def LabelSum : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → 0 ≤ mB → mB < xm → xm ≤ xp →
    xp ≤ (h : ℤ) → h < l ^ 2 → l ≤ 2 * h →
    labelLHS l k t i xm xp mB ≤ labelSumBound l k t h i xm xp mB
def LabelSumNeedsLe : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → 0 ≤ mB → mB < xm → xm ≤ xp →
    xp ≤ (h : ℤ) → h < l ^ 2 →
    labelLHS l k t i xm xp mB ≤ labelSumBound l k t h i xm xp mB
def Linkage : Prop :=
  ∀ (l : ℕ) (K : Type) [Field K] [CharP K l] (N : ℕ) (U U' : Fin N → ℤ) (c : ℤ), l.Prime →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    Multiset.map (fun a => ((U a : ℤ) : ZMod l)) Finset.univ.val =
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val
def mwCount (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) : ℕ :=
  ((U.filter (fun u => u ∉ Finset.Icc b (b + t - 1))).filter
    (fun u => ∃ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ), x ≡ u [ZMOD (l : ℤ)])).card
def KapSum : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) (kap : Fin t → ℤ), 0 < l → t + 2 * κ < l →
    (∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ U) → (∀ s, |kap s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kap s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun u : ℤ => (u : ZMod l)) U.val →
    |∑ s, kap s| ≤ (mwCount l b t κ U : ℤ) * ((t : ℤ) + 2 * κ)
def WEArith : Prop :=
  ∀ (k j t q l h κ mw mwp : ℕ) (U U' : Fin (k + j + t + q) → ℤ) (kc kp : ℤ),
    StrictAnti U → StrictAnti U' → (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) →
    ∑ a, U a = ∑ a, U' a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * kp - kc →
    |kc| ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) → |kp| ≤ (mwp : ℤ) * ((t : ℤ) + 2 * κ) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h + ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ)
def Telescope : Prop :=
  ∀ (T : Type) [CommRing T] (P : Type) [AddCommGroup P] [Module T P] (f : ℕ)
    (F : ℕ → Submodule T P) (l : T) (c : ℕ → ℕ),
    (∀ τ < f, ∀ x ∈ F (τ + 1), l ^ c τ • x ∈ F τ) →
    ∀ x ∈ F f, l ^ (∑ τ ∈ Finset.range f, c τ) • x ∈ F 0
def ExpIndex : Prop :=
  ∀ (R : Type) [CommRing R] (L : Type) [AddCommGroup L] [Module R L] [Module.Free R L]
    [Module.Finite R L] (L' : Submodule R L) (l : R) (J : ℕ),
    Finite (R ⧸ Ideal.span {l ^ J}) → (∀ x : L, l ^ J • x ∈ L') →
    Nat.card (L ⧸ L') ≤ Nat.card (R ⧸ Ideal.span {l ^ J}) ^ Module.finrank R L
def ExpIndexSub : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (L : Type) [AddCommGroup L]
    [Module R L] [Module.Free R L] [Module.Finite R L] (L' Z : Submodule R L) (l : R) (J : ℕ),
    Finite (R ⧸ Ideal.span {l ^ J}) → (∀ x : L, l ^ J • x ∈ L') →
    Nat.card (Z ⧸ L'.comap Z.subtype) ≤ Nat.card (R ⧸ Ideal.span {l ^ J}) ^ Module.finrank R Z
def GatedSum : Prop :=
  ∀ (D h : ℕ) (L A k : ℝ) (P : Finset ℕ), 1 ≤ D → D ≤ h → 0 ≤ A → 0 ≤ k → (h : ℝ) < L ^ 2 →
    1 ≤ L → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, (if ((d0 l D : ℕ) : ℤ) < (D : ℤ) then min k (A / (d0 l D : ℝ)) else 0) *
        Real.log (l : ℝ) ≤
      A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ)
def SharperSize : Prop :=
  ∀ (k m h : ℕ), 1 ≤ m → m ≤ k → 1 ≤ h →
    ∑ d ∈ Finset.Icc 1 h, min (k : ℝ) (((m : ℝ) * h) / d) ≤
      ((m : ℝ) * h) * (1 + Real.log ((k : ℝ) / m))
def SharperSizeNeedsMleK : Prop :=
  ∀ (k m h : ℕ), 1 ≤ m → 1 ≤ k → 1 ≤ h →
    ∑ d ∈ Finset.Icc 1 h, min (k : ℝ) (((m : ℝ) * h) / d) ≤
      ((m : ℝ) * h) * (1 + Real.log ((k : ℝ) / m))
end Formalism.CohomologicalDescent


