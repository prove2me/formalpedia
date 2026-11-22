-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_StatementHar
-- name    : Formalism_PolynomialDimension_StatementHar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:35.874613+00:00
-- url     : https://prove2.me/theorems/41308077-cbd1-4ed9-8f65-3c35a8c12212
-- title:
--   Statement Har
-- statement:
--   Definitions and structural lemmas for Statement Har, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/StatementHar.lean

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
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
abbrev XY (k : ℕ) : Type := Fin k ⊕ Fin k
abbrev PolXY (K : Type) [Field K] (k : ℕ) : Type := MvPolynomial (XY k) K
def xDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inl i)
def yDeg {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∑ i : Fin k, m (Sum.inr i)
def xFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inl i)).factorial
def yFact {k : ℕ} (m : XY k →₀ ℕ) : ℕ := ∏ i : Fin k, (m (Sum.inr i)).factorial
variable (K : Type) [Field K] (k : ℕ)
def hXY : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * X (Sum.inr i)
def ctrF : PolXY K k →ₗ[K] PolXY K k :=
  ∑ i : Fin k, (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap ∘ₗ
    (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap
def hDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • LinearMap.mulLeft K (hXY K k ^ l)
def ctrDiv (l : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((l.factorial : K)⁻¹) • (ctrF K k ^ l)
def PolAB (A B : ℕ) : Submodule K (PolXY K k) where
  carrier := {f | ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B}
  zero_mem' := by
    intro m hm
    simp at hm
  add_mem' := by
    intro f g hf hg m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hf m h
    · exact hg m h
  smul_mem' := by
    intro c f hf m hm
    exact hf m (MvPolynomial.support_smul hm)
def HarAB (A B : ℕ) : Submodule K (PolXY K k) := PolAB K k A B ⊓ LinearMap.ker (ctrF K k)
def harProj (A B : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ∑ l ∈ range (min A B + 1),
    ((-1 : K) ^ l / (((A + B + k - 2).choose l : ℕ) : K)) • (hDiv K k l ∘ₗ ctrDiv K k l)
def levelProj (A B j : ℕ) : PolXY K k →ₗ[K] PolXY K k :=
  ((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹) •
    (hDiv K k j ∘ₗ harProj K k (A - j) (B - j) ∘ₗ ctrDiv K k j)
def fischer (f g : PolXY K k) : K :=
  ∑ m ∈ f.support, ((xFact m : K) * (yFact m : K)) * (coeff m f * coeff m g)
variable {K k}
def glAct (g : GL (Fin k) K) : PolXY K k →ₐ[K] PolXY K k :=
  aeval (Sum.elim
    (fun i : Fin k => ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j))
    (fun i : Fin k => ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)))
def GaussLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, coeff m f ∈ R}
def FockLat (R : Subring K) : Set (PolXY K k) := {f | ∀ m, (xFact m : K) * coeff m f ∈ R}
def DualLat (R : Subring K) : Set (PolXY K k) :=
  {f | ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ∈ R}
def SqrtFockLat (R : Subring K) : Set (PolXY K k) :=
  {f | ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ^ 2 ∈ R}
def SqrtGaussLat (R : Subring K) (n : ℕ) : Set (PolXY K k) := {f | ∀ m, (n : K) * coeff m f ^ 2 ∈ R}
def latOf (g : GL (Fin k) K) (S : Set (PolXY K k)) : Set (PolXY K k) := glAct g '' S
def PLocal (R : Subring K) (p : ℕ) : Prop := ∀ n : ℕ, ¬ p ∣ n → ((n : K))⁻¹ ∈ R
def SlTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ctrF K k (hXY K k * f) - hXY K k * ctrF K k f = ((A + B + k : ℕ) : K) • f
def SlTwoPower : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b i : ℕ), 1 ≤ k → ∀ w : PolXY K k, w ∈ HarAB K k a b →
    ctrF K k (hXY K k ^ (i + 1) * w) = (((i + 1) * (a + b + k + i) : ℕ) : K) • (hXY K k ^ i * w)
def DivPowerEigen : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b : ℕ), 1 ≤ k → ∀ w : PolXY K k, w ∈ HarAB K k a b →
    (∀ i l : ℕ, hDiv K k l (ctrDiv K k l (hXY K k ^ i * w)) =
        ((i.choose l * (a + b + k + i - 1).choose l : ℕ) : K) • (hXY K k ^ i * w)) ∧
    (∀ j : ℕ, ctrDiv K k j (hDiv K k j w) = (((a + b + k + j - 1).choose j : ℕ) : K) • w)
def FischerAdjoint : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (f g : PolXY K k),
    fischer K k (hXY K k * f) g = fischer K k f (ctrF K k g)
def CtrSurj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k → ∀ g : PolXY K k, g ∈ PolAB K k A B →
    ∃ f ∈ PolAB K k (A + 1) (B + 1), ctrF K k f = g
def HarDecomp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k → ∀ f : PolXY K k, f ∈ PolAB K k A B →
    ∃! w : Fin (min A B + 1) → PolXY K k,
      (∀ j : Fin (min A B + 1), w j ∈ HarAB K k (A - (j : ℕ)) (B - (j : ℕ))) ∧
        f = ∑ j : Fin (min A B + 1), hXY K k ^ (j : ℕ) * w j
def HarDim : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k' A B : ℕ),
    Module.finrank K (PolAB K (k' + 1) A B) = (A + k').choose k' * (B + k').choose k' ∧
    Module.finrank K (HarAB K (k' + 1) (A + 1) (B + 1)) + (A + k').choose k' * (B + k').choose k' =
      (A + 1 + k').choose k' * (B + 1 + k').choose k' ∧
    HarAB K (k' + 1) A 0 = PolAB K (k' + 1) A 0 ∧ HarAB K (k' + 1) 0 B = PolAB K (k' + 1) 0 B
def HarProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B →
      harProj K k A B f ∈ HarAB K k A B ∧
      ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g) ∧
    (∀ f : PolXY K k, f ∈ HarAB K k A B → harProj K k A B f = f) ∧
    (1 ≤ A → 1 ≤ B → ∀ g : PolXY K k, g ∈ PolAB K k (A - 1) (B - 1) →
      harProj K k A B (hXY K k * g) = 0)
def LevelProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B : ℕ), 1 ≤ k →
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ j ≤ min A B,
      ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ i ≤ min A B, ∀ j ≤ min A B,
      levelProj K k A B i (levelProj K k A B j f) = if i = j then levelProj K k A B j f else 0) ∧
    (∀ i ≤ min A B, ∀ j ≤ min A B, ∀ w : PolXY K k, w ∈ HarAB K k (A - i) (B - i) →
      levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0)
def Canonical : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (g : GL (Fin k) K),
    glAct g (hXY K k) = hXY K k ∧
    (∀ f : PolXY K k, ctrF K k (glAct g f) = glAct g (ctrF K k f)) ∧
    (∀ (A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B → glAct g f ∈ PolAB K k A B) ∧
    (∀ (A B : ℕ) (f : PolXY K k), harProj K k A B (glAct g f) = glAct g (harProj K k A B f)) ∧
    (∀ (A B j : ℕ) (f : PolXY K k), levelProj K k A B j (glAct g f) = glAct g (levelProj K k A B j f))
def FockStable : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (R : Subring K) (g : GL (Fin k) K) (l : ℕ) (f : PolXY K k),
    f ∈ latOf g (FockLat R) →
      hDiv K k l f ∈ latOf g (FockLat R) ∧ ctrDiv K k l f ∈ latOf g (FockLat R)
def SqrtFockStable : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K) (l : ℕ)
    (f : PolXY K k), f ∈ latOf g (SqrtFockLat O.toSubring) →
      hDiv K k l f ∈ latOf g (SqrtFockLat O.toSubring) ∧ ctrDiv K k l f ∈ latOf g (SqrtFockLat O.toSubring)
def BinomVal : Prop :=
  ∀ p : ℕ, p.Prime →
    (∀ n m : ℕ, padicValNat p (n.choose m) ≤ Nat.log p n) ∧
    (∀ k A B l j : ℕ, 1 ≤ k → l ≤ min A B → j ≤ min A B →
      (padicValNat p ((A + B + k - 2).choose l) : ℝ) ≤ Real.logb p ((A : ℝ) + B + k) ∧
      (padicValNat p ((A + B + k - 2 * j + j - 1).choose j) : ℝ) ≤ Real.logb p ((A : ℝ) + B + k)) ∧
    (∀ k A B a l j : ℕ, 1 ≤ k → A ≤ 8 * a → B ≤ 8 * a → l ≤ min A B → j ≤ min A B →
      (padicValNat p ((A + B + k - 2).choose l) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + k - 1) + 1 ∧
      (padicValNat p ((A + B + k - 2 * j + j - 1).choose j) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + k - 1) + 1)
def FockProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) →
      ((p : K) ^ Nat.log p (A + B + k)) • harProj K k A B f ∈ latOf g (FockLat R) ∧
      ∀ j ≤ min A B,
        ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (FockLat R)
def SqrtFockProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p →
    ∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (SqrtFockLat O.toSubring) →
      ((p : K) ^ Nat.log p (A + B + k)) • harProj K k A B f ∈ latOf g (SqrtFockLat O.toSubring) ∧
      ∀ j ≤ min A B,
        ((p : K) ^ (2 * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (SqrtFockLat O.toSubring)
def FockGaussXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (FockLat R) → (A.factorial : K) • f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ latOf g (FockLat R))
def SqrtFockGaussXY : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (SqrtFockLat O.toSubring) →
        f ∈ latOf g (SqrtGaussLat O.toSubring (A.factorial * B.factorial))) ∧
      (f ∈ latOf g (SqrtGaussLat O.toSubring (A.factorial * B.factorial)) →
        ((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f ∈ latOf g (SqrtFockLat O.toSubring))
def GaussProj : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → ∀ f : PolXY K k, f ∈ PolAB K k A B →
      (f ∈ latOf g (GaussLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (GaussLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (DualLat R) →
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f ∈ latOf g (DualLat R) ∧
        ∀ j ≤ min A B,
          ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • levelProj K k A B j f ∈ latOf g (DualLat R))
def GaussProjText : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B a p e : ℕ) (R : Subring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal R p → A ≤ 8 * a → B ≤ 8 * a →
    3 * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) + 4 * (k : ℝ) * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) ≤ (e : ℝ) →
    ∀ f : PolXY K k, f ∈ PolAB K k A B → ∀ j ≤ min A B,
      (f ∈ latOf g (GaussLat R) → ((p : K) ^ e) • levelProj K k A B j f ∈ latOf g (GaussLat R)) ∧
      (f ∈ latOf g (DualLat R) → ((p : K) ^ e) • levelProj K k A B j f ∈ latOf g (DualLat R))
def GaussLemmaH : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K) (j : ℕ)
    (G : PolXY K k), 1 ≤ k →
      hXY K k ^ j * G ∈ latOf g (GaussLat O.toSubring) → G ∈ latOf g (GaussLat O.toSubring)
def HPrime : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ), 2 ≤ k → Prime (hXY F k)
def LevelLattice : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k a b j : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K), 1 ≤ k →
    latOf g (GaussLat O.toSubring) ∩ {f | ∃ w ∈ HarAB K k a b, f = hXY K k ^ j * w} =
      (fun w => hXY K k ^ j * w) '' (latOf g (GaussLat O.toSubring) ∩ (HarAB K k a b : Set (PolXY K k)))
def HarQuot : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k A B p : ℕ) (O : ValuationSubring K) (g : GL (Fin k) K),
    1 ≤ k → p.Prime → PLocal O.toSubring p →
    (∀ w G : PolXY K k, w ∈ HarAB K k A B → w = hXY K k * G → w = 0) ∧
    (∀ f : PolXY K k, f ∈ PolAB K k A B → f ∈ latOf g (GaussLat O.toSubring) →
      ∃ w ∈ HarAB K k A B, ∃ G ∈ PolAB K k (A - 1) (B - 1),
        w ∈ latOf g (GaussLat O.toSubring) ∧ G ∈ latOf g (GaussLat O.toSubring) ∧
        ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • f = w + hXY K k * G)
end Formalism.CountingSumsFrames


