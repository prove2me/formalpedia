-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
-- name    : Formalism_PolynomialDimension_DigitSumValuationBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:23.562807+00:00
-- url     : https://prove2.me/theorems/8070c439-4aad-4942-a235-34faf3e1000d
-- title:
--   Digit Sum Valuation Bound
-- statement:
--   Definitions and structural lemmas for Digit Sum Valuation Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/DigitSumValuationBound.lean

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
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
open Finset
namespace Formalism.CountingSumsFrames
def lgSeg (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1
def kapSeg (p : ℕ) (a : ℝ) (r s : ℕ) : ℝ := 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r
def firstDepth (t : ℕ) (Y κ : ℝ) : ℝ := (t : ℝ) * (Y * κ + κ) + κ
def initialExponent (p : ℕ) (a : ℝ) (r s t : ℕ) : ℝ :=
  (r : ℝ) * lgSeg p a r + (t : ℝ) * ((r : ℝ) + 1) * lgSeg p a r + (2 * (s : ℝ) + 2) * ((r : ℝ) - 1) * lgSeg p a r
def uSeg (p : ℕ) (a : ℝ) (r t : ℕ) : ℝ := ((t : ℝ) + 1) * ((r : ℝ) + 1) * lgSeg p a r
def DjSeg (p N r s t : ℕ) (Y a : ℝ) : ℝ :=
  ((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ) + 3 * ((s : ℝ) + 1) * lgSeg p a r + 2 * uSeg p a r t +
    kap0I p N (r + 1) a
def epsSeg (S Y' κ lg E : ℝ) : ℝ := 2 * S / Y' + (2 * κ + 2 * S * lg / Y') / E
def epsPlusSeg (J Yp La0 lg E' : ℝ) : ℝ := J / Yp + (La0 + J * lg / Yp) / E'
def SbdSeg (p : ℕ) (a b' P : ℝ) : ℝ := (4 * a / (p : ℝ) ^ 2 + 2 * b') / P
def dimMM (r A0 : ℕ) {s : ℕ} (A C : Fin s → ℕ) : ℕ := dimPol r A0 * ∏ i, (dimPol r (A i) * dimPol r (C i))
def HypSeg (p N N₁ k : ℕ) (Y a b' Q La : ℝ) : Prop :=
  1 ≤ Y ∧ (k : ℝ) ^ 2 * Y ^ 2 ≤ p ∧
  (k : ℝ) * Y ^ 2 * Real.log a ≤ a / b' ∧
  N ≤ k ∧ N₁ ^ 4 ≤ k ∧ Real.log a ≤ k ∧ 0 ≤ La ∧ La ≤ k ∧
  (k : ℝ) ^ 3 * Q * Y ≤ b' ∧ b' ≤ a ∧
  (p : ℝ) < a / b' ∧
  3 ≤ k ∧ 1 ≤ N ∧ 1 ≤ N₁ ∧ 1 ≤ Q ∧ 0 < b'
def HypSegOfHypI : Prop :=
  ∀ C C₀ : ℝ, 1 ≤ C → 1 ≤ C₀ →
    ∀ (p N N₁ k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ),
      HypI C C₀ p N N₁ k n' G' Y Yb a b' Ib cl D cStar →
      HypSeg p N N₁ k Y a b' ((p : ℝ) ^ G') (C₀ * (N₁ : ℝ) ^ 2 * Real.log a) ∧
      a + a / (k * Y) ≤ 2 * a ∧
      ∀ bLo bHi : ℝ, bLo ≤ b' → b' ≤ bHi → bHi - bLo = Ib → b' / 2 ≤ bLo ∧ bHi ≤ 3 * b' / 2
def SegLg : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    1 < Real.logb p a ∧ 2 < lgSeg p a r ∧ lgSeg p a r ≤ Real.logb p a + 3 ∧
    lgSeg p a r ≤ 4 * Real.logb p a ∧ Real.logb p a ≤ Real.log a ∧ lgSeg p a r ≤ 4 * ((r : ℝ) + 1)
def SegDegreeSum : Prop :=
  ∀ (p s : ℕ) (P : Fin s → ℝ) (A C : Fin s → ℕ) (a ap b' : ℝ) (i : Fin s), 2 ≤ p → 0 ≤ a → ap ≤ 2 * a →
    (∀ l, 0 < P l) → (∀ l, l < i → (p : ℝ) ^ (2 * ((i : ℕ) - (l : ℕ))) * P i ≤ P l) →
    (∀ l, (C l : ℝ) ≤ ap / P l) → (∀ l, (A l : ℝ) ≤ 3 * b' / (2 * P l)) →
    (((∑ l ∈ univ.filter (fun l => l < i), C l) + (∑ l ∈ univ.filter (fun l => l ≤ i), A l) : ℕ) : ℤ) ≤
      ⌊SbdSeg p a b' (P i)⌋
def SegTermsAboveS : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    4 * b' + ((r : ℝ) + 1) * Q ≤ a * (1 - 4 / (p : ℝ) ^ 2) ∧
    ∀ (P : ℝ) (C A j : ℕ), 1 ≤ P → P ≤ Q → a / P - ((r : ℝ) + 1) ≤ C → (A : ℝ) ≤ 3 * b' / (2 * P) → j ≤ A →
      ⌊SbdSeg p a b' P⌋ ≤ (C : ℤ) - j
def SegWindowClass : Prop :=
  ∀ a n P sg : ℕ, 0 < P → sg ≤ a →
    ∃ c Y' : ℕ, ((Ico a (a + n)).filter (fun x => x % P = sg % P)).image (fun x => (x - sg) / P) = Ico c (c + Y') ∧
      ((Ico a (a + n)).filter (fun x => x % P = sg % P)).card = Y' ∧ n / P ≤ Y' ∧ Y' ≤ n / P + 1
def SegNoShortWindow : Prop :=
  ∀ (p N N₁ r a : ℕ) (Y b' Q La : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    ((r : ℝ) + 1) ^ 2 * Q ≤ (a : ℝ) / (((r : ℝ) + 1) * Y) ∧
    ∀ P : ℕ, 1 ≤ P → (P : ℝ) ≤ Q →
      P ≤ ⌊(a : ℝ) / (((r : ℝ) + 1) * Y)⌋₊ + 1 ∧
      ∀ Y' : ℕ, (⌊(a : ℝ) / (((r : ℝ) + 1) * Y)⌋₊ + 1) / P ≤ Y' →
        1 ≤ Y' ∧ (a : ℝ) / (2 * ((r : ℝ) + 1) * Y * P) ≤ Y'
def SegShortWindowNoTie : Prop :=
  ∀ (p k : ℕ) (Y a b' P : ℝ), 1 ≤ Y → 2 ≤ k → (k : ℝ) ^ 2 * Y ^ 2 ≤ p → 0 < b' →
    (k : ℝ) * Y ^ 2 * Real.log a ≤ a / b' → 4 < Real.log a → a / (k * Y) < P →
    ⌊SbdSeg p a b' P⌋ = 0
def SegEps : Prop :=
  ∀ (p N N₁ r s : ℕ) (Y a b' Q La P S Y' : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    0 < P → 0 ≤ S → S ≤ SbdSeg p a b' P → a / (2 * ((r : ℝ) + 1) * Y * P) ≤ Y' →
    S / Y' ≤ 12 / Y ∧ S * lgSeg p a r / Y' ≤ 48 / Y ∧ 48 ≤ kapSeg p a r s ∧
    epsSeg S Y' (kapSeg p a r s) (lgSeg p a r) (Y * kapSeg p a r s) ≤ 28 / Y
def SegEpsPlus : Prop :=
  ∀ (p N N₁ r s t : ℕ) (Y a b' Q La J Yp : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La → t ≤ s →
    0 ≤ J → J ≤ 3 * b' / 2 → a / (((r : ℝ) + 1) * Y) ≤ Yp →
    firstDepth t Y (kapSeg p a r s) ≤ 2 * ((t : ℝ) + 1) * Y * kapSeg p a r s ∧
    J / Yp ≤ 2 / (Y * Real.log a) ∧ J * lgSeg p a r / Yp ≤ 8 / Y ∧
    initialExponent p a r s t + lgSeg p a r ≤ kapSeg p a r s - 1 ∧
    ((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) + lgSeg p a r ≤ kapSeg p a r s ∧
    epsPlusSeg J Yp (((⌈initialExponent p a r s t⌉ : ℤ) : ℝ) + firstDepth t Y (kapSeg p a r s) + lgSeg p a r) (lgSeg p a r)
      (((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ) + 1) ≤ 5 / Y
def SegDepth : Prop :=
  ∀ (p N N₁ r s t : ℕ) (Y a b' Q La : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La → t ≤ s → s ≤ N₁ →
    kapSeg p a r s ≤ 9 * N₁ * ((r : ℝ) + 1) ^ 2 * lgSeg p a r ∧
    Y * firstDepth t Y (kapSeg p a r s) ≤ 36 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r ∧
    3 * ((s : ℝ) + 1) * lgSeg p a r + 2 * uSeg p a r t ≤ kapSeg p a r s ∧
    DjSeg p N r s t Y a ≤ 45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a
def SegDepthSum : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    ∀ (Jn : ℕ) (s t : Fin Jn → ℕ), Jn ≤ N → (∀ j, t j ≤ s j ∧ s j ≤ N₁) →
      ∑ j, DjSeg p N r (s j) (t j) Y a ≤ 182 * N * Y ^ 2 * ((r : ℝ) + 1) ^ 3 * Real.logb p a
def SegKap0 : Prop :=
  ∀ (p N N₁ r s : ℕ) (Y a b' Q La ap : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La → s + 1 ≤ N →
    a ≤ ap → ap ≤ a * (1 + 2 / (((r : ℝ) + 1) * Y)) →
    (2 * (s : ℝ) + 2) * (r : ℝ) * Real.logb p ap ≤ kap0I p N (r + 1) a
def SegSTopRoom : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La P Qj A0 sg C : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    0 < P → P ≤ Q → (p : ℝ) * P ≤ Qj → A0 ≤ a / Qj → sg ≤ 2 * La * A0 / ((r : ℝ) + 1) →
    a / P - ((r : ℝ) + 1) < C →
    sg ≤ 2 / 9 * (a / P) ∧ 8 / 9 * (a / P) ≤ a / P - ((r : ℝ) + 1) ∧ sg ≤ C
def SegmentTopRoom : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La P A c o : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    0 < P → 0 ≤ A → A ≤ 3 * b' / (2 * P) → c ≤ a / (p * P) + (3 * b' / 2) / (((p : ℝ) ^ 2 - 1) * P) →
    o ≤ A * (1 + 4 / (p : ℝ) ^ 2) + La * c / ((r : ℝ) + 1) →
    A * (1 + 4 / (p : ℝ) ^ 2) ≤ 0.25 * (a / P) ∧
    a / (p * P) + (3 * b' / 2) / (((p : ℝ) ^ 2 - 1) * P) ≤ 0.12 * (a / P) ∧ o ≤ 0.37 * (a / P)
def SegSize : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La ap P : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La → ap ≤ 2 * a → 1 ≤ P →
    ap + 3 * b' / 2 + r + 1 ≤ 8 * a + r ∧ 2 * (ap + 3 * b' / 2) ≤ 8 * a ∧ a + 2 ≤ 8 * a ∧
    3 * b' / 2 + 1 ≤ 8 * a ∧ 2 * SbdSeg p a b' P + 1 ≤ 8 * a ∧
    ∀ n : ℕ, (n : ℝ) ≤ 8 * a + r → (Nat.clog p n : ℝ) ≤ lgSeg p a r
def BinomRatioExp : Prop :=
  ∀ r x x' : ℕ, 1 ≤ x → x ≤ x' →
    (dimPol r x' : ℝ) ≤ Real.exp ((r : ℝ) * ((x' : ℝ) - x) / x) * dimPol r x
def SegWindowRatio : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La P : ℝ) (C C' : ℕ), HypSeg p N N₁ (r + 1) Y a b' Q La → 1 ≤ P → P ≤ Q →
    a / P - ((r : ℝ) + 1) ≤ C → a / P - ((r : ℝ) + 1) ≤ C' →
    (C : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y)) / P → (C' : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y)) / P →
    (r : ℝ) * |(C' : ℝ) - C| / min (C : ℝ) C' ≤ 2 / Y ∧
    (dimPol r C' : ℝ) ≤ Real.exp (2 / Y) * dimPol r C
def SegWindowDims : Prop :=
  ∀ (p N N₁ r s A0 : ℕ) (Y a b' Q La : ℝ) (P : Fin s → ℝ) (A Clo Chi : Fin s → ℕ),
    HypSeg p N N₁ (r + 1) Y a b' Q La → s ≤ N₁ → (N₁ : ℝ) ≤ Y → (∀ i, 1 ≤ P i ∧ P i ≤ Q) →
    (∀ i, a / P i - ((r : ℝ) + 1) ≤ Clo i ∧ (Clo i : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y)) / P i) →
    (∀ i, a / P i - ((r : ℝ) + 1) ≤ Chi i ∧ (Chi i : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y)) / P i) →
    (dimMM r A0 A Chi : ℝ) ≤ Real.exp (2 * s / Y) * dimMM r A0 A Clo ∧
    (dimMM r A0 A Chi : ℝ) ≤ Real.exp 2 * dimMM r A0 A Clo
def UseSegRatio : Prop :=
  ∀ (r s A0 : ℕ) (A C : Fin s → ℕ) (i : Fin s) (Cp : ℕ) (a L P : ℝ), 0 < a → 0 < P →
    ((r : ℝ) + 1) ^ 2 * P ≤ a → C i ≤ Cp → (Cp : ℝ) ≤ C i + L / P → a / P - ((r : ℝ) + 1) ≤ C i →
    (dimMM r A0 A (Function.update C i Cp) : ℝ) ≤ Real.exp (((r : ℝ) + 1) * L / a) * dimMM r A0 A C
def SegExtWindow : Prop :=
  ∀ (p N N₁ r : ℕ) (Y a b' Q La x : ℝ), HypSeg p N N₁ (r + 1) Y a b' Q La →
    ((r : ℝ) + 1) * Y ^ 2 * La * Real.log a ≤ a / b' → 0 ≤ x → x ≤ 2 * (La * b' / ((r : ℝ) + 1)) →
    x ≤ 2 * a / (((r : ℝ) + 1) ^ 2 * Y ^ 2 * Real.log a) ∧ x ≤ a / (((r : ℝ) + 1) * Y) ∧
    a + a / (((r : ℝ) + 1) * Y) + x ≤ a * (1 + 2 / (((r : ℝ) + 1) * Y)) ∧
    a * (1 + 2 / (((r : ℝ) + 1) * Y)) ≤ 2 * a ∧
    1 / Y + ((r : ℝ) + 1) * x / a ≤ 1 / (3 * Y / 5) ∧
    ∀ (P : ℝ) (C C' : ℕ), 1 ≤ P → P ≤ Q →
      a / P - ((r : ℝ) + 1) ≤ C → a / P - ((r : ℝ) + 1) ≤ C' →
      (C : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y) + x) / P → (C' : ℝ) ≤ (a + a / (((r : ℝ) + 1) * Y) + x) / P →
      (r : ℝ) * |(C' : ℝ) - C| / min (C : ℝ) C' ≤ 3 / Y ∧
      (dimPol r C' : ℝ) ≤ Real.exp (3 / Y) * dimPol r C
def SegExtB : Prop :=
  ∀ (C La k N₁ b' bLo bHi x : ℝ), 4 ≤ C → 0 ≤ La → 0 < k → 1 ≤ N₁ → 0 < b' → bLo ≤ b' → b' ≤ bHi →
    C * N₁ * La / k + 2 * (bHi - bLo) / b' < 1 / 6 → x ≤ 2 * (La * b' / k) →
    (bHi - bLo) / b' < 1 / 12 ∧ La / k < 1 / 24 ∧ b' * (1 - 1 / 12) ≤ bLo ∧
    bHi + x ≤ b' * (1 + 1 / 12 + 1 / 12) ∧ b' / 2 ≤ bLo ∧ bHi + x ≤ 3 * b' / 2
abbrev DigitVec (s m : ℕ) (P : Fin s → ℕ) : Type := (i : Fin s) → Fin (m + 1) → Fin (P i)
def DigitCompat {s m : ℕ} {P : Fin s → ℕ} (ρ : DigitVec s m P) (aa : Fin (s + 1) → ℕ) : Prop :=
  ∀ i : Fin s, (∑ c, ((ρ i c : Fin (P i)) : ℕ)) % P i = aa i.castSucc % P i
instance DigitCompat.decidable {s m : ℕ} {P : Fin s → ℕ} (ρ : DigitVec s m P) (aa : Fin (s + 1) → ℕ) : Decidable (DigitCompat ρ aa) := by
  unfold DigitCompat; infer_instance
def DigitVectorsCount : Prop :=
  ∀ (s m : ℕ) (P : Fin s → ℕ) (aa : Fin (s + 1) → ℕ), (∀ i, 0 < P i) →
    ((univ : Finset (DigitVec s m P)).filter (fun ρ => DigitCompat ρ aa)).card = ∏ i, P i ^ m
def DigitDoubleCount : Prop :=
  ∀ (s m : ℕ) (P : Fin s → ℕ) (I : Finset ℕ) (R : Type) [Fintype R] (M : R → ℝ), (∀ i, 0 < P i) →
    ∑ ρ : DigitVec s m P, ∑ q : R,
        (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) * M q =
      (I.card : ℝ) ^ (s + 1) * ((∏ i, P i ^ m : ℕ) : ℝ) * ∑ q : R, M q
def MeanShareA : Prop :=
  ∀ (s : ℕ) (As : Fin s → Finset ℕ) (Ap : Finset ℕ) (U : Finset (Fin s)) (top : Fin s → ℕ)
    (bad rk : (Fin s → ℕ) → ℕ → ℝ) (m : (Fin s → ℕ) → ℝ) (X : Fin s → (Fin s → ℕ) → ℝ)
    (eps : Fin s → ℝ) (epsP K : ℝ),
    (∀ i, (As i).Nonempty) → Ap.Nonempty → (∀ i ∈ U, top i ∈ As i) →
    (∀ aa ∈ Fintype.piFinset As, ∀ ap ∈ Ap, 0 ≤ bad aa ap) →
    (∀ i ∈ U, ∀ aa ∈ Fintype.piFinset As, 0 ≤ X i aa) →
    (∀ aa ∈ Fintype.piFinset As, 0 < m aa ∧ ∀ ap ∈ Ap, m aa / 2 ≤ rk aa ap) →
    (∀ i ∈ U, ∀ aa ∈ Fintype.piFinset As, m (Function.update aa i (top i)) ≤ K * m aa) →
    (∀ i ∈ U, ∀ aa ∈ Fintype.piFinset As,
      (∑ x ∈ As i, X i (Function.update aa i x)) / (As i).card ≤ eps i * m (Function.update aa i (top i))) →
    (∀ aa ∈ Fintype.piFinset As, (∑ ap ∈ Ap, bad aa ap) / Ap.card ≤ (∑ i ∈ U, X i aa) + epsP * m aa) →
    (∑ aa ∈ Fintype.piFinset As, ∑ ap ∈ Ap, bad aa ap / rk aa ap) / ((Fintype.piFinset As).card * Ap.card) ≤
      2 * K * (∑ i ∈ U, eps i) + 2 * epsP
def MeanShareB : Prop :=
  ∀ (s m : ℕ) (P : Fin s → ℕ) (I : Finset ℕ) (R : Type) [Fintype R]
    (bad rk : DigitVec s m P → R → (Fin (s + 1) → ℕ) → ℝ) (Mlo Mhi : R → ℝ) (eps K : ℝ),
    (∀ i, 0 < P i) → I.Nonempty → 0 ≤ eps → 0 ≤ K →
    (∀ ρ q aa, 0 ≤ bad ρ q aa) → (∀ q, 0 ≤ Mlo q) → (∀ q, Mhi q ≤ K * Mlo q) →
    (∀ ρ q, ∀ aa ∈ Fintype.piFinset fun _ : Fin (s + 1) => I, DigitCompat ρ aa → Mlo q / 2 ≤ rk ρ q aa) →
    (∀ ρ q, ∑ aa ∈ (Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa), bad ρ q aa ≤
      eps * (((Fintype.piFinset fun _ : Fin (s + 1) => I).filter (fun aa => DigitCompat ρ aa)).card : ℝ) * Mhi q) →
    (∑ aa ∈ Fintype.piFinset fun _ : Fin (s + 1) => I,
        (∑ ρ ∈ univ.filter (fun ρ : DigitVec s m P => DigitCompat ρ aa), ∑ q, bad ρ q aa) /
          (∑ ρ ∈ univ.filter (fun ρ : DigitVec s m P => DigitCompat ρ aa), ∑ q, rk ρ q aa)) /
      ((Fintype.piFinset fun _ : Fin (s + 1) => I).card : ℝ) ≤ 2 * K * eps
def SegShareSum : Prop :=
  (∀ (t : ℕ) (Y epsP : ℝ) (eps : Fin t → ℝ), 1 ≤ Y → (∀ i, eps i ≤ 28 / Y) → epsP ≤ 5 / Y →
    2 * Real.exp (2 / Y) * (∑ i, eps i) + 2 * epsP ≤ 2 * Real.exp 2 * ((t : ℝ) + 1) * 28 / Y ∧
    2 * Real.exp 2 * ((∑ i, eps i) + epsP) ≤ 2 * Real.exp 2 * 28 * ((t : ℝ) + 1) / Y) ∧
  ∀ (Jn N N₁ : ℕ) (Y : ℝ) (t : Fin Jn → ℕ) (κ : Fin Jn → ℝ), 1 ≤ Y → 1 ≤ N₁ → ∑ j, (t j + 1) ≤ N →
    (∀ j, κ j ≤ 1) → ((N₁ : ℝ) ≤ Y → ∀ j, κ j ≤ 2 * Real.exp 2 * 28 * ((t j : ℝ) + 1) / Y) →
    (∀ j, κ j ≤ 56 * Real.exp 2 * ((t j : ℝ) + 1) * N₁ / Y) ∧ ∑ j, κ j ≤ 56 * Real.exp 2 * N * N₁ / Y
def PartnerConverse : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (A B : Type) [AddCommGroup A] [Module O A] [Module.Free O A] [Module.Finite O A]
      [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B]
      (b : A →ₗ[O] Module.Dual O B) (n D : ℕ), Formalism.G0.GoodRank π b n D →
      ∃ g : (Fin n → O) →ₗ[O] A, Function.Injective g ∧
        (∀ x : A, π • x ∈ LinearMap.range g → x ∈ LinearMap.range g) ∧
        ∀ x : Fin n → O, (∃ i, ¬ π ∣ x i) → ∃ u' : B, ¬ π ^ (D + 1) ∣ b (g x) u'
def ChangeLatticeGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (L L' : Type) [AddCommGroup L] [Module O L] [Module.Free O L] [Module.Finite O L]
      [AddCommGroup L'] [Module O L'] [Module.Free O L'] [Module.Finite O L']
      (f : L →ₗ[O] Module.Dual O L) (f' : L' →ₗ[O] Module.Dual O L') (φ : L →ₗ[O] L') (c : O) (y n D : ℕ),
      c ∣ π ^ y → (∀ u u₁ : L, f' (φ u) (φ u₁) = c * c * f u u₁) →
      Formalism.G0.GoodRank π f n D → Formalism.G0.GoodRank π f' n (D + 2 * y)
def DirectSumGoodRank : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (M : ℕ) (A B : Fin M → Type) [∀ d, AddCommGroup (A d)] [∀ d, Module O (A d)]
      [∀ d, Module.Free O (A d)] [∀ d, Module.Finite O (A d)]
      [∀ d, AddCommGroup (B d)] [∀ d, Module O (B d)] [∀ d, Module.Free O (B d)] [∀ d, Module.Finite O (B d)]
      (f : ∀ d, A d →ₗ[O] B d) (n : Fin M → ℕ) (D : ℕ),
      (∀ d, Formalism.G0.GoodRank π (f d) (n d) D) →
        Formalism.G0.GoodRank π (LinearMap.pi fun d => f d ∘ₗ LinearMap.proj d : (∀ d, A d) →ₗ[O] (∀ d, B d)) (∑ d, n d) D
def DirectSumPartners : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O), Irreducible π →
    ∀ (M : ℕ) (A B : Fin M → Type) [∀ d, AddCommGroup (A d)] [∀ d, Module O (A d)]
      [∀ d, AddCommGroup (B d)] [∀ d, Module O (B d)]
      (b : ∀ d, A d →ₗ[O] Module.Dual O (B d)) (n : Fin M → ℕ) (g : ∀ d, (Fin (n d) → O) →ₗ[O] A d) (D : ℕ),
      (∀ d, ∀ x : A d, π • x ∈ LinearMap.range (g d) → x ∈ LinearMap.range (g d)) →
      (∀ d, ∀ x : Fin (n d) → O, (∃ i, ¬ π ∣ x i) → ∃ u' : B d, ¬ π ^ (D + 1) ∣ b d (g d x) u') →
      (∀ x : ∀ d, A d,
        π • x ∈ LinearMap.range (LinearMap.pi fun d => g d ∘ₗ LinearMap.proj d : (∀ d, Fin (n d) → O) →ₗ[O] ∀ d, A d) →
          x ∈ LinearMap.range (LinearMap.pi fun d => g d ∘ₗ LinearMap.proj d : (∀ d, Fin (n d) → O) →ₗ[O] ∀ d, A d)) ∧
      ∀ x : ∀ d, Fin (n d) → O, (∃ d i, ¬ π ∣ x d i) →
        ∃ u' : ∀ d, B d, ¬ π ^ (D + 1) ∣ ∑ d, b d (g d (x d)) (u' d)
def DetLeadDiag : Prop :=
  ∀ (K : Type) [Field K] (n J : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial K)) (d : Fin n → K),
    (∀ a b, (A a b).natDegree ≤ J) → (∀ a b, (A a b).coeff J = if a = b then d a else 0) →
    A.det.natDegree ≤ n * J ∧ A.det.coeff (n * J) = ∏ a, d a
def DigitSumValuationBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n r : ℕ) (a : ℝ), 1 ≤ a → (n : ℝ) ≤ 8 * a + r →
    0 ≤ (n : ℝ) / ((p : ℝ) - 1) - padicValNat p n.factorial ∧
    (n : ℝ) / ((p : ℝ) - 1) - padicValNat p n.factorial = ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ∧
    (n : ℝ) / ((p : ℝ) - 1) - padicValNat p n.factorial ≤ lgSeg p a r
end Formalism.CountingSumsFrames


