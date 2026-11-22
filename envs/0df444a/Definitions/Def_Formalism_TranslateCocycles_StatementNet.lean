-- Prove2me | Definitions.Def_Formalism_TranslateCocycles_StatementNet
-- name    : Formalism_TranslateCocycles_StatementNet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:54.242037+00:00
-- url     : https://prove2.me/theorems/b42124dd-3340-4fe3-be6e-9220ddcb46b1
-- title:
--   Statement Net
-- statement:
--   Definitions and structural lemmas for Statement Net, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TranslateCocycles/StatementNet.lean

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
namespace Formalism.CG
open Finset
def NetExponent : Prop :=
  (∀ k c : ℚ,
    (k + c) ^ 2 - c * (c - 1) / 2 - (c - 1) * k - k * (k - 1) / 2
        = k ^ 2 / 2 + k * c + c ^ 2 / 2 + c / 2 + 3 * k / 2 ∧
    k ^ 2 / 2 + k * c + c ^ 2 / 2 + c / 2 + 3 * k / 2 = (k + c) * (k + c + 1) / 2 + k ∧
    k ^ 2 - k * (k - 1) / 2 = k * (k + 1) / 2) ∧
  (∀ k c p : ℚ, c * (c - 1) / 2 + (c - p) * k + (p - 1) * k = c * (c - 1) / 2 + (c - 1) * k) ∧
  (∀ k m : ℚ,
    ((k + m - 1) * (k + m) - k * (k + 1)) / 2 + k = (2 * k * (m - 1) + m * (m - 1)) / 2 + k ∧
    (2 * k * (m - 1) + m * (m - 1)) / 2 + k = k * m + m * (m - 1) / 2 ∧
    k * m + m * (m - 1) / 2 = m * (2 * k + m - 1) / 2) ∧
  (∀ k c : ℕ, 1 ≤ c →
    (c * (c - 1) / 2 + (c - 1) * k + k * (k - 1) / 2) + ((k + c) * (k + c + 1) / 2 + k)
      = (k + c) ^ 2) ∧
  (∀ k : ℕ, k * (k - 1) / 2 + k * (k + 1) / 2 = k ^ 2)
def NetCardGL : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ),
    Nat.card (GL (Fin n) F)
      = Fintype.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (Fintype.card F ^ i - 1) ∧
    (Nat.card (GL (Fin n) F) : ℝ)
      = (Fintype.card F : ℝ) ^ (n ^ 2) * ∏ i ∈ Icc 1 n, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)
def netHasPattern {F : Type} [Field F] {n : ℕ} (S : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0
def NetPatternGroup : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (S : Finset (Fin n × Fin n)),
    (∀ x ∈ S, x.1 < x.2) → (∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S) →
    ∃ H : Subgroup (GL (Fin n) F),
      (∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern S (A : Matrix (Fin n) (Fin n) F)) ∧
      Nat.card H = Fintype.card F ^ S.card
def netFull (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun x => x.1 < x.2
def netPattern (k c p0 : ℕ) : Finset (Fin (k + c) × Fin (k + c)) :=
  univ.filter fun x => x.1 < x.2 ∧ ¬ (p0 ≤ x.1.val ∧ x.2.val = p0 + k)
def NetPatternCard : Prop :=
  (∀ n : ℕ, (netFull n).card = n * (n - 1) / 2 ∧
    ∀ i j l, (i, j) ∈ netFull n → (j, l) ∈ netFull n → (i, l) ∈ netFull n) ∧
  (∀ k c p0 : ℕ, p0 < c →
    (netPattern k c p0).card = c * (c - 1) / 2 + (c - 1) * k + k * (k - 1) / 2 ∧
    ∀ i j l, (i, j) ∈ netPattern k c p0 → (j, l) ∈ netPattern k c p0 → (i, l) ∈ netPattern k c p0)
def netX (k c p0 : ℕ) : Finset (Fin (k + c)) := univ.filter fun i => p0 ≤ i.val ∧ i.val < p0 + k
def NetPatternBlocks : Prop :=
  ∀ k c p0 : ℕ, p0 < c →
    ((netPattern k c p0).filter fun x => x.1 ∈ netX k c p0 ∧ x.2 ∈ netX k c p0).card
      = k * (k - 1) / 2 ∧
    ((netPattern k c p0).filter fun x => x.1 ∈ netX k c p0 ∧ x.2 ∉ netX k c p0).card
      = (c - (p0 + 1)) * k ∧
    (∀ x ∈ netPattern k c p0, x.1 ∈ netX k c p0 → x.2 ∉ netX k c p0 → p0 + k < x.2.val) ∧
    ((netPattern k c p0).filter fun x => x.1 ∉ netX k c p0 ∧ x.2 ∈ netX k c p0).card = p0 * k ∧
    (∀ x ∈ netPattern k c p0, x.1 ∉ netX k c p0 → x.2 ∈ netX k c p0 → x.1.val < p0) ∧
    ((netPattern k c p0).filter fun x => x.1 ∉ netX k c p0 ∧ x.2 ∉ netX k c p0).card
      = c * (c - 1) / 2
def NetIndexCounts : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k c p0 : ℕ), p0 < c →
    ∀ (Ha : Subgroup (GL (Fin k) F)) (Hb : Subgroup (GL (Fin (k + c)) F)),
    (∀ A : GL (Fin k) F, A ∈ Ha ↔ netHasPattern (netFull k) (A : Matrix (Fin k) (Fin k) F)) →
    (∀ A : GL (Fin (k + c)) F, A ∈ Hb ↔
      netHasPattern (netPattern k c p0) (A : Matrix (Fin (k + c)) (Fin (k + c)) F)) →
    Ha.index = ∏ i ∈ Icc 1 k, (Fintype.card F ^ i - 1) ∧
    (Ha.index : ℝ) = (Fintype.card F : ℝ) ^ (k * (k + 1) / 2)
        * ∏ i ∈ Icc 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹) ∧
    (Hb.index : ℝ) = (Fintype.card F : ℝ) ^ ((k + c) * (k + c + 1) / 2 + k)
        * ∏ i ∈ Icc 1 (k + c), (1 - ((Fintype.card F : ℝ) ^ i)⁻¹) ∧
    (Hb.index : ℝ) / (Ha.index : ℝ) = (Fintype.card F : ℝ) ^ (k * (c + 1) + (c + 1) * c / 2)
        * ∏ i ∈ Ioc k (k + c), (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)
def NetIndexLocal : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] [Fintype (IsLocalRing.ResidueField O)] (k c p0 : ℕ),
    p0 < c →
    ∀ (Ka : Subgroup (GL (Fin k) O)) (Kb : Subgroup (GL (Fin (k + c)) O)),
    (∀ A : GL (Fin k) O, A ∈ Ka ↔
      netHasPattern (netFull k) ((A : Matrix (Fin k) (Fin k) O).map (IsLocalRing.residue O))) →
    (∀ A : GL (Fin (k + c)) O, A ∈ Kb ↔ netHasPattern (netPattern k c p0)
      ((A : Matrix (Fin (k + c)) (Fin (k + c)) O).map (IsLocalRing.residue O))) →
    Ka.index = ∏ i ∈ Icc 1 k, (Fintype.card (IsLocalRing.ResidueField O) ^ i - 1) ∧
    (Ka.index : ℝ) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ (k * (k + 1) / 2)
        * ∏ i ∈ Icc 1 k, (1 - ((Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ i)⁻¹) ∧
    (Kb.index : ℝ) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ ((k + c) * (k + c + 1) / 2 + k)
        * ∏ i ∈ Icc 1 (k + c), (1 - ((Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ i)⁻¹) ∧
    (Kb.index : ℝ) / (Ka.index : ℝ)
      = (Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ (k * (c + 1) + (c + 1) * c / 2)
        * ∏ i ∈ Ioc k (k + c), (1 - ((Fintype.card (IsLocalRing.ResidueField O) : ℝ) ^ i)⁻¹)
def NetRho : Prop :=
  ∀ (g : ℝ), 2 ≤ g → ∀ k r : ℕ, k < r →
    1 - 2 * (g ^ (k + 1))⁻¹ < ∏ i ∈ Ioc k r, (1 - (g ^ i)⁻¹) ∧
    ∏ i ∈ Ioc k r, (1 - (g ^ i)⁻¹) < 1 ∧
    (1 ≤ k → |Real.log (∏ i ∈ Ioc k r, (1 - (g ^ i)⁻¹))| ≤ 4 * (g ^ (k + 1))⁻¹)
def NetLogT : Prop :=
  ∀ (f k m : ℕ), 0 < f → 0 < k → ∀ (g1 g2 rho1 rho2 : ℝ), 0 < g1 → 0 < g2 → 0 < rho1 → 0 < rho2 →
    Real.log ((g1 ^ (k * m + m * (m - 1) / 2) * rho1) ^ f * (g2 ^ (k * m + m * (m - 1) / 2) * rho2) ^ f)
        / ((f : ℝ) * k)
      = (m : ℝ) * (1 + ((m : ℝ) - 1) / (2 * k)) * Real.log (g1 * g2)
        + (Real.log rho1 + Real.log rho2) / k
def NetLogTWindow : Prop :=
  ∀ (f k m : ℕ), 0 < f → 0 < k → ∀ (g1 g2 rho1 rho2 X Rest Gam T : ℝ), 0 < g1 → 0 < g2 → 0 < rho1 →
    0 < rho2 → 0 < X → 0 < Rest → 0 < Gam →
    X ^ (f * k) = (g1 ^ (k * m + m * (m - 1) / 2) * rho1) ^ f
        * (g2 ^ (k * m + m * (m - 1) / 2) * rho2) ^ f * Rest →
    X * Gam ^ (-2 / ((f : ℝ) * k)) ≤ T → T ≤ X * Gam ^ (-2 / ((f : ℝ) * k)) * (1 + 1 / ((f : ℝ) * k)) →
    0 ≤ Real.log T - ((m : ℝ) * (1 + ((m : ℝ) - 1) / (2 * k)) * Real.log (g1 * g2)
        + (Real.log rho1 + Real.log rho2) / k + Real.log Rest / ((f : ℝ) * k)
        - 2 / ((f : ℝ) * k) * Real.log Gam) ∧
    Real.log T - ((m : ℝ) * (1 + ((m : ℝ) - 1) / (2 * k)) * Real.log (g1 * g2)
        + (Real.log rho1 + Real.log rho2) / k + Real.log Rest / ((f : ℝ) * k)
        - 2 / ((f : ℝ) * k) * Real.log Gam) ≤ 1 / ((f : ℝ) * k)
def NetReturnOfA : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (P TT : Finset ι), TT ⊆ P → ∀ (n a : ι → ℝ) (R1 R2 m k : ℝ),
    1 ≤ m → 0 < k → m - 1 ≤ 2 * k →
    (∀ t ∈ TT, |n t - a t| ≤ R1) → (∀ τ ∈ P \ TT, |n τ| ≤ R2) → 0 ≤ R2 →
    |(∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k)))
        - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)|
      ≤ 2 * m * ((TT.card : ℝ) * R1 + (P.card : ℝ) * R2)
def NetExcess : Prop :=
  ∀ (a at' m k L C lg : ℝ), 1 ≤ m → 1 ≤ k → 0 < L → m ^ 2 * L ≤ k → 0 ≤ lg → lg ≤ C * L →
    0 ≤ at' → at' ≤ a * (1 + 1 / k) →
    0 ≤ m * (m - 1) / (2 * k) * at' * lg ∧
    m * (m - 1) / (2 * k) * at' * lg ≤ a * (1 + 1 / k) * m ^ 2 * lg / (2 * k) ∧
    a * (1 + 1 / k) * m ^ 2 * lg / (2 * k) ≤ C * a
def NetSurplus : Prop :=
  ∀ (a m k lg : ℝ), k ≠ 0 →
    a * ((m + m * (m - 1) / (2 * k)) * lg) = m * a * lg + a * m * (m - 1) * lg / (2 * k) ∧
    a * m ^ 2 * lg / (2 * k) - a * m * (m - 1) * lg / (2 * k) = a * m * lg / (2 * k) ∧
    m + m * (m - 1) / (2 * k) = m * (1 + (m - 1) / (2 * k))
def NetUnitMean : Prop :=
  ∀ (Λ : Type) [Fintype Λ] (y X : Λ → ℝ) (lg : ℝ), (∀ w w', y w = y w') → ∑ w, y w = lg →
    ∑ w, y w * X w = lg * ((∑ w, X w) / (Fintype.card Λ : ℝ))
def NetPairMean : Prop :=
  ∀ (Λ : Type) [Fintype Λ] (c : Λ → Λ), Function.Involutive c → ∀ (x X : Λ → ℝ),
    (∀ w, x (c w) = x w) → ∑ w, x w * X w = ∑ w, x w * ((X w + X (c w)) / 2)
def NetUnitHalf : Prop :=
  ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (A : Finset Λ) (d v : Λ → ℝ) (n D lg : ℝ), n ≠ 0 →
    ∑ w ∈ A, d w = n / 2 → (∀ w ∈ A, v w = D) → (∀ w ∉ A, v w = 0) →
    2 * ∑ w, d w * lg / n * v w = D * lg
def NetRemainderShare : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (G : Finset Ω) (c : Ω → Ω), Function.Involutive c → (∀ u ∈ G, c u ∈ G) →
    ∀ (y r : Ω → ℝ), (∀ u, 0 ≤ y u) → (∀ u, 0 ≤ r u) → (∀ u ∈ G, y (c u) = y u) →
    ∀ (dK del D B : ℝ), 0 < del → 0 < D → dK / del ≤ 4 * D → 0 ≤ B → ∑ u, y u * r u ≤ dK * B →
      ∑ u ∈ G, y u * ((r u + r (c u)) / (del * D)) ≤ 2 * 4 * B
def NetWeightDegree : Prop :=
  ∀ (k j m : ℕ), 1 ≤ k → j ≤ m → ∀ (w η Cc : ℝ) (c' : Fin (k - 1) → ℝ) (u : Fin j → ℝ)
    (v : Fin (m - j) → ℝ), (∀ i, |c' i| ≤ Cc) → (∀ i, 0 ≤ u i ∧ u i ≤ η) → (∀ i, 0 ≤ v i ∧ v i ≤ η) →
    |((∑ i, (w + c' i) + ∑ i, u i) + ∑ i, v i) - ((k : ℝ) - 1) * w| ≤ ((k : ℝ) - 1) * Cc + m * η
def NetRankSize : Prop :=
  (∀ (k m t L S η : ℕ), 1 ≤ m → 1 ≤ t → 1 ≤ L → k ≤ S → m * k * t * L ≤ η →
    k * (k + m - 1 + t) ≤ k * S + m * η) ∧
  (∀ (k m t L η : ℕ), 2 ≤ m → 1 ≤ L → k ≤ t → m * k * t * L ≤ η → k * (k + m - 1 + t) ≤ m * η)
def NetRemSize : Prop :=
  ∀ (C L lg tt f b' Sg w'' b m : ℝ), 0 ≤ C → 0 ≤ L → 0 ≤ lg → lg ≤ C * L → 0 ≤ tt → tt ≤ f →
    0 ≤ b' → b' ≤ 2 * b → 0 ≤ Sg → Sg ≤ 4 * w'' → w'' ≤ b → 1 ≤ m →
    2 * C * lg * (tt * (b' + Sg) + f * Sg) ≤ 16 * C ^ 2 * L * (tt * b' + f * w'') ∧
    16 * C ^ 2 * L * (tt * b' + f * w'') ≤ 48 * C ^ 2 * (f * m * b * L)
def NetComplement : Prop :=
  ∀ (Fj nnL nnLb vc vcb m Dpi Dp Dm sa sw k ε1 ε2 oL oLb δ : ℝ), 2 * Fj = -(Dp + Dm) →
    nnL + nnLb = Dpi → vc + vcb = 0 → |Dpi - (sa + k * sw)| ≤ ε1 → |Dp + Dm - (k - 1) * sw| ≤ ε2 →
    |oL| ≤ δ → |oLb| ≤ δ →
    (Fj + nnL - vc / m + oL) + (Fj + nnLb - vcb / m + oLb) = 2 * Fj + Dpi + (oL + oLb) ∧
    |(Fj + nnL - vc / m + oL) + (Fj + nnLb - vcb / m + oLb) - (sa + sw)| ≤ ε1 + ε2 + 2 * δ
def NetTopDifference : Prop :=
  ∀ (a bt b' x w k ε : ℝ), w = bt + b' / x + ε →
    (a - bt + k * w) - (k - 1) * w = a + b' / x + ε ∧ (2 ≤ x → 0 ≤ b' → b' ≤ w → b' / x ≤ w / 2)
def NetBalanceG : Prop :=
  ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (colL colLb : ℝ) (aL aLb Dpi Dp Dm eta etab top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA rL rLb Etw : ℝ),
    -(∑ j ∈ J, Dpi j) - Ecol ≤ colL + colLb →
    ∑ j ∈ J, (aL j + aLb j) ≤ ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j + etab j)
        + 2 * (J.card : ℝ) * (CA * D + (rL + rLb) / del) + Etw →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
    ∀ (n : ℕ → ℝ) (R1 R2 : ℝ), T ⊆ P → 1 ≤ J.card → 0 < k → (J.card : ℝ) - 1 ≤ 2 * k →
    (∀ t ∈ T, |n t - top t| ≤ R1) → (∀ τ ∈ P \ T, |n τ| ≤ R2) → 0 ≤ R2 →
      -(∑ j ∈ J, ∑ τ ∈ P, w j τ)
        + (J.card : ℝ) * ((J.card : ℝ) - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + ∑ j ∈ J, (eta j + etab j) / (2 * D)
            + Ecol + (J.card : ℝ) * (CA + (rL + rLb) / (del * D)) + Etw / (2 * D)
            + 2 * (J.card : ℝ) * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2))
      ≤ ((2 * colL + 2 * colLb) / 2 - (∑ j ∈ J, (aL j + aLb j) / D) / 2)
        + (∑ τ ∈ P, n τ) * ((J.card : ℝ) * (1 + ((J.card : ℝ) - 1) / (2 * k)))
def NetBalanceMean : Prop :=
  ∀ (Λ : Type) [Fintype Λ] [Nonempty Λ] (c : Λ → Λ), Function.Involutive c →
    ∀ (y : Λ → ℝ) (lg : ℝ), (∀ u u', y u = y u') → ∑ u, y u = lg → 0 ≤ lg →
    ∀ (J T P : Finset ℕ) (D del : ℝ), 0 < D → 0 < del →
    ∀ (col r : Λ → ℝ) (a eta : ℕ → Λ → ℝ) (Dpi Dp Dm top : ℕ → ℝ) (k : ℝ) (w e1 e2 : ℕ → ℕ → ℝ)
      (Ecol CA Etw : ℝ),
    (∀ u, -(∑ j ∈ J, Dpi j) - Ecol ≤ col u + col (c u)) →
    (∀ u, ∑ j ∈ J, (a j u + a j (c u)) ≤
        ∑ j ∈ J, (-2 * (Dp j + Dm j) * D + eta j u + eta j (c u))
        + 2 * (J.card : ℝ) * (CA * D + (r u + r (c u)) / del) + Etw) →
    (∀ j ∈ J, Dpi j ≤ ∑ t ∈ T, top t + ∑ τ ∈ P, (k * w j τ + e1 j τ)) →
    (∀ j ∈ J, ∑ τ ∈ P, ((k - 1) * w j τ - e2 j τ) ≤ Dp j + Dm j) →
    ∀ (n : ℕ → ℝ) (R1 R2 : ℝ), T ⊆ P → 1 ≤ J.card → 0 < k → (J.card : ℝ) - 1 ≤ 2 * k →
    (∀ t ∈ T, |n t - top t| ≤ R1) → (∀ τ ∈ P \ T, |n τ| ≤ R2) → 0 ≤ R2 →
      lg * (-(∑ j ∈ J, ∑ τ ∈ P, w j τ)
        + (J.card : ℝ) * ((J.card : ℝ) - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ)
            + ∑ j ∈ J, ((∑ u, eta j u) / (Fintype.card Λ : ℝ)) / D
            + Ecol
            + (J.card : ℝ) * (CA + ((∑ u, (r u + r (c u))) / (Fintype.card Λ : ℝ)) / (del * D))
            + Etw / (2 * D)
            + 2 * (J.card : ℝ) * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2)))
      ≤ ∑ u, y u * (2 * col u - ∑ j ∈ J, a j u / D)
        + (∑ τ ∈ P, n τ) * ((J.card : ℝ) * (1 + ((J.card : ℝ) - 1) / (2 * k))) * lg
end Formalism.CG


