-- Prove2me | Definitions.Def_Formalism_TranslateCocycles_StatementHC
-- name    : Formalism_TranslateCocycles_StatementHC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:57.255105+00:00
-- url     : https://prove2.me/theorems/b6ec6748-f598-43cb-b12b-26560eda5a74
-- title:
--   Statement HC
-- statement:
--   Definitions and structural lemmas for Statement HC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TranslateCocycles/StatementHC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CG
open Finset
def HCrank (k t j : ℕ) : ℕ := k + j * (t + 1)
def HCparam (k t : ℕ) (u e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l ≤ k then u l
  else -e ((l - k - 1) / (t + 1) + 1) + (t : ℚ) / 2 - (((l - k - 1) % (t + 1) : ℕ) : ℚ)
def HCnu (k t : ℕ) (u e : ℕ → ℚ) (j l : ℕ) : ℚ :=
  HCparam k t u e l - ((HCrank k t (j - 1) : ℚ) + 1 - 2 * (l : ℚ)) / 2 + e j
    - (HCrank k t j : ℚ) / 2
def HClam0 (k : ℕ) (u : ℕ → ℚ) (i : ℕ) : ℚ := u i - ((k : ℚ) + 1 - 2 * (i : ℚ)) / 2
def HCwG (k t : ℕ) (e : ℕ → ℚ) (j : ℕ) : ℚ :=
  e j - (k : ℚ) / 2 - (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2
def HCdeg (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Icc 1 (HCrank k t (j - 1)), HCnu k t u e j l
def HCblockSum (t : ℕ) (e : ℕ → ℚ) (j : ℕ) : ℚ :=
  ((t : ℚ) + 1) * ∑ i ∈ Ico 1 j, ((e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1))
def HCParamBlocks : Prop :=
  ∀ (k t : ℕ) (u e : ℕ → ℚ),
    (∀ i, i ≤ k → HCparam k t u e i = u i) ∧
    (∀ i s, 1 ≤ i → 1 ≤ s → s ≤ t + 1 →
      HCparam k t u e (k + (i - 1) * (t + 1) + s) = -e i + (t : ℚ) / 2 - ((s : ℚ) - 1))
def HCRows : Prop :=
  ∀ (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ), 1 ≤ j →
    (∀ i, 1 ≤ i → i ≤ k → HCnu k t u e j i = HClam0 k u i + HCwG k t e j) ∧
    (∀ i s, 1 ≤ i → i < j → 1 ≤ s → s ≤ t + 1 →
      HCnu k t u e j (k + (i - 1) * (t + 1) + s)
        = (e j - e i) - ((j : ℚ) - (i : ℚ)) * ((t : ℚ) + 1))
def HCDegree : Prop :=
  ∀ (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ), 1 ≤ j →
    HCdeg k t u e j = ∑ i ∈ Icc 1 k, HClam0 k u i + (k : ℚ) * e j
        - (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2 + HCblockSum t e j ∧
    HCdeg k t u e j = ∑ i ∈ Icc 1 k, HClam0 k u i + (k : ℚ) * HCwG k t e j + HCblockSum t e j
def HCTarget : Prop :=
  ∀ (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ), 1 ≤ j → ∀ l, 1 ≤ l → l ≤ HCrank k t j →
    ((if l ≤ HCrank k t (j - 1) then HCnu k t u e j l else 0)
        - (e j - (HCrank k t (j - 1) : ℚ) / 2))
      + ((HCrank k t j : ℚ) + 1 - 2 * (l : ℚ)) / 2 = HCparam k t u e l
def HCPartition : Prop :=
  ∀ (k t : ℕ) (u e : ℕ → ℚ) (b1 : ℚ) (j : ℕ), 1 ≤ k → 1 ≤ j →
    (∀ i, 1 ≤ i → i < k → u (i + 1) + 1 ≤ u i) →
    -b1 + 1 / 2 ≤ u k →
    b1 + ((t : ℚ) + 3) / 2 ≤ e 1 →
    (∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1)) →
    (∀ l, 1 ≤ l → l < HCrank k t j → HCparam k t u e (l + 1) + 1 ≤ HCparam k t u e l) ∧
    (∀ l, 1 ≤ l → l < HCrank k t (j - 1) → HCnu k t u e j (l + 1) ≤ HCnu k t u e j l) ∧
    2 * (j : ℚ) - 1 ≤ HCnu k t u e j k ∧
    (∀ i s, 1 ≤ i → i < j → 1 ≤ s → s ≤ t + 1 →
      2 * ((j : ℚ) - (i : ℚ)) ≤ HCnu k t u e j (k + (i - 1) * (t + 1) + s)) ∧
    (∀ l, 1 ≤ l → l ≤ HCrank k t (j - 1) → 0 ≤ HCnu k t u e j l)
def HCLamSum : Prop :=
  ∀ (k : ℕ) (u : ℕ → ℚ),
    ∑ i ∈ Icc 1 k, HClam0 k u i = ∑ i ∈ Icc 1 k, u i ∧
    ∀ a b' : ℚ, 2 ≤ k → u 1 = a + ((k : ℚ) - 1) / 2 → u k = -b' - ((k : ℚ) - 1) / 2 →
      HClam0 k u 1 = a ∧ HClam0 k u k = -b' ∧
      ∑ i ∈ Icc 1 k, HClam0 k u i = a - b' + ∑ i ∈ Ioo 1 k, u i
def HCSizesA : Prop :=
  ∀ (k t m j : ℕ) (u e b : ℕ → ℚ) (S η : ℚ), 1 ≤ j → j ≤ m → 1 ≤ t → (k : ℚ) ≤ S → (k : ℚ) ≤ η →
    (∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1)) →
    (∀ i, 1 ≤ i → i < j → b i ≤ e i ∧ e j - b i ≤ η) →
    0 ≤ HCblockSum t e j ∧
    HCblockSum t e j ≤ ((t : ℚ) + 1) * ((j : ℚ) - 1) * η ∧
    ((t : ℚ) + 1) * ((j : ℚ) - 1) * η ≤ 2 * m * t * η ∧
    (k : ℚ) * ((k : ℚ) + (2 * (j : ℚ) - 1) * ((t : ℚ) + 1)) / 2 ≤ (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1) ∧
    (k : ℚ) ^ 2 + k * m * ((t : ℚ) + 1) ≤ k * S + 2 * m * t * η ∧
    -(k * S + 2 * m * t * η) ≤ HCdeg k t u e j - ∑ i ∈ Icc 1 k, HClam0 k u i - k * e j ∧
    HCdeg k t u e j - ∑ i ∈ Icc 1 k, HClam0 k u i - k * e j ≤ 2 * m * t * η
def HCSizesB : Prop :=
  ∀ (k t m j : ℕ) (u e : ℕ → ℚ) (b1 S η : ℚ), 1 ≤ j → j ≤ m → k < t → (k : ℚ) ≤ S →
    (∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1)) →
    (∀ i, 1 ≤ i → i ≤ j → |e i - b1| ≤ η) →
    (k : ℚ) * HCwG k t e j = k * e j - (k : ℚ) ^ 2 / 2 - k * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 ∧
    (k : ℚ) ^ 2 / 2 ≤ k * S ∧
    (k : ℚ) * (2 * (j : ℚ) - 1) * ((t : ℚ) + 1) / 2 ≤ k * m * ((t : ℚ) + 1) ∧
    (k : ℚ) * m * ((t : ℚ) + 1) ≤ m * t * ((t : ℚ) + 1) ∧
    (∀ l, k < l → l ≤ HCrank k t (j - 1) → 0 ≤ HCnu k t u e j l ∧ HCnu k t u e j l ≤ 2 * η) ∧
    -(k * S + m * t * ((t : ℚ) + 1)) ≤ HCdeg k t u e j - ∑ i ∈ Icc 1 k, HClam0 k u i - k * e j ∧
    HCdeg k t u e j - ∑ i ∈ Icc 1 k, HClam0 k u i - k * e j ≤ 2 * m * ((t : ℚ) + 1) * η
def HCDpi : Prop :=
  ∀ (k t m j : ℕ) (P T : Finset ℕ) (u e b : ℕ → ℕ → ℚ) (a b' : ℕ → ℚ) (S η C : ℚ),
    2 ≤ k → 1 ≤ t → 1 ≤ j → j ≤ m → T ⊆ P → (k : ℚ) ≤ S → (k : ℚ) ≤ η → 0 ≤ C →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i < j → e τ i + ((t : ℚ) + 3) ≤ e τ (i + 1)) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i < j → b τ i ≤ e τ i ∧ e τ j - b τ i ≤ η) →
    (∀ τ ∈ P \ T, ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u τ i ∧ u τ i ≤ (C + 1) * S) →
    (∀ τ ∈ T, u τ 1 = a τ + ((k : ℚ) - 1) / 2 ∧ u τ k = -b' τ - ((k : ℚ) - 1) / 2 ∧ 0 ≤ b' τ ∧
      ∀ i, 1 < i → i < k → 0 ≤ u τ i ∧ u τ i ≤ S) →
    ∑ τ ∈ P, HCdeg k t (u τ) (e τ) j
      ≤ ∑ τ ∈ T, a τ + ∑ τ ∈ P, (k * e τ j + ((C + 1) * k * S + 2 * m * t * η)) ∧
    ∑ τ ∈ T, (a τ - b' τ) + ∑ τ ∈ P, (k * e τ j - (k + k * S + 2 * m * t * η))
      ≤ ∑ τ ∈ P, HCdeg k t (u τ) (e τ) j
def HCsparam (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l + 1 ≤ k then v (l + 1)
  else if l + 1 ≤ k + j then -b (l + 1 - k)
  else if l + 1 ≤ k + j + t then -e j + ((t : ℚ) - 1) / 2 - (((l + 1 - (k + j) : ℕ) : ℚ) - 1)
  else -b (l + 1 - k - t)
def HCkap (k t m j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  HCsparam k t j v b e l - (((k : ℚ) + m + t - 1) + 1 - 2 * (l : ℚ)) / 2
    + (e j - (t : ℚ) / 2 + ((k : ℚ) + m + t - 1) / 2 - ((k : ℚ) + j - 1))
def HCDplus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ := ∑ l ∈ Ico 1 (k + j), HCkap k t m j v b e l
def HCDminus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ :=
  ∑ l ∈ Ico (k + j + t) (k + m + t), -HCkap k t m j v b e l
def HCSigmaRows : Prop :=
  ∀ (k t m j : ℕ) (v b e : ℕ → ℚ), 1 ≤ k → 1 ≤ j → j ≤ m →
    (∀ i, 2 ≤ i → i ≤ k → HCkap k t m j v b e (i - 1)
        = e j + (v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j)) ∧
    (∀ i, 1 ≤ i → i ≤ j → HCkap k t m j v b e (k - 1 + i)
        = e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i)) ∧
    (∀ s, 1 ≤ s → s ≤ t → HCkap k t m j v b e (k - 1 + j + s) = 0) ∧
    (∀ i, j < i → i ≤ m → -HCkap k t m j v b e (k - 1 + t + i)
        = b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j))
def HCSigmaPartition : Prop :=
  ∀ (k t m j : ℕ) (v b e : ℕ → ℚ), 1 ≤ k → 1 ≤ t → 1 ≤ j → j ≤ m →
    (∀ i, 2 ≤ i → i < k → v (i + 1) + 1 ≤ v i) →
    (2 ≤ k → -b 1 + 1 ≤ v k) →
    (∀ i, 1 ≤ i → i ≤ m → b i + ((t : ℚ) + 3) / 2 ≤ e i) →
    (∀ i, 1 ≤ i → i < m → e i + ((t : ℚ) + 3) / 2 ≤ b (i + 1)) →
    (∀ l, 1 ≤ l → l + 1 < k + m + t →
      HCsparam k t j v b e (l + 1) + 1 ≤ HCsparam k t j v b e l) ∧
    (∀ l, 1 ≤ l → l + 1 < k + m + t → HCkap k t m j v b e (l + 1) ≤ HCkap k t m j v b e l) ∧
    (∀ l, 1 ≤ l → l < k + j → 1 ≤ HCkap k t m j v b e l) ∧
    (∀ l, k + j + t ≤ l → l < k + m + t → HCkap k t m j v b e l ≤ -1)
def HCSigmaDegree : Prop :=
  ∀ (k t m j : ℕ) (v b e : ℕ → ℚ) (S η : ℚ), 1 ≤ k → 1 ≤ t → 1 ≤ j → j ≤ m →
    (∀ i, 2 ≤ i → i ≤ k → 0 ≤ v i ∧ v i ≤ S) →
    (∀ i, 1 ≤ i → i ≤ m → b i + ((t : ℚ) + 3) / 2 ≤ e i) →
    (∀ i, 1 ≤ i → i < m → e i + ((t : ℚ) + 3) / 2 ≤ b (i + 1)) →
    (∀ i, 1 ≤ i → i ≤ m → |b i - e j| ≤ η) →
    HCDplus k t m j v b e + HCDminus k t m j v b e
      = ((k : ℚ) - 1) * e j + ∑ i ∈ Icc 2 k, (v i - ((t : ℚ) + 1) / 2 - ((k : ℚ) - i) - j)
        + ∑ i ∈ Icc 1 j, (e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i))
        + ∑ i ∈ Ioc j m, (b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j)) ∧
    (∀ i, 1 ≤ i → i ≤ j → 0 ≤ e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ∧
      e j - b i - ((t : ℚ) + 1) / 2 - ((j : ℚ) - i) ≤ η) ∧
    (∀ i, j < i → i ≤ m → 0 ≤ b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ∧
      b i - e j - ((t : ℚ) - 1) / 2 - ((i : ℚ) - j) ≤ η) ∧
    ((k : ℚ) - 1) * e j - ((k : ℚ) - 1) * ((k : ℚ) + m + t - 1)
      ≤ HCDplus k t m j v b e + HCDminus k t m j v b e ∧
    HCDplus k t m j v b e + HCDminus k t m j v b e
      ≤ ((k : ℚ) - 1) * e j + ((k : ℚ) - 1) * S + m * η ∧
    ((k : ℚ) ≤ S → (k : ℚ) * t ≤ η → (k : ℚ) * ((k : ℚ) + m + t - 1) ≤ k * S + m * η)
def HCDifference : Prop :=
  ∀ (k t m j : ℕ) (P T : Finset ℕ) (u v e b : ℕ → ℕ → ℚ) (a b' : ℕ → ℚ) (S η C : ℚ),
    2 ≤ k → 1 ≤ t → 1 ≤ j → j ≤ m → T ⊆ P → (k : ℚ) ≤ S → (k : ℚ) * t ≤ η → 0 ≤ C →
    (∀ τ ∈ P, ∀ i, 2 ≤ i → i ≤ k → 0 ≤ v τ i ∧ v τ i ≤ S) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i ≤ m → b τ i + ((t : ℚ) + 3) / 2 ≤ e τ i) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i < m → e τ i + ((t : ℚ) + 3) / 2 ≤ b τ (i + 1)) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i ≤ m → |b τ i - e τ j| ≤ η) →
    (∀ τ ∈ P \ T, ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u τ i ∧ u τ i ≤ (C + 1) * S) →
    (∀ τ ∈ T, u τ 1 = a τ + ((k : ℚ) - 1) / 2 ∧ u τ k = -b' τ - ((k : ℚ) - 1) / 2 ∧ 0 ≤ b' τ ∧
      ∀ i, 1 < i → i < k → 0 ≤ u τ i ∧ u τ i ≤ S) →
    (∑ τ ∈ P, HCdeg k t (u τ) (e τ) j
        - ∑ τ ∈ P, (HCDplus k t m j (v τ) (b τ) (e τ) + HCDminus k t m j (v τ) (b τ) (e τ))
      ≤ ∑ τ ∈ T, a τ + ∑ τ ∈ P, (e τ j + ((C + 2) * k * S + (2 * t + 1) * m * η))) ∧
    (∑ τ ∈ T, (a τ - b' τ) + ∑ τ ∈ P, (e τ j - (k + 2 * k * S + (2 * t + 1) * m * η))
      ≤ ∑ τ ∈ P, HCdeg k t (u τ) (e τ) j
        - ∑ τ ∈ P, (HCDplus k t m j (v τ) (b τ) (e τ) + HCDminus k t m j (v τ) (b τ) (e τ))) ∧
    (∀ τ ∈ T,
      a τ + (e τ j - b' τ) - (2 * k * S + (2 * t + 1) * m * η)
        ≤ HCdeg k t (u τ) (e τ) j
          - (HCDplus k t m j (v τ) (b τ) (e τ) + HCDminus k t m j (v τ) (b τ) (e τ)) ∧
      HCdeg k t (u τ) (e τ) j
          - (HCDplus k t m j (v τ) (b τ) (e τ) + HCDminus k t m j (v τ) (b τ) (e τ))
        ≤ a τ + (e τ j - b' τ) + (2 * k * S + (2 * t + 1) * m * η))
def HCIntegral : Prop :=
  ∀ (k t m j : ℕ) (u v b e : ℕ → ℚ), 1 ≤ k → 1 ≤ j → j ≤ m →
    (∀ i, 1 ≤ i → i ≤ j → ∃ z : ℤ, e i = z + ((k : ℚ) + t + 1) / 2) →
    ((∀ i, 1 ≤ i → i ≤ k → ∃ z : ℤ, u i = z + ((k : ℚ) + 1) / 2) →
      ∀ l, 1 ≤ l → l ≤ HCrank k t (j - 1) → ∃ z : ℤ, HCnu k t u e j l = z) ∧
    ((∀ i, 2 ≤ i → i ≤ k → ∃ z : ℤ, v i = z + (k : ℚ) / 2) →
      (∀ i, 1 ≤ i → i ≤ m → ∃ z : ℤ, b i = z + (k : ℚ) / 2) →
      ∀ l, 1 ≤ l → l + 1 ≤ k + m + t → ∃ z : ℤ, HCkap k t m j v b e l = z)
def HCTopRow : Prop :=
  ∀ (k t m j : ℕ) (u e b : ℕ → ℚ) (a bt b0 x S η : ℚ),
    2 ≤ k → 1 ≤ t → 1 ≤ j → j ≤ m → (k : ℚ) ≤ S → (k : ℚ) ≤ η →
    (∀ i, 1 ≤ i → i < j → e i + ((t : ℚ) + 3) ≤ e (i + 1)) →
    (∀ i, 1 ≤ i → i < j → b i ≤ e i ∧ e j - b i ≤ η) →
    u 1 = a + ((k : ℚ) - 1) / 2 → u k = -bt - ((k : ℚ) - 1) / 2 →
    (∀ i, 1 < i → i < k → 0 ≤ u i ∧ u i ≤ S) →
    0 ≤ b0 → b0 ≤ bt → 2 ≤ x → bt + b0 / x ≤ e j → e j ≤ bt + b0 / x + η →
    0 ≤ e j - bt ∧ b0 / x ≤ e j / 2 ∧
    a + ((k : ℚ) - 1) * e j + b0 / x - (k * S + 2 * m * t * η) ≤ HCdeg k t u e j ∧
    HCdeg k t u e j ≤ a + ((k : ℚ) - 1) * e j + b0 / x + (k * S + (2 * m * t + 1) * η) ∧
    HCdeg k t u e j ≤ a + k * e j + (k * S + 2 * m * t * η)
def HCBalance : Prop :=
  ∀ (k t m : ℕ) (J P T : Finset ℕ) (u v e b : ℕ → ℕ → ℚ) (a b' : ℕ → ℚ) (S η C : ℚ),
    2 ≤ k → 1 ≤ t → (∀ j ∈ J, 1 ≤ j ∧ j ≤ m) → T ⊆ P → (k : ℚ) ≤ S → (k : ℚ) * t ≤ η → 0 ≤ C →
    (∀ τ ∈ P, ∀ i, 2 ≤ i → i ≤ k → 0 ≤ v τ i ∧ v τ i ≤ S) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i ≤ m → b τ i + ((t : ℚ) + 3) / 2 ≤ e τ i) →
    (∀ τ ∈ P, ∀ i, 1 ≤ i → i < m → e τ i + ((t : ℚ) + 3) / 2 ≤ b τ (i + 1)) →
    (∀ τ ∈ P, ∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → |b τ i - e τ j| ≤ η) →
    (∀ τ ∈ P \ T, ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u τ i ∧ u τ i ≤ (C + 1) * S) →
    (∀ τ ∈ T, u τ 1 = a τ + ((k : ℚ) - 1) / 2 ∧ u τ k = -b' τ - ((k : ℚ) - 1) / 2 ∧ 0 ≤ b' τ ∧
      ∀ i, 1 < i → i < k → 0 ≤ u τ i ∧ u τ i ≤ S) →
    (∀ j ∈ J, ((∑ τ ∈ P, HCdeg k t (u τ) (e τ) j : ℚ) : ℝ)
      ≤ ∑ τ ∈ T, (a τ : ℝ)
        + ∑ τ ∈ P, ((k : ℝ) * (e τ j : ℝ) + (((C + 1) * k * S + 2 * m * t * η : ℚ) : ℝ))) ∧
    (∀ j ∈ J, ∑ τ ∈ P, (((k : ℝ) - 1) * (e τ j : ℝ) - ((k * S + m * η : ℚ) : ℝ))
      ≤ ((∑ τ ∈ P, HCDplus k t m j (v τ) (b τ) (e τ) : ℚ) : ℝ)
        + ((∑ τ ∈ P, HCDminus k t m j (v τ) (b τ) (e τ) : ℚ) : ℝ))
end Formalism.CG


