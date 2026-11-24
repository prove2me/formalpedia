-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_HeightGeSecondCubicBound
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_HeightGeSecondCubicBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:04.67865+00:00
-- url     : https://prove2.me/theorems/37e77ebc-538c-4554-a241-e9d733baad82
-- title:
--   Height Ge Second Cubic Bound
-- statement:
--   Definitions and structural lemmas for Height Ge Second Cubic Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/HeightGeSecondCubicBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
structure ChainParams where

  k : ℕ

  m : ℕ

  t : ℕ

  s : ℕ

  h0 : ℤ

  v : ℕ → ℤ

  b : ℕ → ℤ

  e : ℕ → ℤ
  k_even : Even k
  m_even : Even m
  two_le_k : 2 ≤ k
  two_le_m : 2 ≤ m
  t_odd : Odd t

  t_ge : k + m - 1 + 5 ≤ t

  v_anti : ∀ i, 2 ≤ i → i < k → v (i + 1) < v i

  cloud_above : -b 1 < v k

  low_above_centre : ∀ j, 1 ≤ j → j ≤ m → -e j < -b j

  centre_above_low : ∀ j, 1 ≤ j → j < m → -b (j + 1) < -e j

  lower_gap_bound : ∀ j, 1 ≤ j → j ≤ m → ((t : ℚ) + 3) / 2 ≤ ((e j - b j : ℤ) : ℚ)

  upper_gap_bound : ∀ j, 1 ≤ j → j < m → ((t : ℚ) + 3) / 2 ≤ ((b (j + 1) - e j : ℤ) : ℚ)

  height_le_block_spacing : ∀ i, 1 ≤ i → i < m → h0 ≤ b (i + 1) - b i

  height_ge_first_cubic_bound : 4 * ((k + m * (t + 1) : ℕ) : ℤ) ^ 3 + 2 * t + 6 ≤ h0

  height_ge_second_cubic_bound : (t : ℤ) + 2 * ((k + m * (t + s + 1) : ℕ) : ℤ) ^ 3 + 1 ≤ h0
inductive ChainEntry
  | cloud (i : ℕ)
  | low (i : ℕ)
  | block (i l : ℕ)
  deriving DecidableEq
namespace ChainParams
variable (P : ChainParams)
def r : ℕ := P.k + P.m - 1
def rk (j : ℕ) : ℕ := P.r + j * P.t
def NF : ℕ := P.k + P.m * (P.t + P.s + 1)
def Nm : ℕ := P.k + P.m * (P.t + 1)
noncomputable def nu (j : ℕ) : ℕ :=
  if j < P.m then ⌈((P.m : ℚ) - 1 - j) / 2⌉₊ else 0
def entryVal : ChainEntry → ℤ
  | .cloud i => P.v i
  | .low i => -P.b i
  | .block i l => -P.e i + ((P.t : ℤ) - 1) / 2 - l
def entries (j : ℕ) : Finset ChainEntry :=
  (Finset.Icc 2 P.k).image ChainEntry.cloud ∪ (Finset.Icc 1 P.m).image ChainEntry.low ∪
    (Finset.Icc 1 j ×ˢ Finset.range P.t).image (fun p => ChainEntry.block p.1 p.2)
end ChainParams
def chainSgn (j : ℕ) : ChainEntry → ℤ
  | .cloud _ => 1
  | .low i => if i ≤ j + 1 then 1 else (-1) ^ (i - j - 1)
  | .block _ _ => 1
def initialDifferentialSign : ChainEntry → ℤ
  | .cloud _ => 1
  | .low i => if Odd i then 1 else -1
  | .block _ _ => 1
open ChainParams
def ChainParamEntries.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, j ≤ P.m →
    (P.entries j).card = P.rk j ∧ Set.InjOn P.entryVal (P.entries j)
def ChainSignsInitialDifferential.Statement : Prop :=
  ∀ P : ChainParams, ∀ x ∈ P.entries 0, chainSgn 0 x = initialDifferentialSign x
def ChainSignCount.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, j ≤ P.m →
    ((P.entries j).filter (fun x => chainSgn j x = -1)).card = P.nu j
def ChainSignRule.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, 1 ≤ j → j ≤ P.m →
    P.entries j = P.entries (j - 1) ∪ (Finset.range P.t).image (ChainEntry.block j) ∧
    (∀ x ∈ P.entries (j - 1),
      (-P.e j < P.entryVal x ∧ chainSgn j x = chainSgn (j - 1) x) ∨
      (P.entryVal x < -P.e j ∧ chainSgn j x = -chainSgn (j - 1) x)) ∧
    ∀ l < P.t, chainSgn j (ChainEntry.block j l) = 1
def ChainSignNoneAbove.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, 1 ≤ j → j ≤ P.m →
    ∀ x ∈ P.entries (j - 1), -P.e j < P.entryVal x → chainSgn (j - 1) x = 1
def ChainNuBound.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, j ≤ P.m →
    (P.nu j : ℚ) ≤ (P.m : ℚ) / 2 ∧ (P.m : ℚ) / 2 < (P.t : ℚ) / 2 ∧
      (1 ≤ j → (P.nu j : ℚ) ≤ (P.m : ℚ) / 2 - 1)
def ChainLemmaSigns.Statement : Prop :=
  ChainSignsInitialDifferential.Statement ∧ ChainSignCount.Statement ∧ ChainSignRule.Statement ∧
    ChainSignNoneAbove.Statement ∧ ChainNuBound.Statement
def ChainCentreModulus.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, 1 ≤ j → j ≤ P.m →
    ∀ x ∈ P.entries (j - 1),
      ((P.t : ℚ) + 3) / 2 ≤ |((P.entryVal x + P.e j : ℤ) : ℚ)| ∧
      ((P.entryVal x + P.e j : ℤ) : ℚ) ≠ ((P.t : ℚ) + 1) / 2 ∧
      ((P.entryVal x + P.e j : ℤ) : ℚ) ≠ -(((P.t : ℚ) + 1) / 2)
def ChainGaps.Statement : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, 1 ≤ j → j ≤ P.m →
    (∀ i ∈ ({j - 1, j} : Finset ℕ), ∀ x ∈ P.entries i, ∀ y ∈ P.entries i,
      chainSgn i x = 1 → chainSgn i y = -1 →
        P.h0 ≤ |P.entryVal x - P.entryVal y| ∧
        (120 : ℝ) * (P.rk (j - 1) : ℝ) * (P.nu (j - 1) : ℝ) ^ ((3 : ℝ) / 2) ≤
          ((|P.entryVal x - P.entryVal y| : ℤ) : ℝ)) ∧
    ((P.h0 : ℚ) - P.t) / 2 < P.h0 ∧
    ((P.NF : ℚ)) ^ 3 < ((P.h0 : ℚ) - P.t) / 2 ∧
    P.rk j ^ 3 ≤ P.NF ^ 3
def ChainLemmaGaps.Statement : Prop :=
  ChainCentreModulus.Statement ∧ ChainGaps.Statement
def chainParams_2_2_9 : ChainParams where
  k := 2
  m := 2
  t := 9
  s := 0
  h0 := 42616
  v := fun i => 3 - (i : ℤ)
  b := fun i => ((i : ℤ) - 1) * 42616
  e := fun i => ((i : ℤ) - 1) * 42616 + 6
  k_even := ⟨1, rfl⟩
  m_even := ⟨1, rfl⟩
  two_le_k := le_refl _
  two_le_m := le_refl _
  t_odd := ⟨4, rfl⟩
  t_ge := by norm_num
  v_anti := by intro i h1 h2; omega
  cloud_above := by norm_num
  low_above_centre := by intro j _ _; omega
  centre_above_low := by intro j _ _; push_cast; omega
  lower_gap_bound := by intro j _ _; norm_num
  upper_gap_bound := by intro j _ _; push_cast; norm_num; linarith
  height_le_block_spacing := by intro i _ _; push_cast; linarith
  height_ge_first_cubic_bound := by norm_num
  height_ge_second_cubic_bound := by norm_num
def chainParams_4_4_13 : ChainParams where
  k := 4
  m := 4
  t := 13
  s := 0
  h0 := 864032
  v := fun i => 5 - (i : ℤ)
  b := fun i => ((i : ℤ) - 1) * 864032
  e := fun i => ((i : ℤ) - 1) * 864032 + 8
  k_even := ⟨2, rfl⟩
  m_even := ⟨2, rfl⟩
  two_le_k := by norm_num
  two_le_m := by norm_num
  t_odd := ⟨6, rfl⟩
  t_ge := by norm_num
  v_anti := by intro i h1 h2; omega
  cloud_above := by norm_num
  low_above_centre := by intro j _ _; omega
  centre_above_low := by intro j _ _; push_cast; omega
  lower_gap_bound := by intro j _ _; norm_num
  upper_gap_bound := by intro j _ _; push_cast; norm_num; linarith
  height_le_block_spacing := by intro i _ _; push_cast; linarith
  height_ge_first_cubic_bound := by norm_num
  height_ge_second_cubic_bound := by norm_num
def exampleChainParams : ChainParams where
  k := 2
  m := 2
  t := 9
  s := 9
  h0 := 128010
  v := fun i => 3 - (i : ℤ)
  b := fun i => ((i : ℤ) - 1) * 128010
  e := fun i => ((i : ℤ) - 1) * 128010 + 6
  k_even := ⟨1, rfl⟩
  m_even := ⟨1, rfl⟩
  two_le_k := le_refl _
  two_le_m := le_refl _
  t_odd := ⟨4, rfl⟩
  t_ge := by norm_num
  v_anti := by intro i h1 h2; omega
  cloud_above := by norm_num
  low_above_centre := by intro j _ _; omega
  centre_above_low := by intro j _ _; push_cast; omega
  lower_gap_bound := by intro j _ _; norm_num
  upper_gap_bound := by intro j _ _; push_cast; norm_num; linarith
  height_le_block_spacing := by intro i _ _; push_cast; linarith
  height_ge_first_cubic_bound := by norm_num
  height_ge_second_cubic_bound := by norm_num
example : exampleChainParams.Nm = 22 ∧ exampleChainParams.NF = 40 := by
  decide
example : exampleChainParams.h0 <
    4 * (exampleChainParams.NF : ℤ) ^ 3 + 2 * exampleChainParams.t + 6 := by
  decide
end GroundTheory.Heights₂.Theta


