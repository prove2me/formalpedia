-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
-- name    : Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:10:56.086391+00:00
-- url     : https://prove2.me/theorems/b99406ed-2f23-44a2-88aa-0864588c51cf
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/TimeClaims/Sec3/Definitions.lean

import Definitions.Def_Submission_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
set_option autoImplicit false
section
namespace ThreeSumApsp
structure DetTimeModel where
  /-- Theorem 5: given `X ∈ ℤ^{N×D}`, `Y ∈ ℤ^{D×N}` with entries of absolute value at most
  `u` and a set of at most `w` positions, compute the wanted entries of `XY` (`IsWantedEntries`).
  The arguments of the time are `N D w u`. -/
  thinProduct : (ℕ → ℕ → ℕ → ℝ → ℝ) → Prop
  /-- #Lop-AE-SparseTri(n, D), Definition 14, with at most `w` query pairs
  (`LopInstance.IsCountingAnswer`).  The arguments of the time are `n D w`. -/
  lopCount : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Lop-AE-SparseTri(n, D), Definition 13, with at most `w` query pairs
  (`LopInstance.IsDetectionAnswer`).  The arguments of the time are `n D w`. -/
  lopDetect : (ℕ → ℕ → ℕ → ℝ) → Prop
  /-- Exact Triangle on `n` vertices per part with integer weights of absolute value at most `u`
  (`TriangleInstance.HasZeroTriangle`).  The arguments of the time are `n u`. -/
  exactTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Negative Triangle, decision (`TriangleInstance.HasNegativeTriangle`).  Arguments `n u`. -/
  negativeTriangle : (ℕ → ℝ → ℝ) → Prop
  /-- Convolution-3SUM on `N` integers of absolute value at most `u` (`Convolution3SUM`).  Arguments
  `N u`. -/
  convolution3SUM : (ℕ → ℝ → ℝ) → Prop
  /-- 3SUM on `n` integers of absolute value at most `u` (`ThreeSum`).  Arguments `n u`. -/
  threeSum : (ℕ → ℝ → ℝ) → Prop
  /-- The (min,+)-product of two `n × n` integer matrices with entries of absolute value at most `u`
  (`IsMinPlusProduct`). Arguments `n u`. -/
  minPlusProduct : (ℕ → ℝ → ℝ) → Prop
  /-- APSP on directed `n`-vertex graphs with integer weights of absolute value at most `u` and no
  negative cycles (`IsDistanceMatrix`, `NoNegativeCycle`).  Arguments `n u`. -/
  apsp : (ℕ → ℝ → ℝ) → Prop
noncomputable abbrev thinBound (n D : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.log D ^ 2 / (D : ℝ) ^ (1 / 18 : ℝ)
noncomputable abbrev splitBound (n D w : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 + (w : ℝ) * Real.sqrt D) * Real.log D ^ 2 / (D : ℝ) ^ (1 / 18 : ℝ)
noncomputable abbrev wantedBound (n D w : ℕ) : ℝ :=
  (w : ℝ) * (D : ℝ) ^ (0.437 : ℝ) + (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ)
namespace Closure
def MonoExactTriangle (M : DetTimeModel) : Prop :=
  ∀ T T' : ℕ → ℝ → ℝ, (∀ (s : ℕ) (u : ℝ), 1 ≤ s → 1 ≤ u → T s u ≤ T' s u) →
    M.exactTriangle T → M.exactTriangle T'
def ChooseBySize (M : DetTimeModel) : Prop :=
  ∀ n₀ : ℕ, ∃ C₀ : ℝ, ∀ T₁ T₂ : ℕ → ℝ → ℝ, M.exactTriangle T₁ → M.exactTriangle T₂ →
    M.exactTriangle fun n u => (if n < n₀ then T₁ n u else T₂ n u) + C₀
end Closure
namespace Claim
def Theorem_5 (M : DetTimeModel) : Prop :=
  ∀ c : ℝ, ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), (∃ k : ℕ, D = 4 ^ k) → 4 ≤ D → D ^ 18 ≤ N →
      (w : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D →
      u ≤ (N : ℝ) ^ c → T N D w u ≤ C * thinBound N D
def BruteForce (M : DetTimeModel) : Prop :=
  ∃ C : ℝ, M.exactTriangle fun n u => C * ((n : ℝ) ^ 3 * (1 + logU u))
def LopCountFromThinProduct (M : DetTimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ → ℝ, M.thinProduct T →
    M.lopCount fun n D w => T n D w 1 + C₀ * ((n : ℝ) * (D : ℝ) + (w : ℝ) + 1)
def LopDetectFromCount (M : DetTimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopCount T →
    M.lopDetect fun n D w => T n D w + C₀ * ((w : ℝ) + 1)
def LopSplit (M : DetTimeModel) : Prop :=
  ∃ C₀ : ℝ, ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopCount T →
    M.lopCount fun n D w =>
      (⌈(w : ℝ) / (splitCap n D : ℝ)⌉₊ : ℝ) *
          (T n D (splitCap n D) + C₀ * ((n : ℝ) * (D : ℝ) + 1)) +
        C₀ * ((w : ℝ) + 1)
def Theorem_17 (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (D n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))
def ApspFromMinPlus (M : DetTimeModel) : Prop :=
  ∃ c C₀ : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, M.minPlusProduct T →
    M.apsp fun n u =>
      ((Nat.clog 2 n : ℝ) + 1) *
        (T n (c * ((n : ℝ) * u)) + C₀ * ((n : ℝ) ^ 2 * (1 + logU (c * ((n : ℝ) * u)))))
def CH20_Theorem_5_1 (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (N : ℕ → ℕ) (c' κ' : ℝ),
    IsPowPolylog E (3 / 2) ∧ IsPowPolylog Num 0 ∧ IsPowPolylog (fun n => (N n : ℝ)) 1 ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ N n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.convolution3SUM T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (N n) (mag n)
def VW13_Theorem_4_3 (M : DetTimeModel) : Prop :=
  ∃ (c : ℝ) (E Num : ℕ → ℝ) (size : ℕ → ℕ), 1 ≤ c ∧
    IsPowLittleO E (3 / 2) ∧ IsBigOPow Num (1 / 2) ∧ IsBigOPow (fun N => (size N : ℝ)) (1 / 2) ∧
    (∀ N : ℕ, 1 ≤ N → 1 ≤ size N) ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      M.convolution3SUM fun N u => E N * (1 + logU u) + Num N * T (size N) (c * u)
def VW13_Theorem_3_3 (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ 2 ≤ C ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    M.negativeTriangle fun s U => C * (T s (c * U) * logU U)
def VW18_Theorem_4_2 (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ 0 ≤ C ∧ ∀ T' : ℕ → ℝ → ℝ, GoodTime T' → M.negativeTriangle T' →
    ∃ T'' : ℕ → ℝ → ℝ, M.minPlusProduct T'' ∧
      ∀ (n : ℕ) (U : ℝ), 1 ≤ n → 1 ≤ U →
        T'' n U ≤ C * ((n : ℝ) ^ 2 * T' (cbrtCeil n) (c * U) * logU U)
def Corollary_26_wanted (M : DetTimeModel) : Prop :=
  ∀ c : ℝ, ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ D → D ^ 18 ≤ N → u ≤ (N : ℝ) ^ c →
      T N D w u ≤ C * wantedBound N D w
def Corollary_15_first (M : DetTimeModel) : Prop :=
  ∃ (C : ℝ) (Tc Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopCount Tc ∧ M.lopDetect Td ∧
    ∀ n D w : ℕ, (∃ k : ℕ, D = 4 ^ k) → 4 ≤ D → D ^ 18 ≤ n → (w : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D →
      Tc n D w ≤ C * thinBound n D ∧ Td n D w ≤ C * thinBound n D
def Corollary_15_general (M : DetTimeModel) : Prop :=
  ∃ (C : ℝ) (Tc Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopCount Tc ∧ M.lopDetect Td ∧
    ∀ n D w : ℕ, (∃ k : ℕ, D = 4 ^ k) → 4 ≤ D → D ^ 18 ≤ n →
      Tc n D w ≤ C * splitBound n D w ∧ Td n D w ≤ C * splitBound n D w
def Corollary_16 (M : DetTimeModel) : Prop :=
  ∃ (C : ℝ) (Tc Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopCount Tc ∧ M.lopDetect Td ∧
    ∀ n D w : ℕ, 1 ≤ D → D ^ 18 ≤ n →
      Tc n D w ≤ C * wantedBound n D w ∧ Td n D w ≤ C * wantedBound n D w
def Theorem_19_explicit (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ (K : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))
def Theorem_19_first (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 1 ≤ κ → ∃ (C : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    ∀ᶠ n : ℕ in Filter.atTop, T n ((n : ℝ) ^ κ) ≤ C * ((n : ℝ) ^ (3 - 1 / 648 : ℝ) * Real.log n ^ 2)
def Theorem_19_second (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 1 ≤ κ → ∃ (C : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    (∀ᶠ n : ℕ in Filter.atTop, T n ((n : ℝ) ^ κ) ≤ C * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n)) ∧
    UpperBigOPow (fun n => T n ((n : ℝ) ^ κ)) (3 - 0.0017)
def ExactTriangleUniform (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ M.exactTriangle (uniformTime K δ e)
def Theorem_21a (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (E Num mag : ℕ → ℝ) (size : ℕ → ℕ) (c' κ' : ℝ),
    IsPowLittleO E (3 / 2) ∧ IsPowLittleO Num (1 / 2) ∧
    IsPowLittleO (fun n => (size n : ℝ)) (1 / 2) ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ size n ∧ 1 ≤ mag n ∧ mag n ≤ c' * (n : ℝ) ^ κ') ∧
    ∀ T : ℕ → ℝ → ℝ, M.exactTriangle T →
      ∃ T' : ℕ → ℝ → ℝ, M.threeSum T' ∧
        ∀ n : ℕ, 1 ≤ n → T' n ((n : ℝ) ^ κ) ≤ E n + Num n * T (size n) (mag n)
def Theorem_21b_minPlus (M : DetTimeModel) : Prop :=
  ∃ c C : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    ∃ T' : ℕ → ℝ → ℝ, M.minPlusProduct T' ∧
      ∀ (n : ℕ) (U : ℝ), 1 ≤ n → 1 ≤ U →
        T' n U ≤ C * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c * U) * logU U ^ 2)
def Theorem_21b_apsp (M : DetTimeModel) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ c C : ℝ, 1 ≤ c ∧ ∀ T : ℕ → ℝ → ℝ, GoodTime T → M.exactTriangle T →
    ∃ T' : ℕ → ℝ → ℝ, M.apsp T' ∧
      ∀ n : ℕ, 2 ≤ n →
        T' n ((n : ℝ) ^ κ)
          ≤ C * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c * (n : ℝ) ^ (κ + 1)) * Real.log n ^ 3)
def SolvedAlongPow (S : (ℕ → ℝ → ℝ) → Prop) (Cls : (ℕ → ℝ) → ℝ → Prop) (a : ℝ) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ T : ℕ → ℝ → ℝ, S T ∧ Cls (fun n => T n ((n : ℝ) ^ κ)) a
abbrev ExactTriangleIn (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.exactTriangle UpperBigOPow a
abbrev ThreeSumInLittleO (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.threeSum UpperPowLittleO a
abbrev MinPlusInPolylog (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.minPlusProduct UpperPowPolylog a
abbrev ApspInPolylog (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.apsp UpperPowPolylog a
end Claim
end ThreeSumApsp


