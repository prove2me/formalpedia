-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:41.096344+00:00
-- url     : https://prove2.me/theorems/7c01c30d-e0c7-4caa-9690-f89ae32dd08d
-- title:
--   Lower Step Statement
-- statement:
--   Definitions and structural lemmas for Lower Step Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/LowerStepStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
def IsHCPar {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)
def parEps (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun a => if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)
def parLam (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if h : a.val < k - 1 then v ⟨a.val, h⟩
    else -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩
def lamT (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if h : a.val < k then u ⟨a.val, h⟩ - 1 / 2
    else -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ - ((a.val - (k - 1) : ℕ) : ℝ) * (t : ℝ)
def Interlaces (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ hk : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩
def HalfInts (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (i : Fin k) (s : Fin (2 * r + k + 1)), ∃ m : ℤ, u i - parLam k r v b s = (m : ℝ) + 1 / 2
def LowGaps (r : ℕ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j
def StepClosed {n k : ℕ} (ε : Fin n → Bool) (u : Fin k → ℝ) (h : ℝ) (P : (Fin n → ℝ) → Prop) : Prop :=
  (∀ (lam : Fin n → ℝ) (s : Fin n), IsHCPar lam → GapAtLeast ε lam h →
      IsHCPar (lam - Pi.single s 1) → GapAtLeast ε (lam - Pi.single s 1) h →
      (∀ j, u j ≠ lam s - 1 / 2) → P lam → P (lam - Pi.single s 1)) ∧
    ∀ (lam : Fin n → ℝ) (s : Fin n), IsHCPar lam → GapAtLeast ε lam h →
      IsHCPar (lam + Pi.single s 1) → GapAtLeast ε (lam + Pi.single s 1) h →
      (∀ j, u j ≠ lam s + 1 / 2) → P lam → P (lam + Pi.single s 1)
def WalkStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (t : ℕ)
    (P : (Fin (2 * r + k + 1) → ℝ) → Prop),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    StepClosed (parEps k r) u h P → P (lamT k r u b t) → P (parLam k r v b)
def raisePar (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if h : a.val < k then u ⟨a.val, h⟩ - 1 / 2
    else if a.val - (k - 1) < j then -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩
    else -b ⟨a.val - (k - 1), by have := a.isLt; omega⟩ - ((a.val - (k - 1) : ℕ) : ℝ) * (t : ℝ)
def walkPar (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (i : ℕ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun a => if h : a.val < i ∧ a.val < k then u ⟨a.val, h.2⟩ - 1 / 2 else parLam k r v b a
def AdjGapStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), StrictAnti lam →
    (∀ (a : Fin n) (ha : a.val + 1 < n), ε a ≠ ε ⟨a.val + 1, ha⟩ → h ≤ lam a - lam ⟨a.val + 1, ha⟩) →
    GapAtLeast ε lam h
def SegStatement : Prop :=
  ∀ (n : ℕ) (Q : (Fin n → ℝ) → Prop) (x : Fin n → ℝ) (s : Fin n) (d : ℝ) (N : ℕ), Q x →
    (∀ j : ℕ, j < N → Q (x + ((j : ℝ) * d) • Pi.single s 1) →
      Q (x + (((j : ℝ) + 1) * d) • Pi.single s 1)) →
    Q (x + ((N : ℝ) * d) • Pi.single s 1)
def EndsStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (t : ℕ),
    lamT k r u b t = raisePar k r u b t 1 ∧ raisePar k r u b t (2 * r + 2) = walkPar k r u v b k ∧
      walkPar k r u v b 0 = parLam k r v b
def RaiseStepStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (t : ℕ)
    (P : (Fin (2 * r + k + 1) → ℝ) → Prop),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    StepClosed (parEps k r) u h P →
    ∀ j : ℕ, 1 ≤ j → j ≤ 2 * r + 1 → P (raisePar k r u b t j) → P (raisePar k r u b t (j + 1))
def LowerStepStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ)
    (P : (Fin (2 * r + k + 1) → ℝ) → Prop),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    StepClosed (parEps k r) u h P →
    ∀ i : ℕ, i < k → P (walkPar k r u v b (i + 1)) → P (walkPar k r u v b i)
end ReciprocityTheory.ChartRestriction.DS.Lap


