-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCleanParams20261120
-- name    : LinearSetReconciliation327_Main_HintCleanParams20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:08:58.55282+00:00
-- url     : https://prove2.me/theorems/ef6946a0-b329-47c0-8999-003686abebb8
-- title:
--   LinearSetReconciliation327 — HintCleanParams (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCleanParams20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLayout20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5920261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream51020261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5420261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5620261120
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
lemma one_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ lg (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hn : (2 : ℝ) ≤ (n : ℝ))
  have h2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  rw [h2] at h
  exact h
lemma allSome_spec {α : Type 1} {k : ℕ} (f : Fin k → Option α) (g : Fin k → α)
    (h : HintParams.allSome f = some g) : ∀ s, f s = some (g s) := by
  intro s
  unfold HintParams.allSome at h
  split at h
  · rename_i hsome
    have hfun : (fun s => (f s).get (hsome s)) = g := Option.some.inj h
    rw [← congrFun hfun s]
    exact (Option.some_get (hsome s)).symm
  · exact absurd h (by simp)
lemma rule_direct_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .direct) :
    (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) ∧
      (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (HintParams.D N X Y : ℝ) ∧
      P.rows X Y ≠ Y := by
  unfold HintParams.rule at h
  by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : (HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : P.rows X Y = Y
      · rw [if_pos h3] at h
        exact absurd h (by decide)
      · rw [if_neg h3] at h
        exact ⟨not_le.mp h1, not_le.mp h2, h3⟩
lemma rule_recursive_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .recursive) :
    ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) ∧
      ¬ ((HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2) ∧
      P.rows X Y = Y := by
  unfold HintParams.rule at h
  by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : (HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : P.rows X Y = Y
      · exact ⟨h1, h2, h3⟩
      · rw [if_neg h3] at h
        exact absurd h (by decide)
lemma one_le_Y_of_recursive {P : HintParams} {N X Y : ℕ} (hL1 : 1 ≤ P.lgn)
    (hcf : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10))
    (hrowsY : P.rows X Y = Y) : 1 ≤ Y := by
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hD1 : (1 : ℝ) ≤ (HintParams.D N X Y : ℝ) := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) / P.lgn ^ 10 := div_nonneg (by positivity) (pow_nonneg hLn 10)
    have h1 : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hcf
    have h2 : (0 : ℝ) < (HintParams.D N X Y : ℝ) := lt_of_le_of_lt h0 h1
    have h3 : (0 : ℕ) < HintParams.D N X Y := by exact_mod_cast h2
    exact_mod_cast h3
  rcases Nat.eq_zero_or_pos Y with h0 | hpos
  · exfalso
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
      have hDle : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
        have h : HintParams.D N X Y ≤ X + Y := min_le_right _ _
        exact_mod_cast h
      rw [h0] at hD1 hDle
      push_cast at hDle
      linarith only [hD1, hDle]
    have hc1 : 1 ≤ ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := by
      have h3 : (0 : ℝ) < P.lgn ^ 3 := pow_pos hL0 3
      have hpos2 : (0 : ℝ) < (X : ℝ) / P.lgn ^ 3 := div_pos (by linarith only [hX1]) h3
      have h := Nat.le_ceil ((X : ℝ) / P.lgn ^ 3)
      have h2 : (0 : ℝ) < ((⌈(X : ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hpos2 h
      exact_mod_cast h2
    have hc0 : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ = 0 := by
      have h : P.rows X 0 = 0 := by rw [← h0]; exact hrowsY
      unfold HintParams.rows at h
      have h' : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ 0 := by
        calc ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ max 0 ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := le_max_right _ _
          _ = 0 := h
      omega
    omega
  · exact hpos
lemma one_le_rows_of_ne {P : HintParams} {X Y : ℕ} (h : P.rows X Y ≠ Y) : 1 ≤ P.rows X Y := by
  unfold HintParams.rows at h ⊢
  by_cases hc : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ = 0
  · rw [hc, Nat.max_zero] at h
    exact absurd rfl h
  · have h1 : 0 < ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := Nat.pos_of_ne_zero hc
    exact le_trans h1 (le_max_right _ _)
lemma tree_N (P : HintParams) (fuel : ℕ) :
    ∀ (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → T.N = N := by
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        rfl
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        rfl
      · simp only [hr] at h
        obtain ⟨child, -, hT⟩ := Option.map_eq_some_iff.mp h
        subst hT
        rfl
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        rfl
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
theorem upTreeStatic_tree (CR : CRFamily) (P : HintParams) (Bc : ℕ)
    (hCR : ∀ N t, N ≤ P.n → t ≤ N → UpCRColumns CR Bc N t) (fuel : ℕ) :
    ∀ N X Y T, P.NodeArgs N X Y → P.tree fuel N X Y = some T →
      UpTreeStatic CR Bc P.n T := by
  induction fuel with
  | zero => intro N X Y T hargs ht; simp [HintParams.tree] at ht
  | succ f ih =>
      intro N X Y T hargs ht
      obtain ⟨hn, hl, hN1, hNn, hXN, hYN⟩ := hargs
      simp only [HintParams.tree] at ht
      cases hr : P.rule N X Y
      · simp only [hr] at ht
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using ht.symm
        subst T
        exact ⟨hNn, hCR N _ hNn (min_le_left _ _)⟩
      · simp only [hr] at ht
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using ht.symm
        subst T
        exact ⟨hNn, hCR N _ hNn (min_le_left _ _)⟩
      · simp only [hr] at ht
        obtain ⟨child, hsome, hT⟩ := Option.map_eq_some_iff.mp ht
        rw [← hT]
        have hrs := rule_recursive_spec hr
        have hY1 := one_le_Y_of_recursive (one_le_lg hn) hrs.1 hrs.2.2
        refine ⟨hNn, ?_, hCR N _ hNn (min_le_left _ _), ?_⟩
        · change 0 < P.rows X Y
          rw [hrs.2.2]
          omega
        · intro s
          have hs := allSome_spec _ _ hsome s
          constructor
          · exact (tree_N P f Y _ _ (child s) hs).trans hrs.2.2.symm
          · exact ih Y _ _ (child s)
              ⟨hn, hl, hY1, hYN.trans hNn, min_le_left _ _, min_le_left _ _⟩ hs
      · simp only [hr] at ht
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using ht.symm
        subst T
        exact ⟨hNn, one_le_rows_of_ne (rule_direct_spec hr).2.2,
          hCR N _ hNn (min_le_left _ _)⟩
end LinearSetReconciliation327.Main.HintCleanParams
end
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
def hintW (K : ℝ) (n : ℕ) : ℕ := 1024 * (⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1)
lemma two_pow_hintW (K : ℝ) (n : ℕ) :
    2 ^ hintW K n = (2 * 2 ^ Nat.clog 2 (n + 2)) ^ (1024 * (⌈K⌉₊ + 2)) := by
  have hbase : 2 ^ (Nat.clog 2 (n + 2) + 1) = 2 * 2 ^ Nat.clog 2 (n + 2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [hintW, Nat.mul_comm (1024 * (⌈K⌉₊ + 2)) (Nat.clog 2 (n + 2) + 1), Nat.pow_mul, hbase]
theorem hintLen_succ_add_one_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl
lemma lg_le_two_mul (x : ℝ) (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, div_le_iff₀ h0]
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  nlinarith [Real.log_two_gt_d9]
lemma lg_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x :=
  Real.logb_nonneg (by norm_num) hx
lemma pow_le_two_pow_hintW (K : ℝ) (n a : ℕ) (ha : a ≤ 1024 * (⌈K⌉₊ + 2)) :
    (n + 2) ^ a ≤ 2 ^ hintW K n := by
  have hbase : n + 2 ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := by
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
    omega
  rw [two_pow_hintW]
  exact le_trans (Nat.pow_le_pow_right (by omega) ha) (Nat.pow_le_pow_left hbase _)
lemma sum_schemeCount (sch : RowScheme) (child : Fin sch.ℓ → Node) :
    ((List.ofFn fun s : Fin sch.ℓ => (schemeNodes (child s)).length)).sum
      = ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length :=
  List.sum_ofFn
lemma schemeNodes_length_recursive (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) :
    (schemeNodes (.recursive sch t Xs Ys child)).length
      = 1 + ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length := by
  have h1 : ((List.ofFn fun s : Fin sch.ℓ => schemeNodes (child s)).flatten).length
      = ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length := by
    rw [List.length_flatten, List.map_ofFn]
    exact sum_schemeCount sch child
  rw [schemeNodes, List.length_append, List.length_cons, List.length_nil, h1]
lemma schemeCount_le_nodeCount (T : Node) : (schemeNodes T).length ≤ Node.nodeCount T := by
  induction T with
  | store N => simp [schemeNodes, Node.nodeCount]
  | cr N t => simp [schemeNodes, Node.nodeCount]
  | direct sch t => simp [schemeNodes, Node.nodeCount]
  | recursive sch t Xs Ys child ih =>
      rw [schemeNodes_length_recursive]
      simp only [Node.nodeCount]
      have h2 : (∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) ≤
          ∑ s : Fin sch.ℓ, Node.nodeCount (child s) := Finset.sum_le_sum fun s _ => ih s
      omega
def decCnt (CR : CRFamily) (Bc colBase : ℕ) : Node → ℕ
  | .store N => N
  | .cr _ _ => 1
  | .direct sch _ => sch.m * sch.ℓ + 1
  | .recursive sch _ _ _ child => (∑ s : Fin sch.ℓ, decCnt CR Bc colBase (child s)) + 1
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
theorem up_rows_le_N (P : HintParams) (N X Y : ℕ) (hLog : 1 ≤ P.lgn)
    (hX : X ≤ N) (hY : Y ≤ N) : P.rows X Y ≤ N := by
  unfold HintParams.rows
  apply max_le hY
  apply Nat.ceil_le.mpr
  exact (div_le_self (Nat.cast_nonneg X) (one_le_pow₀ hLog)).trans (by exact_mod_cast hX)
theorem up_nmax_le_N (P : HintParams) (N X Y : ℕ) (hm : 1 ≤ P.rows X Y) :
    schemeNmax (P.scheme N X Y) ≤ N := by
  change ⌈(N : ℝ) / (P.rows X Y : ℝ)⌉₊ ≤ N
  apply Nat.ceil_le.mpr
  exact div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hm)
theorem upDims_actual_tree (P : HintParams) (Bell fuel : ℕ) :
    ∀ N X Y T, P.NodeArgs N X Y → P.tree fuel N X Y = some T →
      UpEllOK Bell T → UpDimsBound (max P.n Bell) T := by
  induction fuel with
  | zero => intro N X Y T ha ht he; simp [HintParams.tree] at ht
  | succ f ih =>
      intro N X Y T hargs ht he
      obtain ⟨hn, hl, hN1, hNn, hXN, hYN⟩ := hargs
      simp only [HintParams.tree] at ht
      have hLog : 1 ≤ P.lgn := one_le_lg hn
      have hmN := up_rows_le_N P N X Y hLog hXN hYN
      cases hr : P.rule N X Y
      · simp only [hr] at ht
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using ht.symm
        subst T
        exact hNn.trans (le_max_left _ _)
      · simp only [hr] at ht
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using ht.symm
        subst T
        exact hNn.trans (le_max_left _ _)
      · simp only [hr] at ht
        obtain ⟨child, hsome, hT⟩ := Option.map_eq_some_iff.mp ht
        rw [← hT] at he ⊢
        have hrs := rule_recursive_spec hr
        have hY1 := one_le_Y_of_recursive hLog hrs.1 hrs.2.2
        have hm1 : 1 ≤ P.rows X Y := by rw [hrs.2.2]; exact hY1
        have hV := up_nmax_le_N P N X Y hm1
        refine ⟨hNn.trans (le_max_left _ _), (hmN.trans hNn).trans (le_max_left _ _),
          he.1.trans (le_max_right _ _), (hV.trans hNn).trans (le_max_left _ _), ?_⟩
        intro s
        exact ih Y _ _ (child s)
          ⟨hn, hl, hY1, hYN.trans hNn, min_le_left _ _, min_le_left _ _⟩
          (allSome_spec _ _ hsome s) (he.2 s)
      · simp only [hr] at ht
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using ht.symm
        subst T
        have hm1 := one_le_rows_of_ne (rule_direct_spec hr).2.2
        have hV := up_nmax_le_N P N X Y hm1
        exact ⟨hNn.trans (le_max_left _ _), (hmN.trans hNn).trans (le_max_left _ _),
          he.trans (le_max_right _ _), (hV.trans hNn).trans (le_max_left _ _)⟩
theorem UpDimsBound.scheme_members {Q : ℕ} : ∀ T, UpDimsBound Q T →
    ∀ v ∈ schemeNodes T,
      v.N ≤ Q ∧ nodeM v ≤ Q ∧ nodeEll v ≤ Q ∧ nodeNmax v ≤ Q := by
  intro T
  induction T with
  | store N => intro h v hv; simp [schemeNodes] at hv
  | cr N t => intro h v hv; simp [schemeNodes] at hv
  | direct sch t =>
      intro h v hv
      simp only [schemeNodes, List.mem_singleton] at hv
      subst v
      exact h
  | recursive sch t Xs Ys child ih =>
      intro h v hv
      rcases List.mem_append.mp hv with hv | hv
      · rw [List.mem_singleton] at hv
        subst v
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      · obtain ⟨L, hL, hv⟩ := List.mem_flatten.mp hv
        obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hL
        exact ih s (h.2.2.2.2 s) v hv
theorem upSpecFits_of_dims (T : Node) (Q W : ℕ) (hQ : 1 ≤ Q)
    (hD : UpDimsBound Q T) (hNc : T.nodeCount ≤ 2 ^ W)
    (hCube : Q ^ 3 ≤ 2 ^ W) (hTwo : 2 ≤ 2 ^ W) : (hintSpec T).Fits W := by
  have hS := (schemeCount_le_nodeCount T).trans hNc
  have hQ3 : Q ≤ Q ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hQ (by norm_num : 1 ≤ (3 : ℕ))
  have hMem := UpDimsBound.scheme_members T hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hintSpec, permSizesOf, List.length_map] using hS
  · simpa only [hintSpec, coeffShapesOf, List.length_map] using hS
  · intro a ha
    change a ∈ (schemeNodes T).map Node.N at ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact (hMem v hv).1.trans (hQ3.trans hCube)
  · intro p hp
    change p ∈ (schemeNodes T).map nodeCoins at hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hN, hm, hl, hv⟩ := hMem v hv
    refine ⟨?_, hTwo⟩
    change nodeM v * nodeEll v * nodeNmax v ≤ 2 ^ W
    calc
      nodeM v * nodeEll v * nodeNmax v ≤ Q * Q * Q := Nat.mul_le_mul (Nat.mul_le_mul hm hl) hv
      _ = Q ^ 3 := by ring
      _ ≤ 2 ^ W := hCube
theorem up_commonDim_cube_word (E K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hEK : E ≤ K) :
    (max n ⌈(E + 1) * lg (n : ℝ) ^ 3⌉₊) ^ 3 ≤ 2 ^ hintW K n := by
  let c := ⌈K⌉₊
  let b := n + 2
  have hb : 1 ≤ b := by dsimp only [b]; omega
  have h2b : 2 ≤ b := by dsimp only [b]; omega
  have hEc : E + 1 ≤ ((c + 1 : ℕ) : ℝ) := by
    have h := hEK.trans (Nat.le_ceil K)
    push_cast
    linarith only [h]
  have hcp : c + 1 ≤ b ^ c := (hintLen_succ_add_one_le_two_pow c).trans (Nat.pow_le_pow_left h2b c)
  have hEP : E + 1 ≤ ((b ^ c : ℕ) : ℝ) := hEc.trans (by exact_mod_cast hcp)
  have hLog0 : 0 ≤ lg (n : ℝ) := lg_nonneg_of_one_le (by exact_mod_cast (by omega : 1 ≤ n))
  have hLog : lg (n : ℝ) ≤ ((b ^ 2 : ℕ) : ℝ) := by
    have h := lg_le_two_mul (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp only [b]
    push_cast
    nlinarith only [h, hn0, sq_nonneg (n : ℝ)]
  have hLog3 : lg (n : ℝ) ^ 3 ≤ ((b ^ 6 : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ hLog0 hLog 3
    calc
      lg (n : ℝ) ^ 3 ≤ (((b ^ 2 : ℕ) : ℝ)) ^ 3 := h
      _ = ((b ^ 6 : ℕ) : ℝ) := by push_cast; ring
  have hCeil : ⌈(E + 1) * lg (n : ℝ) ^ 3⌉₊ ≤ b ^ (c + 6) := by
    apply Nat.ceil_le.mpr
    calc
      (E + 1) * lg (n : ℝ) ^ 3 ≤ ((b ^ c : ℕ) : ℝ) * ((b ^ 6 : ℕ) : ℝ) :=
        mul_le_mul hEP hLog3 (by positivity) (Nat.cast_nonneg _)
      _ = ((b ^ (c + 6) : ℕ) : ℝ) := by push_cast; rw [pow_add]
  have hnPow : n ≤ b ^ (c + 6) := by
    calc
      n ≤ b := by dsimp only [b]; omega
      _ = b ^ 1 := (pow_one _).symm
      _ ≤ b ^ (c + 6) := Nat.pow_le_pow_right hb (by omega)
  calc
    (max n ⌈(E + 1) * lg (n : ℝ) ^ 3⌉₊) ^ 3 ≤ (b ^ (c + 6)) ^ 3 :=
      Nat.pow_le_pow_left (max_le hnPow hCeil) 3
    _ = b ^ ((c + 6) * 3) := by rw [pow_mul]
    _ ≤ 2 ^ hintW K n := pow_le_two_pow_hintW K n ((c + 6) * 3) (by dsimp only [c]; omega)
theorem upSpecFits_actual_tree (P : HintParams) (E K : ℝ) (fuel N X Y : ℕ) (T : Node)
    (hArgs : P.NodeArgs N X Y) (hTree : P.tree fuel N X Y = some T)
    (hEll : UpEllOK ⌈(E + 1) * lg (P.n : ℝ) ^ 3⌉₊ T)
    (hNc : T.nodeCount ≤ 2 ^ hintW K P.n) (hEK : E ≤ K) :
    (hintSpec T).Fits (hintW K P.n) := by
  have hDims := upDims_actual_tree P _ fuel N X Y T hArgs hTree hEll
  have hWpos : 1 ≤ hintW K P.n := by
    unfold hintW
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  apply upSpecFits_of_dims T _ _ (by have h := hArgs.1; omega) hDims hNc
    (up_commonDim_cube_word E K P.n hArgs.1 hEK)
  simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hWpos
theorem up_nodeCount_le_counter (CR : CRFamily) (Bc U colBase : ℕ) :
    ∀ T, UpTreeStatic CR Bc U T → 0 < T.N → T.nodeCount ≤ decCnt CR Bc colBase T := by
  intro T
  induction T with
  | store N => intro hs hN; exact hN
  | cr N t => intro hs hN; exact le_rfl
  | direct sch t => intro hs hN; change 1 ≤ sch.m * sch.ℓ + 1; omega
  | recursive sch t Xs Ys child ih =>
      intro hs hN
      have hSum : (∑ s, (child s).nodeCount) ≤ ∑ s, decCnt CR Bc colBase (child s) := by
        apply Finset.sum_le_sum
        intro s _
        apply ih s (hs.2.2.2 s).2
        rw [(hs.2.2.2 s).1]
        exact hs.2.1
      change 1 + (∑ s, (child s).nodeCount) ≤ (∑ s, decCnt CR Bc colBase (child s)) + 1
      omega
end LinearSetReconciliation327.Main.HintCleanParams
end
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
universe u
def hintCu (K : ℝ) : ℝ := (2 : ℝ) ^ 30 * (K + 1) ^ 4
def hintpu : ℕ := 1024
lemma n_le_two_pow_hintW (K : ℝ) (n : ℕ) : n ≤ 2 ^ hintW K n := by
  rw [two_pow_hintW]
  have h1 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) (n + 2)
  have h2 : n + 2 ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := by omega
  have hm : 1 ≤ 1024 * (⌈K⌉₊ + 2) := Nat.mul_pos (by norm_num) (by omega)
  calc n ≤ n + 2 := by omega
    _ ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := h2
    _ ≤ (2 * 2 ^ Nat.clog 2 (n + 2)) ^ (1024 * (⌈K⌉₊ + 2)) := by
        refine le_trans (le_of_eq (Nat.pow_one _).symm) ?_
        exact Nat.pow_le_pow_right (by omega) hm
lemma lg_add_two_le {n : ℕ} (hn : 2 ≤ n) : lg ((n : ℝ) + 2) ≤ lg (n : ℝ) + 1 := by
  have hmono : lg ((n : ℝ) + 2) ≤ lg (2 * (n : ℝ)) := by
    refine Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) ?_
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmul : lg (2 * (n : ℝ)) = lg (n : ℝ) + 1 := by
    have h : Real.logb 2 (2 * (n : ℝ)) = Real.logb 2 (2 : ℝ) + Real.logb 2 (n : ℝ) :=
      Real.logb_mul (by norm_num) (by positivity)
    rw [Real.logb_self_eq_one (by norm_num)] at h
    simp only [lg]
    linarith
  linarith
noncomputable def hintLenK₁₀ : ℝ := Classical.choose LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10
noncomputable def hintLenA₀₁₀ : ℕ := Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2
noncomputable def hintLenK₅₉ (KCR : ℝ) : ℝ := Classical.choose (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)
noncomputable def hintLenA₀₅₉ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).2
noncomputable def hintLenA₀₅₄ : ℕ := Classical.choose LinearSetReconciliation327.Main.HintUpstream54.lemma_5_4
noncomputable def hintLenA₀₅₆ : ℕ := Classical.choose LinearSetReconciliation327.Main.HintUpstream56.lemma_5_6
noncomputable def hintLenA (KCR : ℝ) : ℕ :=
  max (max (max (max (hintLenA₀₅₉ KCR) (hintLenA₀₁₀)) (hintLenA₀₅₄)) (hintLenA₀₅₆)) 100
theorem le_hintLenA₅₉ (KCR : ℝ) : hintLenA₀₅₉ KCR ≤ hintLenA KCR := by
  unfold hintLenA; omega
theorem le_hintLenA₁₀ (KCR : ℝ) : hintLenA₀₁₀ ≤ hintLenA KCR := by
  unfold hintLenA; omega
theorem le_hintLenA₅₄ (KCR : ℝ) : hintLenA₀₅₄ ≤ hintLenA KCR := by
  unfold hintLenA; omega
theorem le_hintLenA₅₆ (KCR : ℝ) : hintLenA₀₅₆ ≤ hintLenA KCR := by
  unfold hintLenA; omega
noncomputable def hintLenC₀₅₉ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).2
    (hintLenA KCR) (le_hintLenA₅₉ KCR))
noncomputable def hintLenC₀₁₀ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2
    (hintLenA KCR) (le_hintLenA₁₀ KCR))
noncomputable def hintLenC₀₅₄ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream54.lemma_5_4 (hintLenA KCR) (le_hintLenA₅₄ KCR))
noncomputable def hintLenC₀₅₆ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream56.lemma_5_6 (hintLenA KCR) (le_hintLenA₅₆ KCR))
noncomputable def hintLenK₁₀bits (KCR : ℝ) : ℕ :=
  8 * Nat.clog 2 (⌈hintLenK₁₀⌉₊ + 2)
noncomputable def hintLenC (KCR : ℝ) : ℕ :=
  max (max (max (hintLenC₀₅₉ KCR) (hintLenC₀₁₀ KCR)) (max (hintLenC₀₅₄ KCR) (hintLenC₀₅₆ KCR)))
    (max (48 * (hintLenA KCR + 40 + 2)) (hintLenK₁₀bits KCR + 3 * hintLenA KCR + 40))
theorem le_hintLenC₁₀ (KCR : ℝ) : hintLenC₀₁₀ KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega
theorem lemma_5_10_at (KCR : ℝ) :
    ∀ (n lam N X Y : ℕ),
      (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).NodeArgs N X Y →
      ∃ (fuel : ℕ) (T : Node), (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).tree fuel N X Y
          = some T ∧
        (fuel : ℝ) ≤ hintLenK₁₀ * (lg (lg n) + 1) ∧
        (T.depth : ℝ) ≤ hintLenK₁₀ * (lg (lg n) + 1) ∧
        (T.recursiveCount : ℝ) ≤ hintLenK₁₀ * lg n ^ 13 ∧
        (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27 :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2
      (hintLenA KCR) (le_hintLenA₁₀ KCR))
    (hintLenC KCR) (le_hintLenC₁₀ KCR)
noncomputable def hintLenK (KCR : ℝ) : ℝ := hintLenK₅₉ KCR + hintLenK₁₀ + max KCR 0 + 1
theorem hintLenK_pos (KCR : ℝ) : 0 < hintLenK KCR := by
  have h1 : 0 < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : 0 < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  unfold hintLenK
  linarith
noncomputable def hintLenE (KCR : ℝ) : ℕ := 48 * (hintLenA KCR + hintLenC KCR + 2)
lemma lg_two : lg 2 = 1 := by
  rw [lg_eq_log_div,
    div_self (ne_of_gt (by linarith [Real.log_two_gt_d9] : (0 : ℝ) < Real.log 2))]
lemma lg_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : lg (x * y) = lg x + lg y := by
  simp only [lg, Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]
lemma lg_pow_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  rw [lg_eq_log_div, lg_eq_log_div, Real.log_pow]
  push_cast
  field_simp
lemma lg_sixteen : lg (16 : ℝ) = 4 := by
  have h : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h, lg_pow_pos (by norm_num)]
  simp [lg_two]
lemma lg_exp_one_le_two : lg (Real.exp 1) ≤ 2 := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, Real.log_exp, div_le_iff₀ h0]
  linarith [Real.log_two_gt_d9]
lemma inv_eta_sq (P : HintParams) : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := by
  have hL : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  rw [hL, inv_pow, inv_inv, ← pow_mul]
  congr 1
  omega
lemma rows_le_N {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn) (hXN : X ≤ N) (hYN : Y ≤ N) :
    P.rows X Y ≤ N := by
  unfold HintParams.rows
  refine max_le hYN ?_
  rw [Nat.ceil_le]
  have h3 : (1 : ℝ) ≤ P.lgn ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ P.lgn ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < P.lgn ^ 3)]
  have hX : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  nlinarith
lemma Nmax_le_N {P : HintParams} {N X Y : ℕ} : P.Nmax N X Y ≤ N := by
  unfold HintParams.Nmax
  rw [Nat.ceil_le]
  rcases Nat.eq_zero_or_pos (P.rows X Y) with hm | hm
  · rw [hm]; simp
  · have hmR : (0 : ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm
    rw [div_le_iff₀ hmR]
    have hm1 : (1 : ℝ) ≤ (P.rows X Y : ℝ) := by exact_mod_cast hm
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith
lemma wordsOf_le_self {W M : ℕ} (hW : 1 ≤ W) : wordsOf W M ≤ M := by
  have hW0 : 0 < W := by omega
  unfold wordsOf
  have h1 : (M + W - 1) / W < M + 1 := by
    rw [Nat.div_lt_iff_lt_mul hW0]
    have hm : M ≤ M * W := by
      have h := Nat.mul_le_mul_left M hW
      simpa using h
    have e : M + W - 1 = M + (W - 1) := by omega
    have e2 : (M + 1) * W = M * W + W := by ring
    omega
  omega
lemma one_le_nodeCount (T : Node) : 1 ≤ T.nodeCount := by
  induction T with
  | store N => simp [Node.nodeCount]
  | cr N t => simp [Node.nodeCount]
  | direct sch t => simp [Node.nodeCount]
  | recursive sch t Xs Ys child ih => simp only [Node.nodeCount]; omega
lemma allSome_some {α : Type 1} {k : ℕ} (f : Fin k → Option α) (g : Fin k → α)
    (h : ∀ s, f s = some (g s)) : HintParams.allSome f = some g := by
  have hsome : ∀ s, (f s).isSome := fun s => by rw [h s]; rfl
  unfold HintParams.allSome
  rw [dif_pos hsome]
  have hfun : (fun s => (f s).get (hsome s)) = g := by
    funext s
    simp only [h s]
    rfl
  rw [hfun]
lemma tree_mono (P : HintParams) :
    ∀ (fuel N X Y : ℕ) {T : Node}, P.tree fuel N X Y = some T →
      ∀ g, fuel ≤ g → P.tree g N X Y = some T := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h g hg
      cases g with
      | zero => omega
      | succ g' =>
        have hg' : f ≤ g' := by omega
        simp only [HintParams.tree] at h ⊢
        cases hr : P.rule N X Y
        · simp only [hr] at h ⊢
          exact h
        · simp only [hr] at h ⊢
          exact h
        · simp only [hr] at h ⊢
          have hex : ∃ child : Fin (P.scheme N X Y).ℓ → Node,
              HintParams.allSome (fun s : Fin (P.scheme N X Y).ℓ =>
                P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
              (fun child : Fin (P.scheme N X Y).ℓ → Node =>
                Node.recursive (P.scheme N X Y) (P.resid N X Y)
                  (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
            Option.map_eq_some_iff.mp h
          obtain ⟨chi, hsome, hT⟩ := hex
          have hstep : ∀ s : Fin (P.scheme N X Y).ℓ,
              P.tree g' Y (P.capX N X Y s.val) (P.capY N X Y s.val) = some (chi s) :=
            fun s => ih Y (P.capX N X Y s.val) (P.capY N X Y s.val)
              (allSome_spec _ _ hsome s) g' hg'
          have hsome' : HintParams.allSome (fun s : Fin (P.scheme N X Y).ℓ =>
              P.tree g' Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some chi :=
            allSome_some _ _ hstep
          refine Option.map_eq_some_iff.mpr ⟨chi, hsome', ?_⟩
          exact hT
        · simp only [hr] at h ⊢
          exact h
lemma lgn_nonneg (P : HintParams) : 0 ≤ P.lgn := by
  rcases Nat.eq_zero_or_pos P.n with h | h
  · rw [HintParams.lgn, h]
    simp [lg_eq_log_div]
  · exact lg_nonneg_of_one_le (by exact_mod_cast h)
lemma BX_le_sharp (P : HintParams) (N X Y : ℕ) :
    (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := by
  have h0 : (0 : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 := by
    have h1 := lgn_nonneg P
    positivity
  have h1 : P.BX N X Y ≤ ⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ := by
    unfold HintParams.BX
    exact min_le_right _ _
  have h2 : (P.BX N X Y : ℝ) ≤ ((⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one h0
  linarith only [h2, h3]
lemma BY_le_sharp (P : HintParams) (N X Y : ℕ) :
    (P.BY N X Y : ℝ) ≤ (P.C : ℝ) * lg (P.lgn + 2) + 5 := by
  have hmin : P.BY N X Y ≤ ⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ + 4 := by
    unfold HintParams.BY
    exact min_le_right _ _
  have hcast : (P.BY N X Y : ℝ) ≤ ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) + 4 := by
    exact_mod_cast hmin
  have h0 : (0 : ℝ) ≤ (P.C : ℝ) * lg (P.lgn + 2) := by
    have h1 := lgn_nonneg P
    have h2 : (0 : ℝ) ≤ lg (P.lgn + 2) := lg_nonneg_of_one_le (by linarith)
    positivity
  have hlt := Nat.ceil_lt_add_one h0
  linarith only [hcast, hlt]
lemma ceil_lg_exp_Nmax_le (P : HintParams) (N X Y : ℕ) (hNmax : 1 ≤ P.Nmax N X Y) :
    (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ lg ((P.Nmax N X Y : ℝ)) + 3 := by
  have hNpos : (0 : ℝ) < (P.Nmax N X Y : ℝ) := by exact_mod_cast hNmax
  have hx0 : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := by
    apply lg_nonneg_of_one_le
    have h1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hNmax
    nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hlt := Nat.ceil_lt_add_one hx0
  have hmul : lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) =
      lg (Real.exp 1) + lg (P.Nmax N X Y : ℝ) := lg_mul_pos (Real.exp_pos 1) hNpos
  have hexp := lg_exp_one_le_two
  linarith only [hlt, hmul, hexp]
lemma ceil_lg_eta_inv_sq_le {P : HintParams} (hn : 2 ≤ P.n) :
    (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ 5 + 2 * (P.A : ℝ) * lg (P.lgn) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hpos : (0 : ℝ) < P.lgn ^ (2 * P.A) := by positivity
  have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
    rw [div_eq_mul_inv, inv_eta_sq]
  have hx0 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
    rw [heta]
    apply lg_nonneg_of_one_le
    have h1 : (1 : ℝ) ≤ P.lgn ^ (2 * P.A) := one_le_pow₀ hL1
    nlinarith
  have hlt := Nat.ceil_lt_add_one hx0
  have hlog : lg (16 / P.eta ^ 2) = 4 + 2 * (P.A : ℝ) * lg (P.lgn) := by
    rw [heta, lg_mul_pos (by norm_num) hpos, lg_sixteen, lg_pow_pos hlgn]
    push_cast
    ring
  linarith only [hlt, hlog]
theorem ell_le_four {KCR : ℝ} {P : HintParams}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) {N X Y : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hm1 : 1 ≤ P.rows X Y) :
    (P.ell N X Y : ℝ) ≤ P.lgn ^ 3 + (hintLenE KCR : ℝ) * P.lgn ^ 2 := by
  have hL1 : 1 ≤ P.lgn := one_le_lg hn
  have hL0 : 0 < P.lgn := by linarith
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  have hAr : (P.A : ℝ) = (hintLenA KCR : ℝ) := by rw [hA]
  have hCr : (P.C : ℝ) = (hintLenC KCR : ℝ) := by rw [hC]
  have hL2 : P.lgn ≤ P.lgn ^ 2 := by nlinarith only [hL1]
  have hrowsle : P.rows X Y ≤ N := rows_le_N hL1 hXN hYN
  have hm0 : (0 : ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  have hNmax1 : 1 ≤ P.Nmax N X Y := by
    unfold HintParams.Nmax
    have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have h3 : (1 : ℝ) ≤ (N : ℝ) / (P.rows X Y : ℝ) := by
      rw [le_div_iff₀ hm0]
      have h4 : (P.rows X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrowsle
      linarith
    have h5 := Nat.le_ceil ((N : ℝ) / (P.rows X Y : ℝ))
    have h6 : (1 : ℝ) ≤ ((⌈(N : ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) := le_trans h3 h5
    exact_mod_cast h6
  have hNmaxN : P.Nmax N X Y ≤ N := Nmax_le_N
  have hlgNmax : lg ((P.Nmax N X Y : ℕ) : ℝ) ≤ P.lgn := by
    have hcast : ((P.Nmax N X Y : ℕ) : ℝ) ≤ ((P.n : ℕ) : ℝ) := by
      exact_mod_cast le_trans hNmaxN hNn
    have hpos : (0 : ℝ) < ((P.Nmax N X Y : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((P.Nmax N X Y : ℕ) : ℝ) := by exact_mod_cast hNmax1
      linarith
    exact Real.logb_le_logb_of_le (by norm_num) hpos hcast
  have hce : (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ 4 * P.lgn := by
    have h := ceil_lg_exp_Nmax_le P N X Y hNmax1
    linarith only [h, hlgNmax, hL1]
  have hBX := BX_le_sharp P N X Y
  have hBY := BY_le_sharp P N X Y
  have hBY2 : (P.BY N X Y : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by
    have hlgL2 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := lg_le_two_mul _ (by linarith)
    have h2 : (P.C : ℝ) * lg (P.lgn + 2) ≤ (P.C : ℝ) * (2 * (P.lgn + 2)) :=
      mul_le_mul_of_nonneg_left hlgL2 hC0
    have h4 : (4 : ℝ) * (P.C : ℝ) ≤ 4 * (P.C : ℝ) * P.lgn := by nlinarith only [hC0, hL1]
    nlinarith only [hBY, h2, h4]
  have hBYce : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
      ≤ (24 * (P.C : ℝ) + 20) * P.lgn ^ 2 := by
    have hpos : (0 : ℝ) ≤ (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) := by positivity
    have hnn : (0 : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by nlinarith only [hC0, hL1]
    have h1 : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
        ≤ (6 * (P.C : ℝ) * P.lgn + 5) * (4 * P.lgn) := mul_le_mul hBY2 hce hpos hnn
    have h3 : (20 : ℝ) * P.lgn ≤ 20 * P.lgn ^ 2 := by nlinarith only [hL1]
    nlinarith only [h1, h3]
  have h7 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn ^ 2 := by
    have h6 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn := by nlinarith only [hBY2, hL1]
    nlinarith only [h6, hL2]
  have heta := ceil_lg_eta_inv_sq_le (P := P) hn
  have hlgL : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have heta2 : (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
    have h3 : (5 : ℝ) + 2 * (P.A : ℝ) * lg P.lgn ≤ 5 + 4 * (P.A : ℝ) * P.lgn := by
      nlinarith only [hA0, hlgL]
    have h4 : (5 : ℝ) + 4 * (P.A : ℝ) * P.lgn ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
      nlinarith only [hA0, hL1, hL2]
    linarith only [heta, h3, h4]
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  have hE : (31 * (P.C : ℝ) + 4 * (P.A : ℝ) + 41) ≤ (hintLenE KCR : ℝ) := by
    unfold hintLenE
    rw [hAr, hCr]
    push_cast
    linarith only []
  have h1 : (1 : ℝ) ≤ P.lgn ^ 2 := one_le_pow₀ hL1
  have hB : (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10
      ≤ P.lgn ^ 3 + (hintLenE KCR : ℝ) * P.lgn ^ 2 := by
    have h1' : (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := hBX
    have h8 : (10 : ℝ) ≤ 10 * P.lgn ^ 2 := by linarith only [h1]
    nlinarith only [h1', hBYce, h7, heta2, h8, hE, h1]
  linarith only [hell, hB]
lemma sq_add_one_le_four_sq {L : ℝ} (hL : 1 ≤ L) : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by
  nlinarith only [hL, sq_nonneg (L - 1)]
lemma ell_le_cubic {KCR : ℝ} {P : HintParams}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hn : 2 ≤ P.n) {N X Y : ℕ}
    (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N) (hm1 : 1 ≤ P.rows X Y) :
    (P.ell N X Y : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) ≤ P.lgn := le_of_lt (by linarith only [hL1] : (0 : ℝ) < P.lgn)
  have hell := ell_le_four hA hC hn hN1 hNn hXN hYN hm1
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hL2 : P.lgn ^ 2 ≤ P.lgn ^ 3 := by
    have h0 : (0 : ℝ) ≤ P.lgn ^ 2 := pow_nonneg hL0 2
    nlinarith only [hL1, h0]
  have hE1 : (0 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 :=
    mul_nonneg (by linarith only [hE0]) (pow_nonneg hL0 3)
  nlinarith only [hell, hE0, hL2, hL1, hE1]
noncomputable def hintP (KCR : ℝ) (n lam : ℕ) : HintParams := ⟨hintLenA KCR, hintLenC KCR, n, lam⟩
def NodeShrink (KCR : ℝ) (n : ℕ) : Node → Prop
  | .store N => N ≤ n
  | .cr N t => N ≤ n ∧ t ≤ N
  | .direct sch t => sch.N ≤ n ∧ t ≤ sch.N ∧
      (sch.ℓ : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3
  | .recursive sch t _ _ child => sch.N ≤ n ∧ t ≤ sch.N ∧
      (sch.ℓ : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 ∧
      (∀ s, (child s).N = sch.m) ∧ ∀ s, NodeShrink KCR n (child s)
lemma tree_shrink {KCR : ℝ} {P : HintParams} (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) :
    ∀ (fuel : ℕ) (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T →
      1 ≤ N → N ≤ P.n → X ≤ N → Y ≤ N → NodeShrink KCR P.n T := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hN1 hNn hXN hYN
      simp only [HintParams.tree] at h
      have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        obtain ⟨child, hsome, hT⟩ := Option.map_eq_some_iff.mp h
        subst hT
        have hrowsY : P.rows X Y = Y := (rule_recursive_spec hr).2.2
        have hY1 : 1 ≤ Y := one_le_Y_of_recursive hL1 (rule_recursive_spec hr).1 hrowsY
        have hell : ((P.scheme N X Y).ℓ : ℝ) ≤
            ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 := by
          have hm1 : 1 ≤ P.rows X Y := by rw [hrowsY]; exact hY1
          exact ell_le_cubic hA hC hn hN1 hNn hXN hYN hm1
        refine ⟨hNn, min_le_left _ _, hell, ?_, ?_⟩
        · intro s
          have h1 : (child s).N = Y :=
            tree_N P f Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
              (allSome_spec _ _ hsome s)
          rw [h1]
          exact hrowsY.symm
        · intro s
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s) hY1 (le_trans hYN hNn) (min_le_left _ _) (min_le_left _ _)
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        have hmne : P.rows X Y ≠ Y := (rule_direct_spec hr).2.2
        have hm1 : 1 ≤ P.rows X Y := one_le_rows_of_ne hmne
        have hell : ((P.scheme N X Y).ℓ : ℝ) ≤
            ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 :=
          ell_le_cubic hA hC hn hN1 hNn hXN hYN hm1
        exact ⟨hNn, min_le_left _ _, hell⟩
noncomputable def colBℓ (KCR : ℝ) (n : ℕ) : ℕ :=
  ⌈((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3⌉₊
noncomputable def colBc (KCR : ℝ) (n : ℕ) : ℕ :=
  ⌈max KCR 0 * lg ((n : ℝ) + 2) ^ 2⌉₊
lemma colBℓ_pos {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) : 1 ≤ colBℓ KCR n := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h3 : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hx1 : (1 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 := by
    nlinarith only [hE0, h3]
  have h2 : ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 ≤ ((colBℓ KCR n : ℕ) : ℝ) := by
    unfold colBℓ
    exact Nat.le_ceil _
  have h4 : (1 : ℝ) ≤ ((colBℓ KCR n : ℕ) : ℝ) := le_trans hx1 h2
  exact_mod_cast h4
lemma col_card_le_ceil {KCR : ℝ} {N n : ℕ} {S : Finset ℕ}
    (h : (S.card : ℝ) ≤ KCR * lg ((N : ℝ) + 2) ^ 2) (hNn : N ≤ n) :
    S.card ≤ colBc KCR n := by
  have h2 : (S.card : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 := by
    have hL0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) := by
      apply lg_nonneg_of_one_le
      have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith only [h1]
    have hmono : lg ((N : ℝ) + 2) ≤ lg ((n : ℝ) + 2) := by
      refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
      have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      linarith only [h1]
    have hmono2 : lg ((N : ℝ) + 2) ^ 2 ≤ lg ((n : ℝ) + 2) ^ 2 := by
      nlinarith only [hmono, hL0]
    rcases lt_or_ge KCR 0 with hk | hk
    · have h0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) ^ 2 := by positivity
      have hneg : KCR * lg ((N : ℝ) + 2) ^ 2 ≤ 0 := by nlinarith only [hk, h0]
      have hle0 : (S.card : ℝ) ≤ 0 := le_trans h hneg
      have hge0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
      have hz : (S.card : ℝ) = 0 := le_antisymm hle0 hge0
      rw [hz, max_eq_right (le_of_lt hk)]
      simp
    · rw [max_eq_left hk]
      exact le_trans h (mul_le_mul_of_nonneg_left hmono2 hk)
  have h3 : (S.card : ℝ) ≤ ((colBc KCR n : ℕ) : ℝ) := by
    refine le_trans h2 ?_
    unfold colBc
    exact Nat.le_ceil _
  exact_mod_cast h3
noncomputable def hintColK (KCR : ℝ) : ℝ :=
  hintLenK KCR + (hintLenA KCR : ℝ) + (hintLenE KCR : ℝ) + 1
theorem hintLenK₁₀_le_hintColK (KCR : ℝ) : hintLenK₁₀ ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4, h5]
theorem hintLenA_le_hintColK (KCR : ℝ) : (hintLenA KCR : ℝ) ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4]
theorem hintLenE_le_hintColK (KCR : ℝ) : (hintLenE KCR : ℝ) ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4]
theorem maxKCR_le_hintColK (KCR : ℝ) : max KCR 0 ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h4, h5]
lemma colB_sum_le {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)
      ≤ ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) * lg (n : ℝ) ^ 3 := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hKr0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hB1 : (colBℓ KCR n : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 1 := by
    have hx0 : (0 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 := by positivity
    have h := Nat.ceil_lt_add_one hx0
    unfold colBℓ
    linarith only [h]
  have hB2 : (colBc KCR n : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 + 1 := by
    have hx0 : (0 : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) ^ 2 := by positivity
      positivity
    have h := Nat.ceil_lt_add_one hx0
    unfold colBc
    linarith only [h]
  have hlg2 : lg ((n : ℝ) + 2) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := by
    have h1 : lg ((n : ℝ) + 2) ≤ lg (n : ℝ) + 1 := lg_add_two_le hn
    have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
      apply lg_nonneg_of_one_le
      have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith only [h3]
    have h2 : lg ((n : ℝ) + 2) ^ 2 ≤ (lg (n : ℝ) + 1) ^ 2 := by nlinarith only [h1, h0, hL1]
    have h3 : (lg (n : ℝ) + 1) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := sq_add_one_le_four_sq hL1
    linarith only [h2, h3]
  have hB2' : (colBc KCR n : ℝ) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) + 1 := by
    have h3 : max KCR 0 * lg ((n : ℝ) + 2) ^ 2 ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlg2 hKr0
    linarith only [hB2, h3]
  have h4 : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have h5 : (1 : ℝ) ≤ lg (n : ℝ) ^ 2 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 2 := pow_le_pow_right₀ hL1 (by norm_num)
  have h6 : max KCR 0 * (4 * lg (n : ℝ) ^ 2) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by
    have h8 : lg (n : ℝ) ^ 2 ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 3)
    have h7 : (4 : ℝ) * lg (n : ℝ) ^ 2 ≤ 4 * lg (n : ℝ) ^ 3 := by linarith only [h8]
    exact mul_le_mul_of_nonneg_left h7 hKr0
  nlinarith only [hB1, hB2', h6, h4, hE0, hKr0, hL1]
theorem depth_le_three {K : ℝ} {n : ℕ} {T : Node} (hn : 2 ≤ n) (hK : 0 ≤ K)
    (hd : (T.depth : ℝ) ≤ K * (lg (lg (n : ℝ)) + 1)) :
    (T.depth : ℝ) ≤ 3 * K * lg (n : ℝ) := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have h2 : lg (lg (n : ℝ)) ≤ 2 * lg (n : ℝ) := lg_le_two_mul (lg (n : ℝ)) hL1
  have h3 : (0 : ℝ) ≤ lg (lg (n : ℝ)) := lg_nonneg_of_one_le hL1
  nlinarith only [hd, h2, hL1, h3, hK]
theorem upSteps_leFix {KCR : ℝ} {n : ℕ} {T : Node} (hn : 2 ≤ n)
    (hnc : (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27)
    (hd : (T.depth : ℝ) ≤ hintLenK₁₀ * (lg (lg (n : ℝ)) + 1)) :
    ((125 * (T.nodeCount * (T.depth + colBℓ KCR n + colBc KCR n)) + 12 : ℕ) : ℝ)
      ≤ hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hKc1 : (1 : ℝ) ≤ hintColK KCR := by
    have h1 : (0 : ℝ) ≤ hintLenK KCR := le_of_lt (hintLenK_pos KCR)
    have h2 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
    unfold hintColK
    linarith only [h1, h2, h3]
  have hA0 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hKr0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ hintLenK₁₀ := le_of_lt (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have hd3 : (T.depth : ℝ) ≤ 3 * hintLenK₁₀ * lg (n : ℝ) := depth_le_three hn hK0 hd
  have hBsum := colB_sum_le (KCR := KCR) hn
  have hB0 : (0 : ℝ) ≤ (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ) := by
    have h1 : (0 : ℝ) ≤ (colBℓ KCR n : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (colBc KCR n : ℝ) := by positivity
    linarith only [h1, h2]
  have hlg1 : (0 : ℝ) ≤ lg (n : ℝ) := by linarith only [hL1]
  have hlg3 : lg (n : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc lg (n : ℝ) = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hD : (T.depth : ℝ) + ((colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
      ≤ (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) * lg (n : ℝ) ^ 3 := by
    have h1 : 3 * hintLenK₁₀ * lg (n : ℝ) ≤ 3 * hintLenK₁₀ * lg (n : ℝ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left hlg3
      linarith only [hK0]
    have h3 : (0 : ℝ) ≤ lg (n : ℝ) ^ 3 := by positivity
    nlinarith only [hd3, hBsum, h1, h3, hE0, hKr0, hK0, hlg1]
  have hkey : (T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
      ≤ (hintLenK₁₀ * (hintLenA KCR : ℝ)
          * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3))) * lg (n : ℝ) ^ 30 := by
    have hD' : (T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)
        ≤ (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) * lg (n : ℝ) ^ 3 := by
      linarith only [hD]
    have h1 : (T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
        ≤ (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27)
          * ((3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) * lg (n : ℝ) ^ 3) := by
      apply mul_le_mul hnc hD'
      · linarith only [hd3, hBsum, hK0, hE0, hKr0, hlg1]
      · have hz : (0 : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27 := by positivity
        exact hz
    have h2 : (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27)
          * ((3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) * lg (n : ℝ) ^ 3)
        = (hintLenK₁₀ * (hintLenA KCR : ℝ)
          * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3))) * lg (n : ℝ) ^ 30 := by
      rw [show (30 : ℕ) = 27 + 3 from rfl, pow_add]
      ring
    rw [h2] at h1
    exact h1
  have hC0 : 3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)
      ≤ 10 * (hintColK KCR + 1) := by
    have h1 := hintLenK₁₀_le_hintColK KCR
    have h2 := hintLenE_le_hintColK KCR
    have h3 := maxKCR_le_hintColK KCR
    linarith only [h1, h2, h3, hKc1]
  have hC00 : (0 : ℝ) ≤ 3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) := by
    linarith only [hK0, hE0, hKr0]
  have hKA : hintLenK₁₀ * (hintLenA KCR : ℝ)
      ≤ (hintColK KCR + 1) * (hintColK KCR + 1) := by
    have h2 : hintLenK₁₀ ≤ hintColK KCR + 1 := by linarith only [hintLenK₁₀_le_hintColK KCR, hKc1]
    have h3 : (hintLenA KCR : ℝ) ≤ hintColK KCR + 1 := by
      linarith only [hintLenA_le_hintColK KCR, hKc1]
    exact mul_le_mul h2 h3 hA0 (by linarith only [hKc1])
  have hconst : 137 * (hintLenK₁₀ * (hintLenA KCR : ℝ)
        * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)))
      ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4 := by
    have hX1 : (1 : ℝ) ≤ hintColK KCR + 1 := by linarith only [hKc1]
    have hmul : hintLenK₁₀ * (hintLenA KCR : ℝ)
          * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3))
        ≤ ((hintColK KCR + 1) * (hintColK KCR + 1)) * (10 * (hintColK KCR + 1)) := by
      apply mul_le_mul hKA hC0 hC00
      positivity
    have h1000 : (137 : ℝ) * 10 ≤ (2 : ℝ) ^ 30 := by norm_num
    have h3 : (hintColK KCR + 1) ^ 3 ≤ (hintColK KCR + 1) ^ 4 := by
      have := pow_le_pow_right₀ hX1 (by norm_num : 3 ≤ 4)
      simpa using this
    have h4 : 137 * (((hintColK KCR + 1) * (hintColK KCR + 1)) * (10 * (hintColK KCR + 1)))
        ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4 := by
      nlinarith only [h1000, h3, hX1]
    linarith only [hmul, h4]
  have hY1 : (1 : ℝ) ≤ (T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (T.nodeCount : ℝ) := by exact_mod_cast one_le_nodeCount T
    have h2 : (1 : ℝ) ≤ (T.depth : ℝ) := by exact_mod_cast one_le_depth T
    have h3 : (1 : ℝ) ≤ (colBℓ KCR n : ℝ) := by exact_mod_cast colBℓ_pos hn
    have h4 : (0 : ℝ) ≤ (colBc KCR n : ℝ) := by positivity
    have h5 : (1 : ℝ) ≤ (T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ) := by linarith only [h2, h3, h4]
    have h6 : (0 : ℝ) ≤ (T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ) := by linarith only [h5]
    have h7 : (0 : ℝ) ≤ (T.nodeCount : ℝ) := by linarith only [h1]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)) :=
          mul_le_mul h1 h5 (by norm_num) h7
  have hlgpu : lg (n : ℝ) ^ 30 ≤ lg (n : ℝ) ^ hintpu := by
    have hle : (30 : ℕ) ≤ hintpu := by unfold hintpu; norm_num
    exact pow_le_pow_right₀ hL1 hle
  have hP0 : (0 : ℝ) ≤ lg (n : ℝ) ^ 30 := by positivity
  calc ((125 * (T.nodeCount * (T.depth + colBℓ KCR n + colBc KCR n)) + 12 : ℕ) : ℝ)
      = 125 * ((T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))) + 12 := by
        push_cast
        ring
    _ ≤ 137 * ((T.nodeCount : ℝ) * ((T.depth : ℝ) + (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))) := by
        nlinarith only [hY1]
    _ ≤ 137 * ((hintLenK₁₀ * (hintLenA KCR : ℝ)
          * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3))) * lg (n : ℝ) ^ 30) := by
        exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = (137 * (hintLenK₁₀ * (hintLenA KCR : ℝ)
          * (3 * hintLenK₁₀ + ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)))) * lg (n : ℝ) ^ 30 := by
        ring
    _ ≤ ((2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4) * lg (n : ℝ) ^ 30 :=
        mul_le_mul_of_nonneg_right hconst hP0
    _ ≤ ((2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4) * lg (n : ℝ) ^ hintpu := by
        have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4 := by positivity
        exact mul_le_mul_of_nonneg_left hlgpu h0
    _ = hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu := by
        unfold hintCu
        ring
theorem decCnt_le_synLen (CR : CRFamily) (Bc colBase : ℕ) (T : Node) :
    decCnt CR Bc colBase T ≤ synLen CR T + T.nodeCount := by
  induction T with
  | store N =>
      simp only [decCnt, synLen, Node.nodeCount]
      omega
  | cr N t =>
      simp only [decCnt, synLen, Node.nodeCount]
      omega
  | direct sch t =>
      simp only [decCnt, synLen, Node.nodeCount]
      omega
  | recursive sch t Xs Ys child ih =>
      have hsum : (∑ s : Fin sch.ℓ, decCnt CR Bc colBase (child s))
          ≤ (∑ s : Fin sch.ℓ, synLen CR (child s))
            + ∑ s : Fin sch.ℓ, (child s).nodeCount := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun s _ => ih s
      simp only [decCnt, synLen, Node.nodeCount]
      omega
def decTSum (CR : CRFamily) (Bc colBase : ℕ) : Node → ℕ
  | .store _ => 0
  | .cr _ t => t
  | .direct _ t => t
  | .recursive sch t _ _ child => (∑ s : Fin sch.ℓ, decTSum CR Bc colBase (child s)) + t
def decKb (KCR : ℝ) (n : ℕ) : ℕ := colBℓ KCR n + colBc KCR n + 2
theorem hintLenK₁₀_pos : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
theorem rows_le_mul_colBc {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) {N t : ℕ} {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hNn : N ≤ n) (ht : t ≤ N) : CR.rows N t ≤ N * colBc KCR n := by
  have hL0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) := by
    apply lg_nonneg_of_one_le
    have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith only [h1]
  have hmono : lg ((N : ℝ) + 2) ≤ lg ((n : ℝ) + 2) := by
    refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
    have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    linarith only [h1]
  have hsq : lg ((N : ℝ) + 2) ^ 2 ≤ lg ((n : ℝ) + 2) ^ 2 := by
    nlinarith only [hmono, hL0]
  have htN : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast ht
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hstep : (CR.rows N t : ℝ) ≤ max KCR 0 * ((N : ℝ) * lg ((n : ℝ) + 2) ^ 2) := by
    rcases lt_or_ge KCR 0 with hk | hk
    · have h0 : (0 : ℝ) ≤ (t : ℝ) * lg ((N : ℝ) + 2) ^ 2 := by positivity
      have hle : KCR * ((t : ℝ) * lg ((N : ℝ) + 2) ^ 2) ≤ 0 := by nlinarith only [hk, h0]
      have h2 : (CR.rows N t : ℝ) ≤ 0 := le_trans (hrows N t ht) hle
      have h3 : (0 : ℝ) ≤ max KCR 0 * ((N : ℝ) * lg ((n : ℝ) + 2) ^ 2) := by
        have hm : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
        have hq : (0 : ℝ) ≤ (N : ℝ) * lg ((n : ℝ) + 2) ^ 2 := by positivity
        exact mul_nonneg hm hq
      linarith only [h2, h3]
    · have hkk : KCR ≤ max KCR 0 := le_max_left _ _
      have hcd : (t : ℝ) * lg ((N : ℝ) + 2) ^ 2 ≤ (N : ℝ) * lg ((n : ℝ) + 2) ^ 2 := by
        have h2 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) ^ 2 := by positivity
        exact mul_le_mul htN hsq h2 hN0
      have h1 : KCR * ((t : ℝ) * lg ((N : ℝ) + 2) ^ 2)
          ≤ max KCR 0 * ((N : ℝ) * lg ((n : ℝ) + 2) ^ 2) :=
        mul_le_mul hkk hcd (by positivity) (le_max_right _ _)
      exact le_trans (hrows N t ht) h1
  have h5 : max KCR 0 * lg ((n : ℝ) + 2) ^ 2 ≤ ((colBc KCR n : ℕ) : ℝ) := by
    unfold colBc
    exact Nat.le_ceil _
  have h6 : (CR.rows N t : ℝ) ≤ (N : ℝ) * ((colBc KCR n : ℕ) : ℝ) := by
    have h4 : max KCR 0 * ((N : ℝ) * lg ((n : ℝ) + 2) ^ 2)
        = (N : ℝ) * (max KCR 0 * lg ((n : ℝ) + 2) ^ 2) := by ring
    rw [h4] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left h5 hN0)
  have h7 : ((N * colBc KCR n : ℕ) : ℝ) = (N : ℝ) * ((colBc KCR n : ℕ) : ℝ) := by
    push_cast
    ring
  have h8 : (CR.rows N t : ℝ) ≤ ((N * colBc KCR n : ℕ) : ℝ) := by
    rw [h7]
    exact h6
  exact_mod_cast h8
theorem tree_cost {KCR : ℝ} {P : HintParams} (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    ∀ (fuel : ℕ) (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T →
      1 ≤ N → N ≤ P.n → X ≤ N → Y ≤ N →
        synLen CR T + T.nodeCount + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) T
          ≤ decKb KCR P.n * N * T.nodeCount := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hN1 hNn hXN hYN
      simp only [HintParams.tree] at h
      have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
      have hkb : colBc KCR P.n + 2 ≤ decKb KCR P.n := by
        unfold decKb
        omega
      have hkb' : colBℓ KCR P.n + colBc KCR P.n + 2 ≤ decKb KCR P.n := by
        unfold decKb
        omega
      have hcr2 : CR.rows N (HintParams.D N X Y) + 1 + HintParams.D N X Y ≤ decKb KCR P.n * N := by
        have htN : HintParams.D N X Y ≤ N := min_le_left _ _
        have hrows1 : CR.rows N (HintParams.D N X Y) ≤ N * colBc KCR P.n :=
          rows_le_mul_colBc hn hrows hNn htN
        have h1 : CR.rows N (HintParams.D N X Y) + 1 + HintParams.D N X Y
            ≤ N * colBc KCR P.n + N + N := by omega
        have h3 : N * colBc KCR P.n + N + N ≤ N * (colBc KCR P.n + 2) := by
          rw [Nat.mul_add]
          omega
        have h4 : N * (colBc KCR P.n + 2) ≤ N * decKb KCR P.n := Nat.mul_le_mul_left N hkb
        have h5 : N * decKb KCR P.n = decKb KCR P.n * N := Nat.mul_comm _ _
        omega
      cases hr : P.rule N X Y
      ·
        simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        simp only [synLen, decTSum, Node.nodeCount, Nat.mul_one]
        exact hcr2
      ·
        simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        simp only [synLen, decTSum, Node.nodeCount, Nat.mul_one]
        exact hcr2
      ·
        simp only [hr] at h
        obtain ⟨child, hsome, hT⟩ := Option.map_eq_some_iff.mp h
        subst hT
        simp only [synLen, decTSum, Node.nodeCount]
        have hrowsY : P.rows X Y = Y := (rule_recursive_spec hr).2.2
        have hY1 : 1 ≤ Y := one_le_Y_of_recursive hL1 (rule_recursive_spec hr).1 hrowsY
        have hYN' : Y ≤ P.n := le_trans hYN hNn
        have hchild : ∀ s : Fin (P.ell N X Y),
            synLen CR (child s) + (child s).nodeCount
                + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s)
              ≤ decKb KCR P.n * Y * (child s).nodeCount :=
          fun s => ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s) hY1 hYN' (min_le_left _ _) (min_le_left _ _)
        have hsum : (∑ s : Fin (P.ell N X Y),
              (synLen CR (child s) + (child s).nodeCount
                + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s)))
            ≤ decKb KCR P.n * Y * (∑ s : Fin (P.ell N X Y), (child s).nodeCount) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun s _ => hchild s
        have hsum2 : (∑ s : Fin (P.ell N X Y),
              (synLen CR (child s) + (child s).nodeCount
                + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s)))
            ≤ decKb KCR P.n * N * (∑ s : Fin (P.ell N X Y), (child s).nodeCount) :=
          le_trans hsum (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hYN))
        have htN : P.resid N X Y ≤ N := min_le_left _ _
        have hrows1 : CR.rows N (P.resid N X Y) ≤ N * colBc KCR P.n :=
          rows_le_mul_colBc hn hrows hNn htN
        have hbase : CR.rows N (P.resid N X Y) + 1 + P.resid N X Y ≤ decKb KCR P.n * N := by
          have h1 : CR.rows N (P.resid N X Y) + 1 + P.resid N X Y
              ≤ N * colBc KCR P.n + N + N := by omega
          have h3 : N * colBc KCR P.n + N + N ≤ N * (colBc KCR P.n + 2) := by
            rw [Nat.mul_add]
            omega
          have h4 : N * (colBc KCR P.n + 2) ≤ N * decKb KCR P.n := Nat.mul_le_mul_left N hkb
          have h5 : N * decKb KCR P.n = decKb KCR P.n * N := Nat.mul_comm _ _
          omega
        have hL : (∑ s : Fin (P.ell N X Y), synLen CR (child s)) + CR.rows (P.scheme N X Y).N (P.resid N X Y)
              + (1 + ∑ s : Fin (P.ell N X Y), (child s).nodeCount)
              + ((∑ s : Fin (P.ell N X Y), decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s))
                  + P.resid N X Y)
            = (∑ s : Fin (P.ell N X Y),
                (synLen CR (child s) + (child s).nodeCount
                  + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s)))
              + (CR.rows (P.scheme N X Y).N (P.resid N X Y) + 1 + P.resid N X Y) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          ring
        refine le_trans (le_of_eq hL) ?_
        calc (∑ s : Fin (P.ell N X Y),
                (synLen CR (child s) + (child s).nodeCount
                  + decTSum CR (colBc KCR P.n) (colBℓ KCR P.n) (child s)))
              + (CR.rows N (P.resid N X Y) + 1 + P.resid N X Y)
            ≤ decKb KCR P.n * N * (∑ s : Fin (P.ell N X Y), (child s).nodeCount)
                + decKb KCR P.n * N := Nat.add_le_add hsum2 hbase
          _ = decKb KCR P.n * N
                * (1 + ∑ s : Fin (P.ell N X Y), (child s).nodeCount) := by ring
      ·
        simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        simp only [synLen, decTSum, Node.nodeCount, Nat.mul_one]
        have hmne : P.rows X Y ≠ Y := (rule_direct_spec hr).2.2
        have hm1 : 1 ≤ P.rows X Y := one_le_rows_of_ne hmne
        have hell : ((P.scheme N X Y).ℓ : ℝ) ≤
            ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 :=
          ell_le_cubic hA hC hn hN1 hNn hXN hYN hm1
        have hℓ : (P.scheme N X Y).ℓ ≤ colBℓ KCR P.n := by
          have hc : ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 ≤ ((colBℓ KCR P.n : ℕ) : ℝ) := by
            unfold colBℓ
            exact Nat.le_ceil _
          have h2 : ((P.scheme N X Y).ℓ : ℝ) ≤ ((colBℓ KCR P.n : ℕ) : ℝ) := le_trans hell hc
          exact_mod_cast h2
        have hmN : P.rows X Y ≤ N := rows_le_N hL1 hXN hYN
        have hmul : (P.scheme N X Y).m * (P.scheme N X Y).ℓ ≤ N * colBℓ KCR P.n :=
          Nat.mul_le_mul hmN hℓ
        have htN : P.resid N X Y ≤ N := min_le_left _ _
        have hrows1 : CR.rows N (P.resid N X Y) ≤ N * colBc KCR P.n :=
          rows_le_mul_colBc hn hrows hNn htN
        have h1 : (P.scheme N X Y).m * (P.scheme N X Y).ℓ + CR.rows N (P.resid N X Y)
            + 1 + P.resid N X Y ≤ N * colBℓ KCR P.n + N * colBc KCR P.n + N + N := by omega
        have h2 : N * colBℓ KCR P.n + N * colBc KCR P.n + N + N
            ≤ N * (colBℓ KCR P.n + colBc KCR P.n + 2) := by
          rw [Nat.mul_add, Nat.mul_add]
          omega
        have h3 : N * (colBℓ KCR P.n + colBc KCR P.n + 2) ≤ N * decKb KCR P.n :=
          Nat.mul_le_mul_left N hkb'
        have h4 : N * decKb KCR P.n = decKb KCR P.n * N := Nat.mul_comm _ _
        exact le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq h4)))
theorem decKb_le_lg_pow {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    ((decKb KCR n : ℕ) : ℝ)
      ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3 := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hM0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hT1 : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hBℓ : ((colBℓ KCR n : ℕ) : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 1 := by
    have hx0 : (0 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 := by positivity
    have h := Nat.ceil_lt_add_one hx0
    unfold colBℓ
    linarith only [h]
  have hBc : ((colBc KCR n : ℕ) : ℝ) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) + 1 := by
    have hlg2 : lg ((n : ℝ) + 2) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := by
      have h1 : lg ((n : ℝ) + 2) ≤ lg (n : ℝ) + 1 := lg_add_two_le hn
      have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
        apply lg_nonneg_of_one_le
        have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith only [h3]
      have h2 : lg ((n : ℝ) + 2) ^ 2 ≤ (lg (n : ℝ) + 1) ^ 2 := by nlinarith only [h1, h0, hL1]
      have h3 : (lg (n : ℝ) + 1) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := sq_add_one_le_four_sq hL1
      linarith only [h2, h3]
    have hx : max KCR 0 * lg ((n : ℝ) + 2) ^ 2 ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlg2 hM0
    have hx0 : (0 : ℝ) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) := by
      have h3 : (0 : ℝ) ≤ lg (n : ℝ) ^ 2 := by positivity
      have h4 : (0 : ℝ) ≤ 4 * lg (n : ℝ) ^ 2 := by linarith only [h3]
      exact mul_nonneg hM0 h4
    have h := Nat.ceil_lt_add_one hx0
    have hmono : ((⌈max KCR 0 * lg ((n : ℝ) + 2) ^ 2⌉₊ : ℕ) : ℝ)
        ≤ ((⌈max KCR 0 * (4 * lg (n : ℝ) ^ 2)⌉₊ : ℕ) : ℝ) := by
      have h2 : ⌈max KCR 0 * lg ((n : ℝ) + 2) ^ 2⌉₊ ≤ ⌈max KCR 0 * (4 * lg (n : ℝ) ^ 2)⌉₊ :=
        Nat.ceil_mono hx
      exact_mod_cast h2
    unfold colBc
    linarith only [h, hmono]
  have hkb : ((decKb KCR n : ℕ) : ℝ)
      ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 1
        + (max KCR 0 * (4 * lg (n : ℝ) ^ 2) + 1) + 2 := by
    have h5 : ((decKb KCR n : ℕ) : ℝ)
        = ((colBℓ KCR n : ℕ) : ℝ) + ((colBc KCR n : ℕ) : ℝ) + 2 := by
      unfold decKb
      push_cast
      ring
    linarith only [h5, hBℓ, hBc]
  have h5 : max KCR 0 * (4 * lg (n : ℝ) ^ 2) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by
    have h8 : lg (n : ℝ) ^ 2 ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have h7 : (4 : ℝ) * lg (n : ℝ) ^ 2 ≤ 4 * lg (n : ℝ) ^ 3 := by linarith only [h8]
    exact mul_le_mul_of_nonneg_left h7 hM0
  have h6 : (0 : ℝ) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by
    have h3 : (0 : ℝ) ≤ lg (n : ℝ) ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ 4 * lg (n : ℝ) ^ 3 := by linarith only [h3]
    exact mul_nonneg hM0 h4
  have hE3 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) * lg (n : ℝ) ^ 3 :=
    mul_nonneg hE0 (by linarith only [hT1])
  have hM3 : (0 : ℝ) ≤ max KCR 0 * lg (n : ℝ) ^ 3 :=
    mul_nonneg hM0 (by linarith only [hT1])
  have hkey : 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3
      = 8 * ((hintLenE KCR : ℝ) * lg (n : ℝ) ^ 3) + 16 * lg (n : ℝ) ^ 3
        + 8 * (max KCR 0 * lg (n : ℝ) ^ 3) + 8 * lg (n : ℝ) ^ 3 := by ring
  have hstep1 : ((decKb KCR n : ℕ) : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4
      + max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by linarith only [hkb, h5]
  have hstep2 : ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4
        + max KCR 0 * (4 * lg (n : ℝ) ^ 3)
      ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3 := by
    have hL : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := hT1
    have hL0 : (0 : ℝ) ≤ lg (n : ℝ) ^ 3 := by linarith only [hL]
    have h4 : (4 : ℝ) ≤ 4 * lg (n : ℝ) ^ 3 := by linarith only [hL]
    have hexp : ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4
          + max KCR 0 * (4 * lg (n : ℝ) ^ 3)
        ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4 * lg (n : ℝ) ^ 3
          + max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by linarith only [h4]
    have hfac : ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4 * lg (n : ℝ) ^ 3
          + max KCR 0 * (4 * lg (n : ℝ) ^ 3)
        = ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 5) * lg (n : ℝ) ^ 3 := by ring
    rw [hfac] at hexp
    have hcoef : ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 5)
        ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) := by linarith only [hE0, hM0]
    calc ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 4
          + max KCR 0 * (4 * lg (n : ℝ) ^ 3)
        ≤ ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 5) * lg (n : ℝ) ^ 3 := hexp
      _ ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hcoef hL0
  linarith only [hstep1, hstep2]
theorem nodeCount_le_at {KCR : ℝ} {n lam N X Y : ℕ}
    (hargs : (hintP KCR n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (htree : (hintP KCR n lam).tree fuel N X Y = some T) :
    (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27 := by
  obtain ⟨f₀, T₀, hT₀, -, -, -, hnc₀⟩ := lemma_5_10_at (KCR := KCR) n lam N X Y hargs
  have hmax : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T :=
    tree_mono (hintP KCR n lam) fuel N X Y htree (max fuel f₀) (le_max_left _ _)
  have hmax0 : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T₀ :=
    tree_mono (hintP KCR n lam) f₀ N X Y hT₀ (max fuel f₀) (le_max_right _ _)
  have hTT : T = T₀ := Option.some.inj (by rw [← hmax, ← hmax0])
  rw [hTT]
  exact hnc₀
def decRecOff : ℕ := 64
theorem one_le_hintColK (KCR : ℝ) : (1 : ℝ) ≤ hintColK KCR := by
  have h1 : (100 : ℝ) ≤ (hintLenA KCR : ℝ) := by
    have h : 100 ≤ hintLenA KCR := le_max_right _ _
    exact_mod_cast h
  have h2 := hintLenA_le_hintColK KCR
  linarith only [h1, h2]
theorem one_le_ceil_hintColK (KCR : ℝ) : 1 ≤ ⌈hintColK KCR⌉₊ := by
  have h : (1 : ℝ) ≤ hintColK KCR := one_le_hintColK KCR
  have h2 : (1 : ℝ) ≤ (⌈hintColK KCR⌉₊ : ℝ) := le_trans h (Nat.le_ceil _)
  exact_mod_cast h2
theorem sixteen_mul_add_le_pow {n e x : ℕ} (hb : 4 ≤ n + 2) (hx : x ≤ (n + 2) ^ e) :
    16 * x + 82 ≤ (n + 2) ^ (e + 6) := by
  have h16 : 16 ≤ (n + 2) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hb 4)
  have h82 : 82 ≤ (n + 2) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hb 4)
  have h1 : 16 * x ≤ (n + 2) ^ 4 * (n + 2) ^ e := Nat.mul_le_mul h16 hx
  have h2 : (n + 2) ^ 4 * (n + 2) ^ e = (n + 2) ^ (e + 4) := by
    rw [← Nat.pow_add, Nat.add_comm 4 e]
  have h1' : 16 * x ≤ (n + 2) ^ (e + 4) := by rw [h2] at h1; exact h1
  have h82' : 82 ≤ (n + 2) ^ (e + 4) :=
    le_trans h82 (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : 16 * x + 82 ≤ (n + 2) ^ (e + 4) + (n + 2) ^ (e + 4) := Nat.add_le_add h1' h82'
  have h4 : (n + 2) ^ (e + 4) + (n + 2) ^ (e + 4) = 2 * (n + 2) ^ (e + 4) := by ring
  have h5 : 2 * (n + 2) ^ (e + 4) ≤ (n + 2) * (n + 2) ^ (e + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  have h6 : (n + 2) * (n + 2) ^ (e + 4) = (n + 2) ^ (e + 5) := by
    rw [Nat.mul_comm, ← pow_succ]
  have h7 : (n + 2) ^ (e + 5) ≤ (n + 2) ^ (e + 6) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc 16 * x + 82 ≤ (n + 2) ^ (e + 4) + (n + 2) ^ (e + 4) := h3
    _ = 2 * (n + 2) ^ (e + 4) := h4
    _ ≤ (n + 2) * (n + 2) ^ (e + 4) := h5
    _ = (n + 2) ^ (e + 5) := h6
    _ ≤ (n + 2) ^ (e + 6) := h7
theorem pow_lt_two_pow_hintW {K : ℝ} {n e : ℕ} (hb : 1 < n + 2)
    (he : e + 1 ≤ 1024 * (⌈K⌉₊ + 2)) :
    (n + 2) ^ e < 2 ^ hintW K n := by
  have h1 : (n + 2) ^ e < (n + 2) ^ (e + 1) := Nat.pow_lt_pow_succ hb
  exact lt_of_lt_of_le h1 (pow_le_two_pow_hintW K n (e + 1) he)
theorem lt_two_pow_hintW_of_le {K : ℝ} {n e x : ℕ} (hb : 1 < n + 2)
    (he : e + 1 ≤ 1024 * (⌈K⌉₊ + 2)) (hx : x ≤ (n + 2) ^ e) :
    x < 2 ^ hintW K n :=
  lt_of_le_of_lt hx (pow_lt_two_pow_hintW hb he)
theorem budget51a (c : ℕ) : 3 * c + 67 + 1 ≤ 1024 * (c + 2) := by omega
theorem budget51b (c : ℕ) : 3 * c + 67 + 6 + 1 ≤ 1024 * (c + 2) := by omega
theorem expShift51b (c : ℕ) : (3 * c + 6) + 61 = 3 * c + 67 := by omega
theorem decKb_mul_nodeCount_le_pow {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) {N : ℕ} {T : Node}
    (hNn : N ≤ n)
    (hnc : (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) :
    decKb KCR n * N * T.nodeCount ≤ (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) := by
  have hb4 : 4 ≤ n + 2 := by omega
  have hc0 : (0 : ℝ) ≤ (⌈hintColK KCR⌉₊ : ℝ) := by positivity
  have hc1' : (1 : ℝ) ≤ (⌈hintColK KCR⌉₊ : ℝ) := by
    exact_mod_cast (one_le_ceil_hintColK KCR)
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hL0 : (0 : ℝ) ≤ lg (n : ℝ) := by linarith only [hL1]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hnc0 : (0 : ℝ) ≤ (T.nodeCount : ℝ) := by positivity
  have hE : (hintLenE KCR : ℝ) ≤ (⌈hintColK KCR⌉₊ : ℝ) :=
    le_trans (hintLenE_le_hintColK KCR) (Nat.le_ceil _)
  have hM : max KCR 0 ≤ (⌈hintColK KCR⌉₊ : ℝ) :=
    le_trans (maxKCR_le_hintColK KCR) (Nat.le_ceil _)
  have hK10 : hintLenK₁₀ ≤ (⌈hintColK KCR⌉₊ : ℝ) :=
    le_trans (hintLenK₁₀_le_hintColK KCR) (Nat.le_ceil _)
  have hA : (hintLenA KCR : ℝ) ≤ (⌈hintColK KCR⌉₊ : ℝ) :=
    le_trans (hintLenA_le_hintColK KCR) (Nat.le_ceil _)
  have hkb := decKb_le_lg_pow (KCR := KCR) hn
  have hb0 : (0 : ℝ) ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3 := by
    have h1 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1) := by positivity
    have h2 : (0 : ℝ) ≤ lg (n : ℝ) ^ 3 := by positivity
    have h3 : (0 : ℝ) ≤ 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) :=
      mul_nonneg (by norm_num) h1
    exact mul_nonneg h3 h2
  have stepA : ((decKb KCR n : ℕ) : ℝ) * (N : ℝ) * (T.nodeCount : ℝ)
      ≤ (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3)
        * ((N : ℝ) * (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27)) := by
    have h1 : ((decKb KCR n : ℕ) : ℝ) * (N : ℝ)
        ≤ (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hkb hN0
    have h2 : (N : ℝ) * (T.nodeCount : ℝ)
        ≤ (N : ℝ) * (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) :=
      mul_le_mul_of_nonneg_left hnc hN0
    calc ((decKb KCR n : ℕ) : ℝ) * (N : ℝ) * (T.nodeCount : ℝ)
        = (((decKb KCR n : ℕ) : ℝ) * (N : ℝ)) * (T.nodeCount : ℝ) := by ring
      _ ≤ ((8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3) * (N : ℝ))
            * (T.nodeCount : ℝ) := mul_le_mul_of_nonneg_right h1 hnc0
      _ = (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3)
            * ((N : ℝ) * (T.nodeCount : ℝ)) := by ring
      _ ≤ (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3)
            * ((N : ℝ) * (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27)) :=
          mul_le_mul_of_nonneg_left h2 hb0
  have hfive : (hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1) ≤ 5 * (⌈hintColK KCR⌉₊ : ℝ) := by
    linarith only [hE, hM, hc1']
  have hcoef0 : (0 : ℝ) ≤ 8 * (5 * (⌈hintColK KCR⌉₊ : ℝ)) := by positivity
  have hKA : hintLenK₁₀ * (hintLenA KCR : ℝ)
      ≤ (⌈hintColK KCR⌉₊ : ℝ) * (⌈hintColK KCR⌉₊ : ℝ) :=
    mul_le_mul hK10 hA (by positivity) hc0
  have hcoef : 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1))
        * (hintLenK₁₀ * (hintLenA KCR : ℝ))
      ≤ 40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3) := by
    have h1 : 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1))
        ≤ 8 * (5 * (⌈hintColK KCR⌉₊ : ℝ)) := by linarith only [hfive]
    have h3 : (0 : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) :=
      mul_nonneg (le_of_lt hintLenK₁₀_pos) (by positivity)
    have h5 := mul_le_mul h1 hKA h3 hcoef0
    calc 8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * (hintLenK₁₀ * (hintLenA KCR : ℝ))
        ≤ (8 * (5 * (⌈hintColK KCR⌉₊ : ℝ)))
            * ((⌈hintColK KCR⌉₊ : ℝ) * (⌈hintColK KCR⌉₊ : ℝ)) := h5
      _ = 40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3) := by ring
  have hpow : lg (n : ℝ) ^ 3 * lg (n : ℝ) ^ 27 = lg (n : ℝ) ^ 30 := by rw [← pow_add]
  have hL30 : (0 : ℝ) ≤ lg (n : ℝ) ^ 30 := pow_nonneg hL0 30
  have stepB : (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3)
        * ((N : ℝ) * (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27))
      ≤ (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * (N : ℝ) * lg (n : ℝ) ^ 30 := by
    have h6 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hN0 hL30)
    calc (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1)) * lg (n : ℝ) ^ 3)
          * ((N : ℝ) * (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27))
        = (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1))
            * (hintLenK₁₀ * (hintLenA KCR : ℝ)))
            * ((N : ℝ) * (lg (n : ℝ) ^ 3 * lg (n : ℝ) ^ 27)) := by ring
      _ = (8 * ((hintLenE KCR : ℝ) + 2 + (max KCR 0 + 1))
            * (hintLenK₁₀ * (hintLenA KCR : ℝ)))
            * ((N : ℝ) * lg (n : ℝ) ^ 30) := by rw [hpow]
      _ ≤ (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * ((N : ℝ) * lg (n : ℝ) ^ 30) := h6
      _ = (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * (N : ℝ) * lg (n : ℝ) ^ 30 := by ring
  have hLsq : lg (n : ℝ) ≤ (((n + 2) ^ 2 : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : lg (n : ℝ) ≤ 2 * (n : ℝ) := lg_le_two_mul _ hn1
    have h2 : (2 : ℝ) * (n : ℝ) ≤ (((n + 2) ^ 2 : ℕ) : ℝ) := by
      have h3 : (((n + 2) ^ 2 : ℕ) : ℝ) = ((n : ℝ) + 2) ^ 2 := by push_cast; ring
      rw [h3]
      nlinarith only [hn2, sq_nonneg ((n : ℝ))]
    linarith only [h1, h2]
  have hL30le : lg (n : ℝ) ^ 30 ≤ (((n + 2) ^ 60 : ℕ) : ℝ) := by
    have h1 : lg (n : ℝ) ^ 30 ≤ ((((n + 2) ^ 2 : ℕ) : ℝ)) ^ 30 := pow_le_pow_left₀ hL0 hLsq 30
    have h2 : ((((n + 2) ^ 2 : ℕ) : ℝ)) ^ 30 = (((n + 2) ^ 60 : ℕ) : ℝ) := by push_cast; ring
    rw [h2] at h1
    exact h1
  have hNL : (N : ℝ) * lg (n : ℝ) ^ 30 ≤ (((n + 2) ^ 61 : ℕ) : ℝ) := by
    have hNle : (N : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      have h : N ≤ n + 2 := by omega
      exact_mod_cast h
    have h1 : (N : ℝ) * lg (n : ℝ) ^ 30
        ≤ ((n + 2 : ℕ) : ℝ) * (((n + 2) ^ 60 : ℕ) : ℝ) :=
      mul_le_mul hNle hL30le hL30 (by positivity)
    have h2 : ((n + 2 : ℕ) : ℝ) * (((n + 2) ^ 60 : ℕ) : ℝ) = (((n + 2) ^ 61 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hc3nat : 40 * ⌈hintColK KCR⌉₊ ^ 3 ≤ (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) := by
    have h40 : 40 ≤ (n + 2) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hb4 6)
    have hcp : ⌈hintColK KCR⌉₊ ≤ (n + 2) ^ ⌈hintColK KCR⌉₊ :=
      le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) _)
    have hc3 : ⌈hintColK KCR⌉₊ ^ 3 ≤ ((n + 2) ^ ⌈hintColK KCR⌉₊) ^ 3 :=
      Nat.pow_le_pow_left hcp 3
    have hc3' : ((n + 2) ^ ⌈hintColK KCR⌉₊) ^ 3 = (n + 2) ^ (3 * ⌈hintColK KCR⌉₊) := by
      rw [← Nat.pow_mul, Nat.mul_comm ⌈hintColK KCR⌉₊ 3]
    have h1 : 40 * ⌈hintColK KCR⌉₊ ^ 3
        ≤ (n + 2) ^ 6 * (n + 2) ^ (3 * ⌈hintColK KCR⌉₊) :=
      Nat.mul_le_mul h40 (le_trans hc3 (le_of_eq hc3'))
    have h2 : (n + 2) ^ 6 * (n + 2) ^ (3 * ⌈hintColK KCR⌉₊)
        = (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) := by
      rw [← Nat.pow_add, Nat.add_comm 6 (3 * ⌈hintColK KCR⌉₊)]
    rw [h2] at h1
    exact h1
  have hc3real : 40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)
      ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) := by
    have h : ((40 * ⌈hintColK KCR⌉₊ ^ 3 : ℕ) : ℝ)
        ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) := by
      exact_mod_cast hc3nat
    calc 40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3) = ((40 * ⌈hintColK KCR⌉₊ ^ 3 : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) := h
  have stepD : (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * (N : ℝ) * lg (n : ℝ) ^ 30
      ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) : ℕ) : ℝ) := by
    have h1 : (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * ((N : ℝ) * lg (n : ℝ) ^ 30)
        ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) * (((n + 2) ^ 61 : ℕ) : ℝ) :=
      mul_le_mul hc3real hNL (mul_nonneg hN0 hL30) (by positivity)
    have h2 : (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) * (((n + 2) ^ 61 : ℕ) : ℝ)
        = (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← Nat.pow_add, expShift51b ⌈hintColK KCR⌉₊]
    calc (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * (N : ℝ) * lg (n : ℝ) ^ 30
        = (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * ((N : ℝ) * lg (n : ℝ) ^ 30) := by ring
      _ ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 6) : ℕ) : ℝ) * (((n + 2) ^ 61 : ℕ) : ℝ) := h1
      _ = (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) : ℕ) : ℝ) := h2
  have stepD' : (40 * ((⌈hintColK KCR⌉₊ : ℝ) ^ 3)) * (N : ℝ) * lg (n : ℝ) ^ 30
      ≤ ((n : ℝ) + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) := by
    refine le_trans stepD (le_of_eq ?_)
    push_cast
    ring
  have hR : ((decKb KCR n : ℕ) : ℝ) * (N : ℝ) * (T.nodeCount : ℝ)
      ≤ ((n : ℝ) + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) :=
    le_trans stepA (le_trans stepB stepD')
  have hgoal : ((decKb KCR n * N * T.nodeCount : ℕ) : ℝ)
      ≤ (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) : ℕ) : ℝ) := by
    have h1 : (((n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) : ℕ) : ℝ)
        = ((n : ℝ) + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) := by push_cast; ring
    rw [h1]
    push_cast
    exact hR
  exact_mod_cast hgoal
def DecWordFits (CR : CRFamily) (KCR : ℝ) (n : ℕ) (T : Node) : Prop :=
  synLen CR T < 2 ^ hintW (hintColK KCR) n ∧
    16 * decCnt CR (colBc KCR n) (colBℓ KCR n) T + decRecOff + 18
      < 2 ^ hintW (hintColK KCR) n
theorem decWordFits_at {KCR : ℝ} {n lam N X Y : ℕ} {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hargs : (hintP KCR n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (htree : (hintP KCR n lam).tree fuel N X Y = some T) :
    DecWordFits CR KCR n T := by
  have hargs' := hargs
  obtain ⟨hn, hlam, hN1, hNn, hXN, hYN⟩ := hargs'
  have hn2 : 2 ≤ n := hn
  have hNn2 : N ≤ n := hNn
  have htc := tree_cost (KCR := KCR) (P := hintP KCR n lam) rfl rfl hn hrows
    fuel N X Y T htree hN1 hNn hXN hYN
  have htc' : synLen CR T + T.nodeCount ≤ decKb KCR n * N * T.nodeCount :=
    le_trans (Nat.le_add_right (synLen CR T + T.nodeCount) _) htc
  have hsyn : synLen CR T ≤ decKb KCR n * N * T.nodeCount :=
    le_trans (Nat.le_add_right (synLen CR T) T.nodeCount) htc'
  have hcnt : decCnt CR (colBc KCR n) (colBℓ KCR n) T ≤ decKb KCR n * N * T.nodeCount :=
    le_trans (decCnt_le_synLen CR (colBc KCR n) (colBℓ KCR n) T) htc'
  have hnc := nodeCount_le_at (KCR := KCR) hargs fuel T htree
  have hbig := decKb_mul_nodeCount_le_pow (KCR := KCR) hn2 hNn2 hnc
  have hsyn2 : synLen CR T ≤ (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) := le_trans hsyn hbig
  have hcnt2 : decCnt CR (colBc KCR n) (colBℓ KCR n) T
      ≤ (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67) := le_trans hcnt hbig
  have hsynLt : synLen CR T < 2 ^ hintW (hintColK KCR) n :=
    lt_two_pow_hintW_of_le (K := hintColK KCR) (n := n) (e := 3 * ⌈hintColK KCR⌉₊ + 67)
      (by omega : 1 < n + 2) (budget51a ⌈hintColK KCR⌉₊) hsyn2
  have hcntLt : 16 * decCnt CR (colBc KCR n) (colBℓ KCR n) T + decRecOff + 18
      < 2 ^ hintW (hintColK KCR) n := by
    have h2 : 16 * decCnt CR (colBc KCR n) (colBℓ KCR n) T + decRecOff + 18
        ≤ (n + 2) ^ (3 * ⌈hintColK KCR⌉₊ + 67 + 6) := by
      have h := sixteen_mul_add_le_pow (n := n) (e := 3 * ⌈hintColK KCR⌉₊ + 67)
        (x := decCnt CR (colBc KCR n) (colBℓ KCR n) T) (by omega) hcnt2
      have h82 : 16 * decCnt CR (colBc KCR n) (colBℓ KCR n) T + decRecOff + 18
          = 16 * decCnt CR (colBc KCR n) (colBℓ KCR n) T + 82 := by
        rw [show decRecOff = 64 from rfl]
      rw [h82]
      exact h
    exact lt_two_pow_hintW_of_le (K := hintColK KCR) (n := n)
      (e := 3 * ⌈hintColK KCR⌉₊ + 67 + 6) (by omega : 1 < n + 2)
      (budget51b ⌈hintColK KCR⌉₊) h2
  unfold DecWordFits
  exact ⟨hsynLt, hcntLt⟩
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
theorem up_hintW_ceil (K : ℝ) (n : ℕ) : ⌈K⌉₊ ≤ hintW K n := by
  calc
    ⌈K⌉₊ ≤ 1024 * (⌈K⌉₊ + 2) := by omega
    _ ≤ 1024 * (⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (1024 * (⌈K⌉₊ + 2))
        (Nat.succ_le_succ (Nat.zero_le (Nat.clog 2 (n + 2))))
theorem up_hintW_clog (K : ℝ) (n : ℕ) : Nat.clog 2 (n + 2) ≤ hintW K n := by
  calc
    Nat.clog 2 (n + 2) ≤ Nat.clog 2 (n + 2) + 1 := by omega
    _ ≤ 1024 * (⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (Nat.clog 2 (n + 2) + 1)
        (by omega : 1 ≤ 1024 * (⌈K⌉₊ + 2))
theorem up_hintW_universe (K : ℝ) (n : ℕ) : n + 2 ≤ 2 ^ hintW K n :=
  (Nat.le_pow_clog (by norm_num) (n + 2)).trans
    (Nat.pow_le_pow_right (by norm_num) (up_hintW_clog K n))
theorem up_colBc_le_word_cube (KCR K : ℝ) (n : ℕ) (hK : max KCR 0 ≤ K) :
    colBc KCR n ≤ 4 * (2 ^ hintW K n) ^ 3 := by
  let R := 2 ^ hintW K n
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hKceil : K ≤ (⌈K⌉₊ : ℕ) := Nat.le_ceil K
  have hKword : (⌈K⌉₊ : ℝ) ≤ (hintW K n : ℝ) := by exact_mod_cast up_hintW_ceil K n
  have hWR : (hintW K n : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := hintW K n)))
  have hKR : max KCR 0 ≤ (R : ℝ) := hK.trans (hKceil.trans (hKword.trans hWR))
  have hnR : (n : ℝ) + 2 ≤ (R : ℝ) := by exact_mod_cast up_hintW_universe K n
  have hlog : lg ((n : ℝ) + 2) ≤ 2 * (R : ℝ) :=
    (lg_le_two_mul _ (by have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)).trans (by linarith only [hnR])
  have hlog0 : 0 ≤ lg ((n : ℝ) + 2) := lg_nonneg_of_one_le (by have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  have hlog2 : lg ((n : ℝ) + 2) ^ 2 ≤ 4 * (R : ℝ) ^ 2 := by
    calc
      lg ((n : ℝ) + 2) ^ 2 = lg ((n : ℝ) + 2) * lg ((n : ℝ) + 2) := by ring
      _ ≤ (2 * (R : ℝ)) * (2 * (R : ℝ)) := mul_le_mul hlog hlog hlog0 (by positivity)
      _ = 4 * (R : ℝ) ^ 2 := by ring
  change ⌈max KCR 0 * lg ((n : ℝ) + 2) ^ 2⌉₊ ≤ 4 * R ^ 3
  apply Nat.ceil_le.mpr
  calc
    max KCR 0 * lg ((n : ℝ) + 2) ^ 2 ≤ (R : ℝ) * (4 * (R : ℝ) ^ 2) :=
      mul_le_mul hKR hlog2 (sq_nonneg _) hR
    _ = ((4 * R ^ 3 : ℕ) : ℝ) := by push_cast; ring
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
theorem up_hint_word_min (K : ℝ) (n : ℕ) : 8 ≤ hintW K n := by
  have h1 : 1 ≤ (⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1) := Nat.mul_pos (by omega) (by omega)
  have h2 : hintW K n = 1024 * ((⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1)) := by unfold hintW; ring
  rw [h2]
  omega
theorem upEll_of_shrink (KCR : ℝ) (n : ℕ) :
    ∀ T, NodeShrink KCR n T → UpEllOK (colBℓ KCR n) T := by
  intro T
  induction T with
  | store N => intro h; exact trivial
  | cr N t => intro h; exact trivial
  | direct sch t =>
      intro h
      have hReal : (sch.ℓ : ℝ) ≤ (colBℓ KCR n : ℝ) := h.2.2.trans (Nat.le_ceil _)
      exact_mod_cast hReal
  | recursive sch t Xs Ys child ih =>
      intro h
      refine ⟨?_, fun s => ih s (h.2.2.2.2 s)⟩
      have hReal : (sch.ℓ : ℝ) ≤ (colBℓ KCR n : ℝ) := h.2.2.1.trans (Nat.le_ceil _)
      exact_mod_cast hReal
theorem up_depth_at {KCR : ℝ} {n lam N X Y : ℕ}
    (hArgs : (hintP KCR n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (hTree : (hintP KCR n lam).tree fuel N X Y = some T) :
    (T.depth : ℝ) ≤ hintLenK₁₀ * (lg (lg n) + 1) := by
  obtain ⟨f₀, T₀, hT₀, hFuel, hDepth, hRec, hCount⟩ := lemma_5_10_at KCR n lam N X Y hArgs
  have hmax : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T :=
    tree_mono (hintP KCR n lam) fuel N X Y hTree (max fuel f₀) (le_max_left _ _)
  have hmax0 : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T₀ :=
    tree_mono (hintP KCR n lam) f₀ N X Y hT₀ (max fuel f₀) (le_max_right _ _)
  have hTT : T = T₀ := Option.some.inj (by rw [← hmax, ← hmax0])
  rw [hTT]
  exact hDepth
structure UpHintPrepared (CR : CRFamily) (KCR : ℝ) (n lam : ℕ) (T : Node) : Prop where
  word_min : 8 ≤ hintW (hintColK KCR) n
  fits : (hintSpec T).Fits (hintW (hintColK KCR) n)
  words : wordsOf (hintW (hintColK KCR) n) (synLen CR T) ≤ 2 ^ hintW (hintColK KCR) n
  static : UpTreeStatic CR (colBc KCR n) n T
  universe_fits : n ≤ 2 ^ hintW (hintColK KCR) n
  positive : 0 < T.N
  padding : colBc KCR n ≤ 4 * (2 ^ hintW (hintColK KCR) n) ^ 3
  ell_pos : 1 ≤ colBℓ KCR n
  ell : UpEllOK (colBℓ KCR n) T
  cost : ((125 * (T.nodeCount * (T.depth + colBℓ KCR n + colBc KCR n)) + 12 : ℕ) : ℝ) ≤
    hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu
theorem upHint_prepared {CR : CRFamily} {KCR : ℝ} {n lam N X Y : ℕ}
    (hRows : ∀ Nv t, t ≤ Nv → (CR.rows Nv t : ℝ) ≤ KCR * ((t : ℝ) * lg ((Nv : ℝ) + 2) ^ 2))
    (hCol : ∀ Nv t, t ≤ Nv → ∀ c, ((CR.col Nv t c).card : ℝ) ≤ KCR * lg ((Nv : ℝ) + 2) ^ 2)
    (hRange : ∀ Nv t, t ≤ Nv → ∀ c, c < Nv → CR.col Nv t c ⊆ Finset.range (CR.rows Nv t))
    (hArgs : (hintP KCR n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (hTree : (hintP KCR n lam).tree fuel N X Y = some T) :
    UpHintPrepared CR KCR n lam T := by
  have hShrink := tree_shrink (KCR := KCR) (P := hintP KCR n lam) rfl rfl hArgs.1
    fuel N X Y T hTree hArgs.2.2.1 hArgs.2.2.2.1 hArgs.2.2.2.2.1 hArgs.2.2.2.2.2
  have hEll := upEll_of_shrink KCR n T hShrink
  have hStatic : UpTreeStatic CR (colBc KCR n) n T := by
    apply upTreeStatic_tree CR (hintP KCR n lam) (colBc KCR n) ?_ fuel N X Y T hArgs hTree
    intro Nv t hNv ht c hc
    exact ⟨col_card_le_ceil (hCol Nv t ht c) hNv, hRange Nv t ht c hc⟩
  have hN : 0 < T.N := by
    rw [tree_N (hintP KCR n lam) fuel N X Y T hTree]
    exact hArgs.2.2.1
  have hDW := decWordFits_at hRows hArgs fuel T hTree
  have hDc : decCnt CR (colBc KCR n) (colBℓ KCR n) T < 2 ^ hintW (hintColK KCR) n := by
    have h := hDW.2
    omega
  have hNc : T.nodeCount ≤ 2 ^ hintW (hintColK KCR) n :=
    (up_nodeCount_le_counter CR (colBc KCR n) n (colBℓ KCR n) T hStatic hN).trans hDc.le
  have hFits := upSpecFits_actual_tree (hintP KCR n lam) (hintLenE KCR) (hintColK KCR)
    fuel N X Y T hArgs hTree hEll hNc (hintLenE_le_hintColK KCR)
  have hMin := up_hint_word_min (hintColK KCR) n
  have hWords : wordsOf (hintW (hintColK KCR) n) (synLen CR T) ≤ 2 ^ hintW (hintColK KCR) n :=
    (wordsOf_le_self (W := hintW (hintColK KCR) n) (M := synLen CR T) (by omega)).trans hDW.1.le
  refine ⟨hMin, hFits, hWords, hStatic, n_le_two_pow_hintW _ _, hN,
    up_colBc_le_word_cube KCR (hintColK KCR) n (maxKCR_le_hintColK KCR),
    colBℓ_pos hArgs.1, hEll, ?_⟩
  exact upSteps_leFix hArgs.1 (nodeCount_le_at hArgs fuel T hTree) (up_depth_at hArgs fuel T hTree)
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main.HintCleanParams
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main.HintCleanParams
end
set_option autoImplicit false



#print axioms LinearSetReconciliation327.Main.HintCleanParams.upHint_prepared


