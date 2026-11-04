-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
-- name    : Submission_ThreeSumApsp_Lang_Rules
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:25:58.36134+00:00
-- url     : https://prove2.me/theorems/8ae0338b-6a94-4f5a-86e5-5c6f55a82c80
-- title:
--   Rules
-- statement:
--   Definitions and structural lemmas for Rules, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Rules.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Theorems.Thm_Light_Ends_mono
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_skip
public import Theorems.Thm_Light_Ends_store
public import Theorems.Thm_Light_Ends_whileConst
public import Theorems.Thm_Light_Limits_Addr_abs_le
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
instance Cond.decidableHolds (σ : State) : (c : Cond) → Decidable (c.Holds σ)
  | .lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | .eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))
@[simp]
def Stmt.after : Stmt → State → State
  | .set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | .store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | .seq s t, σ => t.after (s.after σ)
  | .ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ
@[simp]
def Stmt.blockCost : Stmt → ℕ
  | .set _ e => e.cost + 1
  | .store a e => a.cost + e.cost + 1
  | .seq s t => s.blockCost + t.blockCost
  | .ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0
@[simp]
def Stmt.BlockSafe (lim : Limits) : Stmt → State → Prop
  | .skip, _ => True
  | .set _ e, σ => e.Safe lim σ
  | .store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | .seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | .ite c s t, σ => c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False
abbrev Stmt.Runs (lim : Limits) (s : Stmt) (σ : State) (R : State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R) (hR : ∀ σ', R σ' → R' σ') :
    s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩
theorem Stmt.Runs.seq {s t : Stmt} {σ : State} {R : State → Prop} (h : s.Runs lim σ fun σ' => t.Runs lim σ' R) :
    (_root_.Light.Stmt.seq s t).Runs lim σ R :=
  ⟨⟨h.1, h.2.1⟩, h.2.2⟩
abbrev Stmt.for (i : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  _root_.Light.Stmt.seq (.set i (k 0))
    (.while (_root_.Light.Cond.lt (v i) hi)
      (_root_.Light.Stmt.seq body (.set i ((_root_.Light.Expr.op _root_.Light.Op.add) (v i) (k 1)))))
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop} (I : ℕ → State → Prop)
    (n b : ℕ) (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round :
      ∀ (j : ℕ) (σ : State),
        j < n →
          σ.loc i = j →
            I j σ →
              Ends lim P d body σ b fun σ' =>
                σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))) :
    Ends lim P d (Stmt.for i hi body) σ T Q :=
  by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3) (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine
    Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩ ?_ ?_
      (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : ((_root_.Light.Expr.op _root_.Light.Op.add) (v i) (k 1)).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |((_root_.Light.Expr.op _root_.Light.Op.add) (v i) (k 1)).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _
end Light


