-- Prove2me | Definitions.Def_DetDLP_W3_FpCarryPins
-- name    : DetDLP_W3_FpCarryPins
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:59:46.191808+00:00
-- url     : https://prove2.me/theorems/23bae570-3214-416e-8f7b-fc5d5cb32532
-- title:
--   Unique Boolean carries for modular multiplication checks
-- statement:
--   For three words of $d$ bits and a fixed incoming carry, the column addition constraints with zero final carry certify exact natural-number addition. A correct sum has exactly one sequence of Boolean carries. Applied to the double-width product words, this replaces the addition equation in a strict-modulus multiplication certificate with local column checks.

import Definitions.Def_DetDLP_W3_FpHashPins

set_option autoImplicit false
namespace DetDLP

/-- At column zero the incoming carry is public. Subsequent columns read their predecessor. -/
def w3_addColumns : (d : ℕ) → ℕ → ℕ → ℕ → Bool → (Fin d → Bool) → Prop
  | 0, _, _, _, cin, _ => cin = false
  | d+1, a, b, z, cin, c =>
    a%2 + b%2 + cin.toNat = z%2 + 2*(c 0).toNat ∧
    w3_addColumns d (a/2) (b/2) (z/2) (c 0) (fun i => c i.succ)

theorem w3_addColumns_sound {d a b z : ℕ} {cin : Bool} {c : Fin d → Bool}
    (ha : a < 2^d) (hb : b < 2^d) (hz : z < 2^d) (h : w3_addColumns d a b z cin c) :
    a+b+cin.toNat = z := by
  induction d generalizing a b z cin with
  | zero => change cin = false at h; subst cin; simp only [pow_zero] at *; simp only [Bool.toNat_false]; omega
  | succ d ih =>
    obtain ⟨h1,h2⟩ := h
    rw [pow_succ] at ha hb hz
    have hh := ih (by omega : a/2 < 2^d) (by omega : b/2 < 2^d) (by omega : z/2 < 2^d) h2
    omega

theorem w3_addColumns_unique {d a b z : ℕ} {cin : Bool} (ha : a < 2^d) (hb : b < 2^d)
    (hz : z < 2^d) (he : a+b+cin.toNat = z) : ∃! c, w3_addColumns d a b z cin c := by
  induction d generalizing a b z cin with
  | zero =>
    refine ⟨Fin.elim0,?_,fun c _ => Subsingleton.elim ..⟩
    change cin = false; simp only [pow_zero] at *; cases cin <;> simp_all <;> omega
  | succ d ih =>
    let col := a%2 + b%2 + cin.toNat
    let out := decide (2 ≤ col)
    have hout : col = z%2 + 2*out.toNat := by
      have hc : cin.toNat ≤ 1 := by cases cin <;> decide
      by_cases hc' : 2 ≤ col
      · simp only [out, decide_eq_true hc', Bool.toNat_true]; dsimp [col] at hc' ⊢; omega
      · simp only [out, decide_eq_false hc', Bool.toNat_false]; dsimp [col] at hc' ⊢; omega
    rw [pow_succ] at ha hb hz
    have htail : a/2+b/2+out.toNat = z/2 := by dsimp [col] at hout; omega
    obtain ⟨t,ht,ut⟩ := ih (by omega : a/2 < 2^d) (by omega : b/2 < 2^d) (by omega : z/2 < 2^d) htail
    refine ⟨Fin.cons out t,⟨?_,?_⟩,?_⟩
    · simpa only [Fin.cons_zero] using hout
    · simpa only [Fin.cons_zero,Fin.cons_succ] using ht
    · intro s hs; obtain ⟨h0,hrest⟩ := hs
      have hbit : s 0 = out := by
        have hn : (s 0).toNat = out.toNat := by dsimp [col] at hout; omega
        cases h1 : s 0 <;> cases h2 : out <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
      rw [hbit] at hrest
      have hfun := ut _ hrest
      funext i; cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using hbit
      | succ i => simpa only [Fin.cons_succ] using congrFun hfun i

theorem w3_addColumns_modTwo {d p x y z : ℕ} (hd : 1 ≤ d) (hz : z < 2^(2*d))
    (r : Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd) :
    w3_modTwo hd p x y z r ↔ w3_mulPins hd x y r.2.1 ∧ w3_mulPins hd r.1.val p r.2.2 ∧
      ∃! c, w3_addColumns (2*d) r.2.2.1.val z r.2.1.1.val false c := by
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h2,w3_addColumns_unique r.2.2.1.isLt hz r.2.1.1.isLt (by simpa using h3)⟩
  · rintro ⟨h1,h2,c,hc,_⟩
    exact ⟨h1,h2,by simpa using w3_addColumns_sound r.2.2.1.isLt hz r.2.1.1.isLt hc⟩

end DetDLP


