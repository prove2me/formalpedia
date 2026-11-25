-- Prove2me | Definitions.Def_DetDLP_W1_EuclidPoly
-- name    : DetDLP_W1_EuclidPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T21:38:46.102162+00:00
-- url     : https://prove2.me/theorems/741b30e8-a080-4160-8082-5cae105313b7
-- title:
--   Polynomial-time certificate for the Bezout transducer
-- statement:
--   This module certifies that the binary Euclidean transducer and its divisibility-guarded Bezout residue are polynomial-time functions of their natural-number inputs. It supplies the computational bound needed to compile the transducer into a deterministic multitape machine.

import Definitions.Def_DetDLP_W1_Euclid
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_div

set_option autoImplicit false
open Groundwork
namespace DetDLP_W1_Euclid

attribute [local fun_prop] Groundwork.PolyT.mul Groundwork.PolyT.mod Groundwork.PolyT.div
  Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.comp Groundwork.PolyT.prodMk
  Groundwork.PolyT.const Groundwork.PolyT.id' P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_some__e6a32bd6af45 P2M_Groundwork_PolyT_id__1c5d0f44cc8f

@[local fun_prop] theorem poly_step {α : Type} [Enc α] {n : α → ℕ} {s : α → State}
    (hn : PolyT n) (hs : PolyT s) : PolyT (fun x => step (n x) (s x)) := by
  unfold step
  fun_prop

def bounded (m : ℕ) (s : State) := s.1 ≤ m ∧ s.2.1 ≤ m ∧ s.2.2.1 ≤ m ∧ s.2.2.2 ≤ m

theorem step_bounded {m n : ℕ} (hn : n ≤ m) (s : State) (hs : bounded m s) : bounded m (step n s) := by
  by_cases hz : s.2.1 = 0
  · simpa [step,hz] using hs
  rcases hs with ⟨ha,hb,hc,he⟩
  simp only [step,hz,if_false,bounded]
  refine ⟨hb,(Nat.mod_le _ _).trans ha,he,?_⟩
  by_cases h0 : n = 0
  · subst n; simp; omega
  · exact (Nat.mod_lt _ (Nat.pos_of_ne_zero h0)).le.trans hn

theorem fold_bounded {m n : ℕ} (hn : n ≤ m) (l : List Bool) (s : State) (hs : bounded m s) :
    bounded m (l.foldl (fun s _ => step n (step n s)) s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons b l ih => exact ih _ (step_bounded hn _ (step_bounded hn _ hs))

theorem poly_run : PolyT (fun p : ℕ × ℕ => run p.1 p.2) := by
  apply PolyT.foldl (l := fun p : ℕ × ℕ => p.1.bits) (a := fun p => init p.1 p.2)
    (g := fun p s (_ : Bool) => step p.1 (step p.1 s))
  · fun_prop
  · unfold init; fun_prop
  · fun_prop
  · refine ⟨fun k => 4*k+30, ((PB.const 4).mul PB.id').add (PB.const 30), ?_⟩
    intro p k
    let m := max 1 (max p.1 p.2)
    have h1 : 1 ≤ m := le_max_left _ _
    have hn : p.1 ≤ m := (le_max_left _ _).trans (le_max_right _ _)
    have hu : p.2 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
    have hinit : bounded m (init p.1 p.2) := ⟨hn,hu,Nat.zero_le _,h1⟩
    obtain ⟨ha,hb,hc,he⟩ := fold_bounded hn (p.1.bits.take k) _ hinit
    let s := (p.1.bits.take k).foldl (fun s _ => step p.1 (step p.1 s)) (init p.1 p.2)
    change s.1 ≤ m at ha
    change s.2.1 ≤ m at hb
    change s.2.2.1 ≤ m at hc
    change s.2.2.2 ≤ m at he
    have hm : m.size ≤ p.1.size + p.2.size + 1 := by
      dsimp [m]; rcases le_total p.1 p.2 with h|h
      · rw [max_eq_right h]; rcases le_total 1 p.2 with h'|h' <;> simp [max_eq_right,max_eq_left,h'] <;> omega
      · rw [max_eq_left h]; rcases le_total 1 p.1 with h'|h' <;> simp [max_eq_right,max_eq_left,h'] <;> omega
    change len s ≤ 4 * len p + 30
    conv_lhs => rw [show s = (s.1,s.2.1,s.2.2.1,s.2.2.2) from rfl]
    conv_rhs => rw [show p = (p.1,p.2) from rfl]
    simp only [len_pair,len_nat]
    have ha' := Nat.size_le_size ha
    have hb' := Nat.size_le_size hb
    have hc' := Nat.size_le_size hc
    have he' := Nat.size_le_size he
    omega

@[local fun_prop] theorem poly_run' {α : Type} [Enc α] {n u : α → ℕ} (hn : PolyT n) (hu : PolyT u) :
    PolyT (fun x => run (n x) (u x)) :=
  PolyT.comp (f := fun p : ℕ × ℕ => run p.1 p.2) (g := fun x => (n x, u x))
    poly_run (PolyT.prodMk hn hu)

@[local fun_prop] theorem poly_answer {α : Type} [Enc α] {n u v : α → ℕ} (hn : PolyT n)
    (hu : PolyT u) (hv : PolyT v) : PolyT (fun x => answer (n x) (u x) (v x)) := by
  unfold answer
  fun_prop

end DetDLP_W1_Euclid


