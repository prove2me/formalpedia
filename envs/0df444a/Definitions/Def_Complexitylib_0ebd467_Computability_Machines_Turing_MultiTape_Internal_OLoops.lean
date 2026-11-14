-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:45:53.379958+00:00
-- url     : https://prove2.me/theorems/4750b8fc-bd13-463d-8728-a4ca8362fbc6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops — Direct charged folds with full reachable-prefix bounds
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The original independent time/workspace formulas are retained. Each plain input certificate
--   supplies its own normalized machine within the internal construction; no higher tidy O calculus
--   is imported or used. The state invariant applies only to actual reachable prefixes.
--
--   ### Main results
--
--   * `ComputableInO.foldl`: independent callback time/workspace bounds and a full prefix invariant.
--   * `ComputableInO.foldlWith`: the same with an encoded runtime parameter retained in state.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/OLoops.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCombinators
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct charged folds with full reachable-prefix bounds

The original independent time/workspace formulas are retained. Each plain input certificate
supplies its own normalized machine within the internal construction; no higher tidy O calculus
is imported or used. The state invariant applies only to actual reachable prefixes.

## Main results

* `ComputableInO.foldl`: independent callback time/workspace bounds and a full prefix invariant.
* `ComputableInO.foldlWith`: the same with an encoded runtime parameter retained in state.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}

private lemma fold_time {cl ci cs Tl Ti R L n : ℕ} (hn : n ≤ L) :
    cl * (Tl + 1) + ci * (Ti + 1) + (n + 1) * (cs * (R + 1) + (2 * L + 1 + R) + 1) ≤
      (cl + ci + 2 * cs + 4) * (Tl + Ti + (n + 1) * (R + L) + 1) := by
  have ha : (n + 1) * R ≤ (n + 1) * (R + L) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hb : (n + 1) * L ≤ (n + 1) * (R + L) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hc : n + 1 ≤ (n + 1) * (R + L) + 1 := by nlinarith
  generalize (n + 1) * (R + L) = M at *
  have : (n + 1) * (cs * (R + 1) + (2 * L + 1 + R) + 1) ≤ 2 * cs * M + cs + 4 * M + 2 := by
    have := Nat.mul_le_mul_left cs ha
    have := Nat.mul_le_mul_left cs hc
    nlinarith
  nlinarith

/-- **Left folds within given bounds.** If every round is within the time `R x` and the space
`Q x`, and every state has length at most `B x`, a fold takes the time of the list and of the
initial state, plus `R x`, `B x` and the length of the encoded list for every round, and the space
of the list and of the initial state, plus `Q x`, `B x` and the length of the encoded list once. -/
theorem foldl [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β} {Tl Ti Sl Si R Q B : γ → ℕ}
    {Ts Ss : β × α → ℕ}
    (hlist : ComputableInO list encIn encL Tl Sl)
    (hinit : ComputableInO init encIn encB Ti Si)
    (hstep : ComputableInO (fun p : β × α => step p.1 p.2) (encPair encB encA) encB Ts Ss)
    (hround : ∀ x i (hi : i < (list x).length),
      Ts (((list x).take i).foldl step (init x), (list x)[i]) ≤ R x)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss (((list x).take i).foldl step (init x), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInO (fun x => (list x).foldl step (init x)) encIn encB
      (fun x => Tl x + Ti x + ((list x).length + 1) * (R x + B x + (encL (list x)).length))
      fun x => Sl x + Si x + Q x + B x + (encL (list x)).length := by
  obtain ⟨cl, ⟨kl, Ql, _, tml, hl⟩, -⟩ := Internal.NormalForm.inO hlist
  obtain ⟨ci, ⟨ki, Qi, _, tmi, hi⟩, -⟩ := Internal.NormalForm.inO hinit
  obtain ⟨cs, ⟨ks, Qs, _, tms, hs⟩, -⟩ := Internal.NormalForm.inO hstep
  obtain ⟨c, k, State, hfinite, tm, h⟩ := Internal.FoldCompiler.foldl
    (encA := encA) (encL := encL)
    (encBA := encPair encB encA) (encS := encPair encL encB)
    (encO := encOption (encPair encL encB))
    (fun x => (hl x).mono (t' := cl * (Tl x + 1) + ci * (Ti x + 1))
      (s' := cl * (Sl x + 1) + ci * (Si x + 1))
      (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    (fun x => (hi x).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)) hs
    (tMax := fun x => cs * (R x + B x + 1)) (sMax := fun x => cs * (Q x + 1))
    (lMax := fun x => 2 * (encL (list x)).length + 1 + B x)
    (fun x i hi => Nat.mul_le_mul_left cs (by have := hround x i hi; omega))
    (fun x i hi => Nat.mul_le_mul_left cs (Nat.add_le_add_right (hspace x i hi) 1))
    (fun x i hi => by
      have h₁ := hstate x i hi
      have h₂ := hS.length_drop_le (list x) i
      simp only [length_encPair]
      omega)
  set K := cl + ci + 2 * cs + 4
  refine of_bounds ⟨k, State, hfinite, tm, fun x => (h x).computesInTimeAndSpace⟩
    (c * K + 1) (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · have h₁ : ((list x).length + 1) * (cs * (R x + B x + 1) + (2 * (encL (list x)).length + 1 +
        B x) + 1) ≤ ((list x).length + 1) * (cs * (R x + B x + 1) +
          (2 * (encL (list x)).length + 1 + (R x + B x)) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    refine (Nat.mul_le_mul_left c ((Nat.add_le_add_left h₁ _).trans
      (fold_time (hS.length_le (list x))))).trans ?_
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · have : cl * (Sl x + 1) + ci * (Si x + 1) + cs * (Q x + 1) +
        (2 * (encL (list x)).length + 1 + B x) + 1 ≤
        K * (Sl x + Si x + Q x + B x + (encL (list x)).length + 1) := by
      simp only [K]
      nlinarith
    refine (Nat.mul_le_mul_left c this).trans ?_
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  · have := hstate x _ le_rfl
    rw [List.take_length] at this
    exact this.trans ((show B x ≤ Sl x + Si x + Q x + B x + (encL (list x)).length + 1 by
      omega).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))

/-- **Left folds with a parameter, within given bounds.** The step may depend on a parameter
`par x`, which is kept in the state. -/
theorem foldlWith [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    {Tp Tl Ti Sp Sl Si R Q B : γ → ℕ} {Ts Ss : (π × β) × α → ℕ}
    (hpar : ComputableInO par encIn encP Tp Sp)
    (hlist : ComputableInO list encIn encL Tl Sl)
    (hinit : ComputableInO init encIn encB Ti Si)
    (hstep : ComputableInO (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB Ts Ss)
    (hround : ∀ x i (hi : i < (list x).length),
      Ts ((par x, ((list x).take i).foldl (step (par x)) (init x)), (list x)[i]) ≤ R x)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss ((par x, ((list x).take i).foldl (step (par x)) (init x)), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableInO (fun x => (list x).foldl (step (par x)) (init x)) encIn encB
      (fun x => Tp x + Tl x + Ti x +
        ((list x).length + 1) * (R x + B x + (encP (par x)).length + (encL (list x)).length))
      fun x => Sp x + Sl x + Si x + Q x + B x + (encP (par x)).length + (encL (list x)).length := by
  -- fold over the state `(par x, acc)`, keeping the parameter unchanged
  have heq (l : List α) (s : π × β) :
      l.foldl (fun s a => (s.1, step s.1 s.2 a)) s = (s.1, l.foldl (step s.1) s.2) :=
    List.foldl_hom (fun acc => (s.1, acc)) (fun _ _ => rfl)
  have hkeep := (fst encP encB).comp_linear (fst (encPair encP encB) encA)
  have hfold := foldl (encB := encPair encP encB) hlist (hpar.prod hinit)
    (step := fun s a => (s.1, step s.1 s.2 a)) (hkeep.prod hstep)
    (R := fun x => 4 * (encP (par x)).length + 2 * B x + (encL (list x)).length + 3 + R x)
    (Q := fun x => 4 * (encP (par x)).length + 2 * B x + (encL (list x)).length + 3 + Q x)
    (B := fun x => 2 * (encP (par x)).length + 1 + B x)
    (fun x i hi => by
      have h₁ := hround x i hi
      have h₂ := hstate x i hi.le
      have h₃ := hS.length_elem_le (list x) _ (List.getElem_mem hi)
      rw [heq]
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have h₁ := hspace x i hi
      have h₂ := hstate x i hi.le
      have h₃ := hS.length_elem_le (list x) _ (List.getElem_mem hi)
      rw [heq]
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i hi => by
      have := hstate x i hi
      rw [heq]
      simp only [length_encPair]
      omega)
  refine (((snd encP encB).comp_linear hfold).mono 8 (fun x => ?_) fun x => ?_).of_enc_eq
    fun x => ?_
  · have h₁ := hS.length_le (list x)
    have h₂ : (list x).length ≤ (list x).length * (encL (list x)).length := by
      rcases Nat.eq_zero_or_pos (list x).length with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    ring_nf
    omega
  · omega
  · rw [Function.comp_apply, heq]

end Turing.MultiTapeTM.ComputableInO


