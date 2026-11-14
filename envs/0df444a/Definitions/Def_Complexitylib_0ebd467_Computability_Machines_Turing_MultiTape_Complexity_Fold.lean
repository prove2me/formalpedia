-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Fold
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Fold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:34.93574+00:00
-- url     : https://prove2.me/theorems/91981a93-7b39-4431-a061-fe0491d570c6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold — Left folds with bounds of given degrees
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl` asks for bounds on the arguments of the
--   step function and on the intermediate states paired with the rest of the list. For list encodings
--   whose elements, suffixes and lengths are bounded by the encoded list (`SizedListEncoding`), and the
--   framed encodings of pairs and options, only a bound on the intermediate states is left.
--
--   A fold whose step also needs a fixed parameter, such as a key to look up, keeps the parameter in its
--   state (`Turing.MultiTapeTM.ComputableTidilyInDegree.foldlWith`).
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.SizedListEncoding`: list encodings that bound their elements, suffixes and
--     lengths.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.foldl'`: left folds, with the degree of a round
--     plus the degree of the number of rounds.
--   * `Turing.MultiTapeTM.ComputableTidilyInDegree.foldlWith`: the same, with a parameter.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Fold`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Fold.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: use the local `DegreeBounded.add_max` rule; the fold contracts are unchanged.
-- vendored: derive the encoded suffix bound from Mathlib's `List.Sublist.flatMap`.

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Left folds with bounds of given degrees

`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl` asks for bounds on the arguments of the
step function and on the intermediate states paired with the rest of the list. For list encodings
whose elements, suffixes and lengths are bounded by the encoded list (`SizedListEncoding`), and the
framed encodings of pairs and options, only a bound on the intermediate states is left.

A fold whose step also needs a fixed parameter, such as a key to look up, keeps the parameter in its
state (`Turing.MultiTapeTM.ComputableTidilyInDegree.foldlWith`).

## Main definitions

* `Turing.MultiTapeTM.SizedListEncoding`: list encodings that bound their elements, suffixes and
  lengths.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInDegree.foldl'`: left folds, with the degree of a round
  plus the degree of the number of rounds.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.foldlWith`: the same, with a parameter.
-/

namespace Turing.MultiTapeTM

/-- **Left folds with bounds of given degrees.** If the list has output degree `eL`, the states have
length of degree `b`, and a round has degree `dS`, a fold takes time of degree
`eL + max 1 dS * max b eL`: at most `O(n ^ eL)` rounds, on arguments of length `O(n ^ max b eL)`. -/
public theorem ComputableTidilyInDegree.foldl' {γ α β : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [hS : SizedListEncoding encA encL]
    {list : γ → List α} {init : γ → β} {step : β → α → β} {dL eL dI eI dS eS b : ℕ}
    (hlist : ComputableTidilyInDegree list encIn encL dL eL)
    (hinit : ComputableTidilyInDegree init encIn encB dI eI)
    (hstep : ComputableTidilyInDegree (fun p : β × α => step p.1 p.2) (encPair encB encA) encB
      dS eS)
    {B : γ → ℕ} (hB : DegreeBounded (fun x => (encIn x).length) B b)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInDegree (fun x => (list x).foldl step (init x)) encIn encB
      (max (max dL dI) (eL + max 1 dS * max b eL)) b := by
  obtain ⟨⟨t₁, s₁, ht₁, hs₁, h₁⟩, hl⟩ := hlist
  obtain ⟨⟨t₂, s₂, ht₂, hs₂, h₂⟩, -⟩ := hinit
  obtain ⟨⟨tS, sS, ⟨ct, htS⟩, ⟨cs, hsS⟩, hS'⟩, -⟩ := hstep
  set a := max b eL
  set D := max 1 dS * a
  -- the arguments of a round and the states with the rest of the list
  have haMax : DegreeBounded (fun x => (encIn x).length)
      (fun x => 2 * B x + 1 + (encL (list x)).length) a :=
    ((hB.smul 2).add_const 1).add_max hl
  have hlMax : DegreeBounded (fun x => (encIn x).length)
      (fun x => 2 * (encL (list x)).length + 1 + B x) a :=
    ((hl.mono_deg (le_max_right _ _)).smul 2 |>.add_const 1).add (hB.mono_deg (le_max_left _ _))
  have hround {c : ℕ} : DegreeBounded (fun x => (encIn x).length)
      (fun x => c * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS) D :=
    (DegreeBounded.comp (size' := id) (v := fun n => c * (n + 1) ^ dS) ⟨c, fun _ => le_rfl⟩
      haMax).mono_deg (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (le_max_right _ _))
  have hargs : ∀ x i (hi : i < (list x).length),
      (encPair encB encA (((list x).take i).foldl step (init x), (list x)[i])).length ≤
        2 * B x + 1 + (encL (list x)).length := fun x i hi => by
    have h₁ := hstates x i hi.le
    have h₂ := hS.length_elem_le (list x) _ (List.getElem_mem hi)
    simp only [length_encPair]
    omega
  have hrest : ∀ x, ∀ i ≤ (list x).length,
      (encPair encL encB ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤
        2 * (encL (list x)).length + 1 + B x := fun x i hi => by
    have h₁ := hstates x i hi
    have h₂ := hS.length_drop_le (list x) i
    simp only [length_encPair]
    omega
  have haD : a ≤ D := Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.foldl (encA := encA) (encL := encL)
    (encBA := encPair encB encA) (encS := encPair encL encB)
    (encO := encOption (encPair encL encB))
    (h₁.mono (t' := fun x => t₁ x + t₂ x) (s' := fun x => s₁ x + s₂ x)
      (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (h₂.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _)) hS'
    (tMax := fun x => ct * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS)
    (sMax := fun x => cs * (2 * B x + 1 + (encL (list x)).length + 1) ^ dS)
    (lMax := fun x => 2 * (encL (list x)).length + 1 + B x)
    (fun x i hi => (htS _).trans (Nat.mul_le_mul_left ct (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hargs x i hi) 1) dS)))
    (fun x i hi => (hsS _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hargs x i hi) 1) dS))) hrest
  · have hd₀ : max dL dI ≤ max (max dL dI) (eL + D) := le_max_left _ _
    have hd₁ : eL + D ≤ max (max dL dI) (eL + D) := le_max_right _ _
    have hlen : DegreeBounded (fun x => (encIn x).length) (fun x => (list x).length + 1) eL :=
      (hl.add_const 1).mono fun x => Nat.add_le_add_right (hS.length_le _) 1
    have ht := ht₁.add_max ht₂
    have hs := hs₁.add_max hs₂
    refine ⟨⟨_, _, ((ht.mono_deg hd₀).add ((hlen.mul ((hround.add (hlMax.mono_deg haD)).add_const
      1)).mono_deg hd₁)).smul c, ((((hs.mono_deg hd₀).add (hround.mono_deg (by omega))).add
        (hlMax.mono_deg (by omega))).add_const 1).smul c, h⟩, hB.mono fun x => ?_⟩
    simpa using hstates x _ le_rfl

/-- **Left folds with a parameter, with bounds of given degrees.** The step may depend on a
parameter `par x`, which is kept in the state. -/
public theorem ComputableTidilyInDegree.foldlWith {γ α β π : Type} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encP : π ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {par : γ → π} {list : γ → List α} {init : γ → β} {step : π → β → α → β}
    {dP eP dL eL dI eI dS eS b : ℕ}
    (hpar : ComputableTidilyInDegree par encIn encP dP eP)
    (hlist : ComputableTidilyInDegree list encIn encL dL eL)
    (hinit : ComputableTidilyInDegree init encIn encB dI eI)
    (hstep : ComputableTidilyInDegree (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB dS eS)
    {B : γ → ℕ} (hB : DegreeBounded (fun x => (encIn x).length) B b)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableTidilyInDegree (fun x => (list x).foldl (step (par x)) (init x)) encIn encB
      (max (max dL (max dP dI)) (eL + max 1 dS * max (max eP b) eL)) b := by
  -- fold over the state `(par x, acc)`, keeping the parameter unchanged
  -- vendored: use core's fold homomorphism law for the captured-parameter identity.
  have heq (l : List α) (s : π × β) :
      l.foldl (fun s a => (s.1, step s.1 s.2 a)) s = (s.1, l.foldl (step s.1) s.2) :=
    List.foldl_hom (fun acc => (s.1, acc)) (fun _ _ => rfl)
  have hfold := ComputableTidilyInDegree.foldl' (encB := encPair encP encB) hlist
    (hpar.prod hinit) (step := fun s a => (s.1, step s.1 s.2 a))
    (((ComputableTidilyInDegree.fst encP encB).comp
      (ComputableTidilyInDegree.fst (encPair encP encB) encA)).prod hstep)
    (B := fun x => 2 * (encP (par x)).length + 1 + B x)
    ((((hpar.2.mono_deg (le_max_left eP b)).smul 2).add_const 1).add
      (hB.mono_deg (le_max_right eP b)))
    (fun x i hi => by
      have := hstates x i hi
      rw [heq]
      simp only [length_encPair]
      omega)
  have h := (ComputableTidilyInDegree.snd encP encB).comp hfold
  have hf : (Prod.snd ∘ fun x => (list x).foldl (fun s a => (s.1, step s.1 s.2 a))
      (par x, init x)) = fun x => (list x).foldl (step (par x)) (init x) := by
    funext x
    simp [heq]
  rw [hf, show max 1 (max (max 1 (1 * 1)) dS) = max 1 dS by omega, Nat.mul_one] at h
  have hY : max eP b ≤ max (max dL (max dP dI)) (eL + max 1 dS * max (max eP b) eL) :=
    le_max_of_le_right (le_add_left ((le_max_left _ eL).trans
      (Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _)))))
  exact ⟨(h.mono (max_le le_rfl hY) le_rfl).1, hB.mono fun x => by simpa using hstates x _ le_rfl⟩
end Turing.MultiTapeTM


