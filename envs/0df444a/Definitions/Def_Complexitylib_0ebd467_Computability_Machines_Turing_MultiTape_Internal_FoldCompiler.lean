-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:42.479062+00:00
-- url     : https://prove2.me/theorems/15ca3ecc-fa4e-41a7-b382-74399abd9970
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.FoldCompiler — The existing fold compiler from supplied machine witnesses
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.FoldCompiler` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/FoldCompiler.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
-- vendored: existing fold assembly from crei/tidy-universal @7f7c0696.
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIterateWhile
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_LinearCodecPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ConditionalMachine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.FoldCompiler` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing fold compiler from supplied machine witnesses -/
namespace Turing.MultiTapeTM.Internal.FoldCompiler
universe u
variable {α β : Type u} (step : β → α → β) (a₀ : α) (b₀ : β)
/-- The argument of `step` in a round: the accumulator and the head of the rest of the list. -/
def arg (o : Option (List α × β)) : β × α :=
  ((o.getD ([], b₀)).2, (o.getD ([], b₀)).1.headD a₀)

/-- The state after a round: the tail of the rest of the list, and the new accumulator. -/
def next (o : Option (List α × β)) : List α × β :=
  ((o.getD ([], b₀)).1.tail, step (arg a₀ b₀ o).1 (arg a₀ b₀ o).2)

/-- One round of the fold on the state `some (l, b)`: `some (l.tail, step b a)` for the head `a` of
`l`, or `none` if `l` is empty. Defaults `a₀` and `b₀` make it total. -/
def foldStep (o : Option (List α × β)) : Option (List α × β) :=
  if (o.getD ([], b₀)).1.isEmpty then none else some (next step a₀ b₀ o)

@[simp]
lemma foldStep_none : foldStep step a₀ b₀ none = none := by
  simp [foldStep]

@[simp]
lemma foldStep_cons (a : α) (l : List α) (b : β) :
    foldStep step a₀ b₀ (some (a :: l, b)) = some (l, step b a) := by
  simp [foldStep, next, arg]

lemma iterate_foldStep (l : List α) (b : β) {n : ℕ} (hn : n ≤ l.length) :
    (foldStep step a₀ b₀)^[n] (some (l, b)) = some (l.drop n, (l.take n).foldl step b) := by
  induction n generalizing l b with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp at hn
    | cons a l =>
      rw [Function.iterate_succ_apply, foldStep_cons, ih l (step b a) (by simpa using hn)]
      simp

/-- The number of rounds of the fold on a state. -/
def rounds (o : Option (List α × β)) : ℕ := o.elim 0 fun p => p.1.length

lemma isLeast_rounds {enc₁ : List α × β ↪ List Bool} {enc : Option (List α × β) ↪ List Bool}
    (h : OptionEncoding enc₁ enc) (o : Option (List α × β)) :
    IsLeast {n | enc ((foldStep step a₀ b₀)^[n + 1] o) = []} (rounds o) := by
  have hnone (x : Option (List α × β)) : enc x = [] ↔ x = none := by
    rw [← h.none_eq, enc.injective.eq_iff]
  simp only [IsLeast, lowerBounds, Set.mem_ofPred_eq, hnone]
  rcases o with _ | ⟨l, b⟩
  · exact ⟨Function.iterate_fixed (foldStep_none step a₀ b₀) _, fun _ _ => Nat.zero_le _⟩
  · refine ⟨?_, fun n hn => ?_⟩
    · rw [rounds, Option.elim_some, Function.iterate_succ_apply',
        iterate_foldStep step a₀ b₀ l b le_rfl]
      simp [foldStep]
    · by_contra hlt
      rw [iterate_foldStep step a₀ b₀ l b (by simp only [rounds, Option.elim_some] at hlt; omega)]
        at hn
      exact Option.some_ne_none _ hn

/-- The cost of a round beyond reading the state: `u` of the argument of `step` plus the length of
the next state, unless the list is empty. -/
def roundCost (encS : List α × β ↪ List Bool) (u : β × α → ℕ) (o : Option (List α × β)) : ℕ :=
  if (o.getD ([], b₀)).1.isEmpty then 0 else u (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
  {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
  {encO : Option (List α × β) ↪ List Bool}

/-- Assemble one existing fold round, with independent callback clocks and workspace. -/
private theorem roundMachine [hLE : ListEncoding encA encL] [hBA : PairEncoding encB encA encBA]
    [hSE : PairEncoding encL encB encS] [hOE : OptionEncoding encS encO]
    {ts ss : β × α → ℕ} {ks : ℕ} {Qs : Type} [Finite Qs]
    {tms : MultiTapeTM ks Bool Qs}
    (hstep : ∀ p : β × α, tms.ComputesTidilyInTimeAndSpace (encBA p)
      (encB (step p.1 p.2)) (ts p) (ss p)) :
    ∃ c, ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ o,
      tm.ComputesTidilyInTimeAndSpace (encO o) (encO (foldStep step a₀ b₀ o))
        (c * ((encO o).length + roundCost step a₀ b₀ encS ts o + 1))
        (c * ((encO o).length + roundCost step a₀ b₀ encS ss o + 1)) := by
  have hlist := hSE.fst.comp (hOE.getD ([], b₀))
  have htail := hLE.tail.comp hlist
  have harg : ComputableInDegree (arg a₀ b₀) encO encBA 1 1 :=
    (hSE.snd.comp (hOE.getD ([], b₀))).pair ((hLE.headD a₀).comp hlist)
  obtain ⟨ca, ka, Qa, _, tma, ha⟩ := Internal.NormalForm.linear harg
  let A := 6 * ca + 6 * max ka ks + 30
  have happ : ComputableInTimeAndSpace
      (fun o => step (arg a₀ b₀ o).1 (arg a₀ b₀ o).2) encO encB
      (fun o => A * ((encO o).length + ts (arg a₀ b₀ o) + 1))
      (fun o => A * ((encO o).length + ss (arg a₀ b₀ o) + 1)) := by
    refine ⟨_, _, inferInstance, tms.comp tma true, fun o =>
      (((ha o).comp (hstep _) true).mono ?_ ?_).computesInTimeAndSpace⟩
    all_goals have hl := (ha o).length_output_le; dsimp [A]; ring_nf at hl ⊢; omega
  obtain ⟨ct, kt, Qt, _, tmt, ht⟩ := Internal.NormalForm.linear htail
  obtain ⟨cn, hn⟩ := hSE.pair_mono
    (show ComputableInTimeAndSpace _ encO encL _ _ from
      ⟨kt, Qt, inferInstance, tmt, fun o => (ht o).computesInTimeAndSpace⟩) happ
  let N := cn * (ct + A + 2)
  have hnext : ComputableInBigO (next step a₀ b₀) encO encS
      (fun o => (encO o).length + ts (arg a₀ b₀ o))
      (fun o => (encO o).length + ss (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length) := by
    refine ⟨N, hn.mono (fun o => ?_) (fun o => ?_)⟩
    all_goals dsimp [N, next]; ring_nf; omega
  obtain ⟨cN, kN, QN, _, tmN, hN⟩ := Internal.NormalForm.bigO hnext
  obtain ⟨co, ko, Qo, _, tmo, ho⟩ := Internal.NormalForm.linear hOE.some
  let C := cN + (co + 5) + 6 * max kN ko + 30
  have hsome : ∀ o, (tmo.comp tmN true).ComputesTidilyInTimeAndSpace
      (encO o) (encO (some (next step a₀ b₀ o)))
      (C * ((encO o).length + ts (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length + 1))
      (C * ((encO o).length + ss (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length + 1)) := by
    intro o
    apply ((hN o).comp (ho _) true).mono
    all_goals dsimp [C]; ring_nf; omega
  obtain ⟨ce, ke, Qe, _, tme, he⟩ := Internal.NormalForm.linear (hLE.isEmpty.comp hlist)
  obtain ⟨cz, kz, Qz, _, tmz, hz⟩ := Internal.NormalForm.linear
    (ComputableInDegree.const (encIn := encO) (encMid := encO)
      (none : Option (List α × β)))
  obtain ⟨ci, k, Q, hfinite, tm, htm⟩ := Internal.conditional
    (encIn := encO) (encOut := encO) (encC := encBool)
    (tmc := tme) (tmf := tmz) (tmg := tmo.comp tmN true)
    (tc := fun o => ce * ((encO o).length + 1))
    (sc := fun o => ce * ((encO o).length + 1))
    (tf := fun o => cz * ((encO o).length + 1))
    (sf := fun o => cz * ((encO o).length + 1))
    (tg := fun o => C * ((encO o).length + ts (arg a₀ b₀ o) +
      (encS (next step a₀ b₀ o)).length + 1))
    (sg := fun o => C * ((encO o).length + ss (arg a₀ b₀ o) +
      (encS (next step a₀ b₀ o)).length + 1))
    (c := fun o : Option (List α × β) => (o.getD ([], b₀)).1.isEmpty)
    (f := fun _ => (none : Option (List α × β)))
    (g := fun o => some (next step a₀ b₀ o)) he
    (fun o : {o : Option (List α × β) // (o.getD ([], b₀)).1.isEmpty = true} => hz o)
    (fun o : {o : Option (List α × β) // (o.getD ([], b₀)).1.isEmpty = false} => hsome o)
  refine ⟨ce + cz + C + ci + 1, k, Q, hfinite, tm, fun o => (htm o).mono ?_ ?_⟩
  all_goals
    dsimp only [foldStep, roundCost]
    split_ifs <;> ring_nf <;> omega

set_option maxHeartbeats 1000000 in
/-- Compile a fold from supplied machines, with the original independent prefix bounds. -/
public theorem foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [hLE : ListEncoding encA encL] [hBA : PairEncoding encB encA encBA]
    [hSE : PairEncoding encL encB encS] [hOE : OptionEncoding encS encO]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    {t s : γ → ℕ} {tStep sStep : β × α → ℕ} {tMax sMax lMax : γ → ℕ}
    {kl ki ks : ℕ} {Ql Qi Qs : Type} [Finite Ql] [Finite Qi] [Finite Qs]
    {tml : MultiTapeTM kl Bool Ql} {tmi : MultiTapeTM ki Bool Qi}
    {tms : MultiTapeTM ks Bool Qs}
    (hlist : ∀ x, tml.ComputesTidilyInTimeAndSpace (encIn x) (encL (list x)) (t x) (s x))
    (hinit : ∀ x, tmi.ComputesTidilyInTimeAndSpace (encIn x) (encB (init x)) (t x) (s x))
    (hstep : ∀ p : β × α, tms.ComputesTidilyInTimeAndSpace (encBA p)
      (encB (step p.1 p.2)) (tStep p) (sStep p))
    (htMax : ∀ x i (hi : i < (list x).length),
      tStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ tMax x)
    (hsMax : ∀ x i (hi : i < (list x).length),
      sStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ sMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ∃ c, ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ x,
      tm.ComputesTidilyInTimeAndSpace (encIn x) (encB ((list x).foldl step (init x)))
        (c * (t x + ((list x).length + 1) * (tMax x + lMax x + 1)))
        (c * (s x + sMax x + lMax x + 1)) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ⟨0, 0, _, inferInstance, tidyCopy Bool, isEmptyElim⟩
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · refine ⟨1, ki, Qi, inferInstance, tmi, fun x => ?_⟩
    simpa only [Subsingleton.elim (list x) [], List.foldl_nil, one_mul] using
      (hinit x).mono (by omega) (by omega)
  obtain ⟨cF, kF, QF, _, tmF, hF⟩ := roundMachine (encA := encA) (encL := encL) (encS := encS)
    (encO := encO) step a₀ (init x₀) hstep
  set g := foldStep step a₀ (init x₀)
  let tAlong (o : Option (List α × β)) := (Finset.Iic (rounds o)).sup
    fun n => roundCost step a₀ (init x₀) encS tStep (g^[n] o)
  let sAlong (o : Option (List α × β)) := (Finset.Iic (rounds o)).sup
    fun n => roundCost step a₀ (init x₀) encS sStep (g^[n] o)
  let lAlong (o : Option (List α × β)) := (Finset.Iic (rounds o)).sup
    fun n => (encO (g^[n] o)).length
  have htAlong (o) : tAlong o = _ := rfl
  have hsAlong (o) : sAlong o = _ := rfl
  have hlAlong (o) : lAlong o = _ := rfl
  let ci := 2 * (kF + 3) * (6 * kF + 54) + (4 * kF + 42)
  have hloop (o) : (tmF.iterateWhile true).ComputesTidilyInTimeAndSpace
      (encO o) (encO (g^[rounds o] o))
      ((cF + ci) * ((rounds o + 1) * (tAlong o + lAlong o + 1)))
      ((ci * (cF + 1) + 1) * (sAlong o + lAlong o + 1)) := by
    have hr := isLeast_rounds step a₀ (init x₀) hOE o
    have hround (n : ℕ) (hn : n ≤ rounds o) :
        tmF.ComputesTidilyInTimeAndSpace (encO (g^[n] o)) (encO (g^[n + 1] o))
          (cF * (tAlong o + lAlong o + 1)) (cF * (sAlong o + lAlong o + 1)) := by
      have ht := Finset.le_sup (f := fun n =>
        roundCost step a₀ (init x₀) encS tStep (g^[n] o)) (Finset.mem_Iic.mpr hn)
      have hs := Finset.le_sup (f := fun n =>
        roundCost step a₀ (init x₀) encS sStep (g^[n] o)) (Finset.mem_Iic.mpr hn)
      have hl := Finset.le_sup (f := fun n => (encO (g^[n] o)).length)
        (Finset.mem_Iic.mpr hn)
      change _ ≤ tAlong o at ht
      change _ ≤ sAlong o at hs
      change _ ≤ lAlong o at hl
      simpa only [Function.iterate_succ_apply'] using (hF (g^[n] o)).mono
        (t' := cF * (tAlong o + lAlong o + 1))
        (s' := cF * (sAlong o + lAlong o + 1))
        (Nat.mul_le_mul_left cF (by omega)) (Nat.mul_le_mul_left cF (by omega))
    have h := computesTidily_iterateWhile
      (w := fun n => encO (g^[n] o))
      (t := cF * (tAlong o + lAlong o + 1))
      (s := cF * (sAlong o + lAlong o + 1)) (l := lAlong o) hround
      (fun n hn => Finset.le_sup (f := fun n => (encO (g^[n] o)).length)
        (Finset.mem_Iic.mpr hn))
      (fun n hn he => Nat.not_le_of_lt hn (hr.2 (by simpa using he)))
      (by simpa using hr.1) true
    simpa only [Function.iterate_zero_apply] using h.mono
      (by dsimp [ci]; ring_nf; omega) (by dsimp [ci]; ring_nf; omega)
  obtain ⟨cp, hp⟩ := hSE.pair
    (show ComputableInTimeAndSpace list encIn encL t s from
      ⟨kl, Ql, inferInstance, tml, fun x => (hlist x).computesInTimeAndSpace⟩)
    (show ComputableInTimeAndSpace init encIn encB t s from
      ⟨ki, Qi, inferInstance, tmi, fun x => (hinit x).computesInTimeAndSpace⟩)
  have hpair : ComputableInBigO (fun x => (list x, init x)) encIn encS t
      (fun x => s x + lMax x) := by
    refine ⟨cp, hp.mono (fun _ => le_rfl) (fun x => ?_)⟩
    have hl := hlMax x 0 (Nat.zero_le _)
    simpa using Nat.mul_le_mul_left cp (Nat.add_le_add_right (Nat.add_le_add_left hl (s x)) 1)
  obtain ⟨cP, kP, QP, _, tmP, hP⟩ := Internal.NormalForm.bigO hpair
  obtain ⟨cs, kS, QS, _, tmS, hS⟩ := Internal.NormalForm.linear hOE.some
  let cStart := cP + cs + 6 * max kP kS + 30
  have hstart (x) : (tmS.comp tmP true).ComputesTidilyInTimeAndSpace
      (encIn x) (encO (some (list x, init x)))
      (cStart * (t x + lMax x + 1)) (cStart * (s x + lMax x + 1)) := by
    have hl : (encS (list x, init x)).length ≤ lMax x := by
      simpa using hlMax x 0 (Nat.zero_le _)
    apply ((hP x).comp (hS _) true).mono
    all_goals
      have hlc := Nat.mul_le_mul_left cs hl
      dsimp [cStart]
      ring_nf at hlc ⊢
      omega
  have hcs (p : List α × β) : (encO (some p)).length ≤ cs * ((encS p).length + 1) :=
    (hS p).length_output_le
  have hrounds (x : γ) : rounds (some (list x, init x)) = (list x).length := rfl
  have hstate (x : γ) {i : ℕ} (hi : i ≤ (list x).length) : g^[i] (some (list x, init x)) =
      some ((list x).drop i, ((list x).take i).foldl step (init x)) :=
    iterate_foldStep step a₀ (init x₀) _ _ hi
  have hstep_le (x : γ) {u : β × α → ℕ} {U : ℕ}
      (hu : ∀ i (hi : i < (list x).length),
        u (((list x).take i).foldl step (init x), (list x)[i]) ≤ U)
      {i : ℕ} (hi : i ≤ (list x).length) :
      roundCost step a₀ (init x₀) encS u (g^[i] (some (list x, init x))) ≤ U + lMax x := by
    rw [roundCost, hstate x hi, Option.getD_some]
    split_ifs with h
    · exact Nat.zero_le _
    · have hi' : i < (list x).length := by
        by_contra hc
        simp [List.drop_eq_nil_of_le (by omega : (list x).length ≤ i)] at h
      have hdrop := List.drop_eq_getElem_cons hi'
      refine Nat.add_le_add ?_ ?_
      · simp only [arg, Option.getD_some, hdrop, List.headD_cons]
        exact hu i hi'
      · have := hlMax x (i + 1) hi'
        simp only [next, arg, Option.getD_some, hdrop, List.tail_cons, List.headD_cons]
        rwa [List.take_succ_eq_append_getElem hi', List.foldl_append, List.foldl_cons,
          List.foldl_nil] at this
  have htx (x : γ) : tAlong (some (list x, init x)) ≤ tMax x + lMax x := by
    rw [htAlong]
    exact Finset.sup_le fun i hi => hstep_le x (htMax x) (by rwa [Finset.mem_Iic, hrounds] at hi)
  have hsx (x : γ) : sAlong (some (list x, init x)) ≤ sMax x + lMax x := by
    rw [hsAlong]
    exact Finset.sup_le fun i hi => hstep_le x (hsMax x) (by rwa [Finset.mem_Iic, hrounds] at hi)
  have hlen (x : γ) {i : ℕ} (hi : i ≤ (list x).length) :
      (encO (g^[i] (some (list x, init x)))).length ≤ cs * (lMax x + 1) := by
    rw [hstate x hi]
    exact (hcs _).trans (Nat.mul_le_mul_left cs (Nat.add_le_add_right (hlMax x i hi) 1))
  have hlx (x : γ) : lAlong (some (list x, init x)) ≤ cs * (lMax x + 1) := by
    rw [hlAlong]
    exact Finset.sup_le fun i hi => hlen x (by rwa [Finset.mem_Iic, hrounds] at hi)
  obtain ⟨cf, kf, Qf, _, tmf, hf⟩ := Internal.NormalForm.linear
    (hSE.snd.comp (hOE.getD ([], init x₀)))
  let A := (cF + ci) * (cs + 2)
  let D := (ci * (cF + 1) + 1) * (cs + 2)
  have hrun (x) : (tmF.iterateWhile true).ComputesTidilyInTimeAndSpace
      (encO (some (list x, init x))) (encO (some ([], (list x).foldl step (init x))))
      (A * (((list x).length + 1) * (tMax x + lMax x + 1)))
      (D * (sMax x + lMax x + 1)) := by
    have hfinal : g^[rounds (some (list x, init x))] (some (list x, init x)) =
        some ([], (list x).foldl step (init x)) := by
      rw [hrounds, iterate_foldStep step a₀ (init x₀) _ _ le_rfl]; simp
    rw [← hfinal]
    apply (hloop _).mono
    · dsimp only [A]; rw [hrounds]
      calc
        _ ≤ (cF + ci) * (((list x).length + 1) *
            ((cs + 2) * (tMax x + lMax x + 1))) := by
          apply Nat.mul_le_mul_left _
          apply Nat.mul_le_mul_left _
          have ht := htx x; have hl := hlx x
          nlinarith
        _ = _ := by ring
    · dsimp only [D]
      calc
        _ ≤ (ci * (cF + 1) + 1) * ((cs + 2) * (sMax x + lMax x + 1)) := by
          apply Nat.mul_le_mul_left _
          have hs := hsx x; have hl := hlx x
          nlinarith
        _ = _ := by ring
  let K₁ := 6 * max (max kP kS + 2) (kF + 1 + 2) + 20
  let K₂ := 6 * max (max (max kP kS + 2) (kF + 1 + 2) + 2) kf + 20
  let C := cStart + A + D + (cf + 10) * cs + K₁ + K₂ + cf + 30
  refine ⟨C, _, _, inferInstance,
    tmf.comp ((tmF.iterateWhile true).comp (tmS.comp tmP true) true) true, fun x => ?_⟩
  have h := ((hstart x).comp (hrun x) true).comp
    (hf (some ([], (list x).foldl step (init x)))) true
  apply h.mono
  · have hi : (encO (some (list x, init x))).length ≤ cs * (lMax x + 1) := by
      apply (hcs _).trans (Nat.mul_le_mul_left cs _)
      have hh := hlMax x 0 (Nat.zero_le _); simpa using Nat.add_le_add_right hh 1
    have he : (encO (some ([], (list x).foldl step (init x)))).length ≤
        cs * (lMax x + 1) := by
      apply (hcs _).trans (Nat.mul_le_mul_left cs _)
      have hh := hlMax x (list x).length le_rfl
      simpa using Nat.add_le_add_right hh 1
    have hm : lMax x + 1 ≤ ((list x).length + 1) * (tMax x + lMax x + 1) := by
      nlinarith
    change cStart * (t x + lMax x + 1) +
      A * (((list x).length + 1) * (tMax x + lMax x + 1)) +
      4 * (encO (some (list x, init x))).length + 9 +
      cf * ((encO (some ([], (list x).foldl step (init x)))).length + 1) +
      4 * (encO (some ([], (list x).foldl step (init x)))).length + 9 ≤ _
    have hiw := Nat.mul_le_mul_left 4 hi
    have hew := Nat.mul_le_mul_left (cf + 4) he
    have him := Nat.mul_le_mul_left (cStart + (cf + 8) * cs) hm
    dsimp only [C]
    ring_nf at hiw hew him ⊢
    omega
  · have hi : (encO (some (list x, init x))).length ≤ cs * (lMax x + 1) := by
      apply (hcs _).trans (Nat.mul_le_mul_left cs _)
      have hh := hlMax x 0 (Nat.zero_le _); simpa using Nat.add_le_add_right hh 1
    have he : (encO (some ([], (list x).foldl step (init x)))).length ≤
        cs * (lMax x + 1) := by
      apply (hcs _).trans (Nat.mul_le_mul_left cs _)
      have hh := hlMax x (list x).length le_rfl
      simpa using Nat.add_le_add_right hh 1
    change cStart * (s x + lMax x + 1) + D * (sMax x + lMax x + 1) +
      5 * (encO (some (list x, init x))).length + K₁ +
      cf * ((encO (some ([], (list x).foldl step (init x)))).length + 1) +
      5 * (encO (some ([], (list x).foldl step (init x)))).length + K₂ ≤ _
    have hiw := Nat.mul_le_mul_left 5 hi
    have hew := Nat.mul_le_mul_left (cf + 5) he
    dsimp only [C]
    ring_nf at hiw hew ⊢
    omega
end Turing.MultiTapeTM.Internal.FoldCompiler


