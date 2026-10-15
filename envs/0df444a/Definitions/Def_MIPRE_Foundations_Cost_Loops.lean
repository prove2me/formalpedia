-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Loops
-- name    : MIPRE_Foundations_Cost_Loops
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:04:28.149988+00:00
-- url     : https://prove2.me/theorems/c86eeea6-2c99-4d6f-b739-c64149bd860c
-- title:
--   The closure library II: the loop principle, list reversal and length in unary
-- statement:
--   This bundle gives the generic reasoning principle for `loop` and the first list primitives of the closure library.
--
--   `MIPRE.Cost.Data.list` encodes a list of trees $[a_1, \dots, a_k]$ as the $\mathtt{cons}$-chain $\mathtt{cons}(a_1, \mathtt{cons}(a_2, \dots, \mathtt{nil}))$ (it is `ofList` with the identity); a unary numeral $\mathrm{ofNat}(n)$ is the list of $n$ copies of $\mathtt{nil}$.
--
--   The main lemma of the bundle is the *loop principle* `MIPRE.Cost.Eval.loop_of_invariant`. Let $b$ be a closed loop body, $I$ an invariant on states, $\mu$ a natural-valued measure, $Q$ a postcondition and $B$ a uniform cost bound. If from every state $s$ satisfying $I$ the body either stops with a result satisfying $Q$, or continues to a state $s'$ with $I(s')$ and $\mu(s') < \mu(s)$, in both cases at cost at most $B$, then from every state $s$ with $I(s)$, in any environment whose head is $s$, the loop $\mathtt{loop}\ b$ stops with a result satisfying $Q$ at a cost
--   $$t \le (\mu(s) + 1)\,(B + 1).$$
--
--   Two primitives are then defined directly. `MIPRE.Cost.Prog.revOntoBody` and `MIPRE.Cost.Prog.revOntoProg` $= \mathtt{loop}\ \mathrm{revOntoBody}$ act on the state $\mathtt{cons}(xs, acc)$, moving the elements of $xs$ one by one onto $acc$, and compute $\mathrm{reverse}(xs) \mathbin{+\!\!+} acc$. `MIPRE.Cost.Prog.lenBody` and `MIPRE.Cost.Prog.lenProg` compute the length of a list in unary: the body, on the state $\mathtt{cons}(xs, acc)$, stops with $acc$ when $xs$ is empty and otherwise drops the head of $xs$ and prepends a $\mathtt{nil}$ to $acc$, so that running it to completion prepends $|xs|$ copies of $\mathtt{nil}$ to $acc$; `lenProg` runs it from $\mathtt{cons}(xs, \mathtt{nil})$ and returns $\mathrm{ofNat}(|xs|)$.
--
--   Besides the loop principle, the lemmas proved in the bundle are the equations of `list`, the identity $\mathrm{ofNat}(n) = \mathrm{list}(\mathrm{replicate}\ n\ \mathtt{nil})$, the step and stop behaviour of the length body with exact costs, the run of the length loop (prepending $|xs|$ copies of $\mathtt{nil}$ to $acc$ within cost $(|xs| + 1)(S + 13)$ for any $S$ dominating $\mathrm{size}(xs) + \mathrm{size}(acc) + 2|xs|$), the run of `lenProg` within cost $(|xs| + 2)(\mathrm{size}(xs) + 2|xs| + 14)$, and the well-scopedness of the programs.
--
--   **Formalization Note**. Every program is closed and takes its input in variable $0$; a loop's state is the input itself or a pair assembled by `let_` in front of the loop; a body stops with $\mathtt{cons}(\mathtt{nil}, \mathit{result})$ and continues with $\mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), \mathit{state}')$. Costs are stated as bounds of the form $(\text{iterations} + 1)\cdot(S + c)$ with $S$ any number dominating the sizes involved, so that the bound is a single atom for the `omega` decision procedure throughout an induction. The length body is reused with other accumulators in the next bundle: with a unary numeral as accumulator it is addition, and with the one-bit string $[\mathrm{true}]$ it produces the binary encoding of $2^{|xs|}$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Loops.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Loops.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure

/-!
# The closure library, part II: loops

The generic reasoning principle for `loop` (`Eval.loop_of_invariant`: an invariant, a
strictly decreasing measure and a uniform bound on the body's cost give a run of the loop
with cost `≤ (μ + 1) · (B + 1)`), and the list and unary-numeral primitives of the library
proved by direct induction: reversal onto an accumulator (`revOntoProg`, `revProg`) and
length in unary (`lenProg`). Lists are `cons`-chains (`Data.list`); unary numerals are lists
of `nil`s (`Data.ofNat`).

Conventions: every program is closed and takes its input in variable `0`; a loop's state
is the input itself or a pair assembled by `let_` in front of the loop; the body stops with
`cons nil result` and continues with `cons (cons nil nil) state'`. Costs are stated as
bounds of the form `(iterations + 1) · (S + c)` where `S` is any number dominating the sizes
involved, so that the bound is one atom for `omega` throughout an induction.
-/

namespace MIPRE.Cost

/-! ## Lists as data -/

namespace Data

/-- Lists of data as `cons`-chains. -/
def list : List Data → Data := ofList id

@[simp] theorem list_nil : list [] = nil := rfl

@[simp] theorem list_cons (a : Data) (l : List Data) : list (a :: l) = cons a (list l) := rfl

theorem ofList_eq_list {α : Type*} (f : α → Data) (l : List α) : ofList f l = list (l.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, ih]

@[simp] theorem size_list_cons (a : Data) (l : List Data) :
    (list (a :: l)).size = a.size + (list l).size + 1 := rfl

end Data

/-! ## The loop principle -/

namespace Eval

/-- **Loop with an invariant and a measure.** If from every state `s` satisfying `I` the
body either stops (with a result satisfying `Q`) or continues to a state `s'` satisfying
`I` with `μ s' < μ s`, at cost at most `B` in both cases, then `loop b` from any state
satisfying `I` stops with a result satisfying `Q`, at cost at most `(μ s + 1) · (B + 1)`. -/
theorem loop_of_invariant {b : Prog} (hb : b.WellScoped 1) (env : Env)
    (I : Data → Prop) (μ : Data → ℕ) (Q : Data → Prop) (B : ℕ)
    (hbody : ∀ s, I s →
      (∃ r t, t ≤ B ∧ Eval [s] b (.cons .nil r) t ∧ Q r) ∨
      (∃ x y s' t, t ≤ B ∧ Eval [s] b (.cons (.cons x y) s') t ∧ I s' ∧ μ s' < μ s)) :
    ∀ s, I s → ∃ r t, t ≤ (μ s + 1) * (B + 1) ∧ Q r ∧ Eval (s :: env) (.loop b) r t := by
  suffices key : ∀ n s, I s → μ s ≤ n →
      ∃ r t, t ≤ (n + 1) * (B + 1) ∧ Q r ∧ Eval (s :: env) (.loop b) r t from
    fun s hs => key (μ s) s hs le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs hμ
    rcases hbody s hs with ⟨r, t, ht, hrun, hq⟩ | ⟨x, y, s', t, ht, hrun, hs', hlt⟩
    · exact ⟨r, t + 1, by omega, hq, .loop_stop (Eval.append_of_wellScoped hrun hb env)⟩
    · omega
  | succ n ih =>
    intro s hs hμ
    rcases hbody s hs with ⟨r, t, ht, hrun, hq⟩ | ⟨x, y, s', t, ht, hrun, hs', hlt⟩
    · refine ⟨r, t + 1, ?_, hq, .loop_stop (Eval.append_of_wellScoped hrun hb env)⟩
      have h1 : B + 1 ≤ (n + 1 + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · obtain ⟨r, t', ht', hq, hrun'⟩ := ih s' hs' (by omega)
      refine ⟨r, t + t' + 1, ?_, hq,
        .loop_step (Eval.append_of_wellScoped hrun hb env) hrun'⟩
      have h2 : (n + 1 + 1) * (B + 1) = (n + 1) * (B + 1) + (B + 1) := Nat.succ_mul _ _
      omega

end Eval

/-! ## Reversal onto an accumulator -/

namespace Prog

/-- Body of `revOntoProg`: on state `cons xs acc`, stop with `acc` if `xs` is empty,
otherwise move the head of `xs` onto `acc`. -/
def revOntoBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.var 0) (.var 3)))))

/-- `revOntoProg` on `cons xs acc` computes `reverse xs ++ acc`. -/
def revOntoProg : Prog := .loop revOntoBody

/-! ## Length in unary -/

/-- Body of `lenProg`: on state `cons xs acc`, stop with `acc` if `xs` is empty, otherwise
drop the head of `xs` and prepend a `nil` to `acc`. Running it to completion prepends
`|xs|` copies of `nil` to `acc`: with `acc = nil` this is the length in unary, with `acc` a
unary numeral it is addition, with `acc = [true]` it is the bit string of `2 ^ |xs|`. -/
def lenBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3)))))

theorem lenBody_wellScoped : lenBody.WellScoped 1 := by simp [lenBody, WellScoped]

theorem lenBody_step (h : Data) (l acc : List Data) :
    Eval [.cons (.list (h :: l)) (.list acc)] lenBody
      (.cons (.cons .nil .nil) (.cons (.list l) (.list (.nil :: acc))))
      ((Data.list l).size + (Data.list acc).size + 11) := by
  have e := Eval.elim_cons (env := [Data.cons (.list (h :: l)) (.list acc)]) (i := 0)
    (n := .nil) (a := .list (h :: l)) (b := .list acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := h) (b := .list l) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.cons (Eval.var_of_get (i := 1) (v := .list l) (by simp))
          (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := .list acc) (by simp))))))
  exact e.cast_cost (by omega)

theorem lenBody_stop (acc : List Data) :
    Eval [.cons (.list []) (.list acc)] lenBody (.cons .nil (.list acc))
      ((Data.list acc).size + 5) := by
  have e := Eval.elim_cons (env := [Data.cons (.list []) (.list acc)]) (i := 0)
    (n := .nil) (a := .list []) (b := .list acc) (by simp)
    (Eval.elim_nil (i := 0)
      (c := .cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3)))) (by simp)
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp))))
  exact e.cast_cost (by omega)

/-- The loop of `lenBody` prepends `|xs|` copies of `nil` to `acc`, in time
`(|xs| + 1) · (S + 13)` for any `S` dominating `size xs + size acc + 2 |xs|`. -/
theorem lenLoop_runs (l acc : List Data) (env : Env) (S : ℕ)
    (hS : (Data.list l).size + (Data.list acc).size + 2 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 13),
      Eval (.cons (.list l) (.list acc) :: env) (.loop lenBody)
        (.list (List.replicate l.length .nil ++ acc)) t := by
  induction l generalizing acc with
  | nil =>
    refine ⟨(Data.list acc).size + 5 + 1, ?_, ?_⟩
    · simp only [List.length_nil, Data.list_nil, Data.size_nil] at hS ⊢; omega
    · simpa using Eval.loop_stop
        (Eval.append_of_wellScoped (lenBody_stop acc) lenBody_wellScoped env)
  | cons h l ih =>
    have hS' : (Data.list l).size + (Data.list (.nil :: acc)).size + 2 * l.length ≤ S := by
      simp only [Data.size_list_cons, List.length_cons, Data.size_nil] at hS ⊢; omega
    obtain ⟨t, ht, hrun⟩ := ih (.nil :: acc) hS'
    refine ⟨(Data.list l).size + (Data.list acc).size + 11 + t + 1, ?_, ?_⟩
    · simp only [Data.size_list_cons, List.length_cons] at hS
      have h2 : (l.length + 1 + 1) * (S + 13) = (l.length + 1) * (S + 13) + (S + 13) :=
        Nat.succ_mul _ _
      simp only [List.length_cons]
      omega
    · have hstep := Eval.append_of_wellScoped (lenBody_step h l acc) lenBody_wellScoped env
      have hrun' : Eval (Data.cons (.list l) (.list (.nil :: acc)) :: env) (.loop lenBody)
          (.list (List.replicate (h :: l).length .nil ++ acc)) t := by
        rw [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
        exact hrun
      exact Eval.loop_step hstep hrun'

/-- Length of a list in unary: `lenProg` on `xs` computes `ofNat |xs|`. -/
def lenProg : Prog := .let_ (.cons (.var 0) .nil) (.loop lenBody)

theorem lenProg_wellScoped : lenProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩, ⟨Nat.zero_lt_succ 1, lenBody_wellScoped.mono (by omega) _⟩⟩

theorem _root_.MIPRE.Cost.Data.ofNat_eq_list_replicate (n : ℕ) :
    Data.ofNat n = Data.list (List.replicate n .nil) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Data.ofNat, List.replicate_succ, ih]

theorem lenProg_runs (l : List Data) :
    ∃ t ≤ (l.length + 1 + 1) * ((Data.list l).size + 1 + 2 * l.length + 13),
      lenProg.Runs (.list l) (.ofNat l.length) t := by
  obtain ⟨t, ht, hrun⟩ := lenLoop_runs l [] [Data.list l]
    ((Data.list l).size + 1 + 2 * l.length) (by simp)
  refine ⟨(Data.list l).size + 1 + 1 + 1 + t + 1, ?_, ?_⟩
  · have h2 : (l.length + 1 + 1) * ((Data.list l).size + 1 + 2 * l.length + 13) =
        (l.length + 1) * ((Data.list l).size + 1 + 2 * l.length + 13) +
          ((Data.list l).size + 1 + 2 * l.length + 13) :=
      Nat.succ_mul _ _
    omega
  · have hpre := Eval.cons (Eval.var_of_get (env := [Data.list l]) (i := 0) (v := .list l)
      (by simp)) (Eval.nil [Data.list l])
    have hrun' : Eval (Data.cons (.list l) .nil :: [Data.list l]) (.loop lenBody)
        (.ofNat l.length) t := by
      simpa [Data.ofNat_eq_list_replicate] using hrun
    exact Eval.let_ hpre hrun'

end Prog

end MIPRE.Cost


