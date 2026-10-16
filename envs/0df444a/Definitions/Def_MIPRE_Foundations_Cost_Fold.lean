-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Fold
-- name    : MIPRE_Foundations_Cost_Fold
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:44:43.528387+00:00
-- url     : https://prove2.me/theorems/a4df54cd-d936-4dbd-ad5b-1547d85a95dc
-- title:
--   The closure library: folds over lists under the Cobham condition, and the list combinators built from them
-- statement:
--   Let `PolyTimeFun α β` be the polynomial-time functions between encodable types: a function `toFun`, a closed program `code`, a polynomial `timeBound` and a proof that `code` computes `toFun` within `timeBound.eval (esize a)`, with `esize a = (encode a).size`; $X$ is the polynomial variable.
--
--   Encodings (`MIPRE.Cost`). `instSizedEncodingList`: lists encode elementwise as `cons`-chains, at low priority; `instSizedEncodingUnit` encodes `()` as `nil`; `Unary := List Unit` and `unary n := List.replicate n ()`.
--
--   The fold (`MIPRE.Cost.PolyTimeFun`). `Prog.foldBody F` is the loop body on the state `cons xs acc`: stop with `acc` on empty `xs`, else continue with `cons (tail xs) (F (acc, head xs))`. With `step F s a := F (s, a)`, the Cobham condition `FoldBounded F B` says `esize (pre.foldl F.step s₀) ≤ B.eval (esize (l, s₀))` whenever `l = pre ++ xs`. `foldStepBound F B` is the per-iteration bound, and `foldl F B hB : PolyTimeFun (List α × σ) σ` has code `.loop (foldBody F.code)`, bound `(X + 1) * (foldStepBound F B + 1)` and
--
--   $$\mathrm{foldl}\ F\ B\ h_B\ (l, s_0) = \mathrm{List.foldl}\ (\lambda\, s\ a.\ F(s, a))\ s_0\ l .$$
--
--   `foldlAdd F B hB` is the fold under the additive condition `esize (F (s, a)) ≤ esize s + B.eval (esize a)`. Retyping: `congr F f h` (same code and bound for an extensionally equal `f`), `ofEncodeEq f h` (code `var 0`, for `encode (f a) = encode a`) and `cast F f h` (the code of `F`, for `encode (f a) = encode (F a)`).
--
--   List combinators, with `toFun` the `List` function: `cons F G`, `reverse` (code `revProg`), `casesListFun N K` and `casesList N K` (case analysis on a list component), `map F`, `append`, `zipStep`, `zipStepF` and `zip`, `length` (unary), `replicate` (`(u, b) ↦ List.replicate |u| b`), `mapWith F` (map with a parameter).
--
--   Lemmas: twelve encoding and size equations of lists and unary numerals, the runs of `foldBody` (`_wellScoped`, `_stop`, `_step`), `foldl_esize_le` and `foldBounded_of_additive`, every combinator's `_apply` equation, and the pure fold identities (`foldl_cons_map`, `foldl_cons_reverse`, `foldl_zipStep_nil`, `foldl_zipStep`, `foldl_replicate`).
--
--   **Formalization Note**. Every combinator's `toFun` is the corresponding `List` function (programs are defined by their meaning, only the bound is inherited), and the `_apply` lemmas hold by `rfl`. The loop state of `foldl` is the input pair itself. Definitions carrying a `Polynomial ℕ` are noncomputable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Fold.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Fold.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B

/-!
# The closure library, part IV: folds over lists

The generic iteration combinator of the library, `PolyTimeFun.foldl`: a fold of a
polynomial-time body over a list is polynomial-time provided the accumulator grows by at
most an additive polynomial in the element at each step (the Cobham condition
`esize (F (s, a)) ≤ esize s + B (esize a)`), and from it `cons`, `casesList`, `map`, `zip`,
`append`, `replicate` and `reverse` (`planning/succinct-cook-levin.md`, S3). Every
combinator's `toFun` is the corresponding `List` function, so that a program assembled
from them is *defined* by its mathematical meaning and only its time bound is inherited.

Lists of an arbitrary encodable type encode as `cons`-chains of the encodings
(`instSizedEncodingList`, at low priority so that the existing instances for bit strings
and gate lists are still found first; they agree definitionally).
-/

namespace MIPRE.Cost

open Polynomial

/-! ## Lists of encodable values -/

/-- Lists encode elementwise, as `cons`-chains. -/
instance (priority := low) instSizedEncodingList {α : Type*} [SizedEncoding α] :
    SizedEncoding (List α) where
  encode := Data.ofList encode
  decode := Data.toList? decode
  decode_encode := Data.toList?_ofList SizedEncoding.decode_encode

section ListEnc

variable {α : Type*} [SizedEncoding α]

theorem encode_list_nil : (encode ([] : List α) : Data) = .nil := rfl

theorem encode_list_cons (a : α) (l : List α) :
    (encode (a :: l) : Data) = .cons (encode a) (encode l) := rfl

theorem encode_list_eq_list (l : List α) : (encode l : Data) = Data.list (l.map encode) :=
  Data.ofList_eq_list _ _

@[simp] theorem esize_list_nil : esize ([] : List α) = 1 := rfl

@[simp] theorem esize_list_cons (a : α) (l : List α) :
    esize (a :: l) = esize a + esize l + 1 := rfl

theorem esize_mem_le {a : α} {l : List α} (h : a ∈ l) : esize a + 1 ≤ esize l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [esize_list_cons]; omega
    · have := ih h; simp only [esize_list_cons]; omega

theorem length_le_esize_list (l : List α) : l.length ≤ esize l :=
  Data.length_le_size_ofList _ l

theorem esize_list_append (l₁ l₂ : List α) : esize (l₁ ++ l₂) + 1 = esize l₁ + esize l₂ := by
  induction l₁ with
  | nil => simp; omega
  | cons a l ih => simp only [List.cons_append, esize_list_cons]; omega

end ListEnc

/-! ## Program layer: the fold loop -/

namespace Prog

/-- The body of the fold loop of `F`: on the state `cons xs acc`, stop with `acc` if `xs` is
empty; otherwise bind `acc' := F (acc, head xs)` and continue with `cons (tail xs) acc'`. -/
def foldBody (F : Prog) : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.let_ (.let_ (.cons (.var 3) (.var 0)) F)
      (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))))

theorem foldBody_wellScoped {F : Prog} (hF : F.WellScoped 1) : (foldBody F).WellScoped 1 := by
  simp [foldBody, WellScoped, hF.mono (show 1 ≤ 1 + 2 + 2 + 1 by omega) F]

theorem foldBody_stop {F : Prog} (acc : Data) :
    Eval [.cons .nil acc] (foldBody F) (.cons .nil acc) (acc.size + 5) := by
  have e := Eval.elim_cons (env := [Data.cons .nil acc]) (i := 0) (n := .nil) (a := .nil) (b := acc)
    (by simp)
    (Eval.elim_nil (i := 0)
      (c := .let_ (.let_ (.cons (.var 3) (.var 0)) F)
        (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))) (by simp)
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := acc) (by simp))))
  exact e.cast_cost (by omega)

theorem foldBody_step {F : Prog} (hF : F.WellScoped 1) (h rest acc acc' : Data) (t : ℕ)
    (hrun : Eval [.cons acc h] F acc' t) :
    Eval [.cons (.cons h rest) acc] (foldBody F)
      (.cons (.cons .nil .nil) (.cons rest acc'))
      (acc.size + h.size + rest.size + acc'.size + t + 14) := by
  have e := Eval.elim_cons (env := [Data.cons (.cons h rest) acc]) (i := 0) (n := .nil)
    (a := .cons h rest) (b := acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := h) (b := rest) (by simp)
      (Eval.let_
        (Eval.let_
          (Eval.cons (Eval.var_of_get (i := 3) (v := acc) (by simp))
            (Eval.var_of_get (i := 0) (v := h) (by simp)))
          (Eval.append_of_wellScoped hrun hF _))
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 2) (v := rest) (by simp))
            (Eval.var_of_get (i := 0) (v := acc') (by simp))))))
  exact e.cast_cost (by omega)

end Prog

/-! ## Function layer -/

namespace PolyTimeFun

variable {α β γ σ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ] [SizedEncoding σ]

/-- The step function of a fold, as a binary function. -/
abbrev step (F : PolyTimeFun (σ × α) σ) (s : σ) (a : α) : σ := F (s, a)

/-- The size bound along a fold under the additive Cobham condition: after consuming `pre`,
the accumulator has size at most `esize s₀ + |pre| · B (esize l)` whenever the elements of
`pre` are elements of `l`. -/
theorem foldl_esize_le (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ)
    (hB : ∀ s a, esize (F (s, a)) ≤ esize s + B.eval (esize a)) (l : List α) (s₀ : σ) :
    ∀ pre : List α, pre ⊆ l →
      esize (pre.foldl F.step s₀) ≤ esize s₀ + pre.length * B.eval (esize l) := by
  intro pre hpre
  induction pre generalizing s₀ with
  | nil => simp
  | cons a pre ih =>
    have ha : a ∈ l := hpre (List.mem_cons_self ..)
    have hpre' : pre ⊆ l := fun x hx => hpre (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons, List.length_cons]
    refine (ih (F.step s₀ a) hpre').trans ?_
    have h1 : esize (F.step s₀ a) ≤ esize s₀ + B.eval (esize a) := hB s₀ a
    have h2 := polynomial_eval_mono B (show esize a ≤ esize l by have := esize_mem_le ha; omega)
    rw [Nat.succ_mul]
    omega

/-- **The Cobham condition** for folding `F` over a list: along the fold of any list `l` from
any `s₀`, the accumulator has size at most `B (esize (l, s₀))`. -/
def FoldBounded (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ) : Prop :=
  ∀ (l : List α) (s₀ : σ) (pre xs : List α), l = pre ++ xs →
    esize (pre.foldl F.step s₀) ≤ B.eval (esize (l, s₀))

/-- The additive condition — each step grows the accumulator by at most `B (esize a)` — is a
Cobham condition with the bound `X + X · B`. -/
theorem foldBounded_of_additive (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ)
    (hB : ∀ s a, esize (F (s, a)) ≤ esize s + B.eval (esize a)) :
    FoldBounded F (X + X * B) := by
  intro l s₀ pre xs hl
  refine (foldl_esize_le F B hB l s₀ pre (by rw [hl]; exact List.subset_append_left _ _)).trans ?_
  have hpl : pre.length ≤ esize (l, s₀) := by
    have := congrArg List.length hl
    have := length_le_esize_list l
    simp only [List.length_append, esize_prod] at *; omega
  have hsN : esize s₀ ≤ esize (l, s₀) := by simp only [esize_prod]; omega
  have hBl : B.eval (esize l) ≤ B.eval (esize (l, s₀)) :=
    polynomial_eval_mono B (by simp only [esize_prod]; omega)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  exact Nat.add_le_add hsN (Nat.mul_le_mul hpl hBl)

/-- The per-iteration cost bound of the fold loop, as a polynomial in `esize (l, s₀)`. -/
noncomputable def foldStepBound (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ) : Polynomial ℕ :=
  F.timeBound.comp (B + X + 1) + 2 * B + 3 * X + C 14

/-- **Folding a polynomial-time body over a list**, under the Cobham condition `FoldBounded F B`:
`foldl F B hB (l, s₀) = l.foldl (fun s a => F (s, a)) s₀`. The loop state is the input pair
itself. -/
noncomputable def foldl (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ) (hB : FoldBounded F B) :
    PolyTimeFun (List α × σ) σ where
  toFun p := p.1.foldl F.step p.2
  code := .loop (Prog.foldBody F.code)
  closed := ⟨Nat.zero_lt_one, Prog.foldBody_wellScoped F.closed⟩
  timeBound := (X + 1) * (foldStepBound F B + 1)
  computes p := by
    obtain ⟨l, s₀⟩ := p
    set N := esize (l, s₀) with hN
    have hlN : esize l ≤ N := by simp only [hN, esize_prod]; omega
    have hsN : esize s₀ ≤ N := by simp only [hN, esize_prod]; omega
    have hacc : ∀ pre xs : List α, l = pre ++ xs →
        esize (pre.foldl F.step s₀) ≤ B.eval N := fun pre xs hl => hB l s₀ pre xs hl
    -- the loop
    have key := Eval.loop_of_invariant (Prog.foldBody_wellScoped F.closed) []
      (fun s => ∃ pre xs : List α, l = pre ++ xs ∧
        s = .cons (encode xs) (encode (pre.foldl F.step s₀)))
      (fun s => match s with | .cons xs _ => xs.size | .nil => 0)
      (fun r => r = encode (l.foldl F.step s₀))
      ((foldStepBound F B).eval N) ?_ (.cons (encode l) (encode s₀)) ⟨[], l, by simp, by simp⟩
    · obtain ⟨r, t, ht, rfl, hrun⟩ := key
      refine ⟨t, ?_, hrun⟩
      refine ht.trans ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      have : (encode l : Data).size + 1 ≤ N + 1 := by
        show esize l + 1 ≤ N + 1; omega
      exact Nat.mul_le_mul this le_rfl
    · rintro s ⟨pre, xs, hl, rfl⟩
      rcases xs with _ | ⟨a, xs⟩
      · left
        refine ⟨_, _, ?_, Prog.foldBody_stop _, by rw [hl, List.append_nil]⟩
        have := hacc pre [] hl
        simp only [foldStepBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_one, Polynomial.eval_ofNat]
        show esize (pre.foldl F.step s₀) + 5 ≤ _
        omega
      · right
        obtain ⟨t, ht, hrun⟩ := F.computes (pre.foldl F.step s₀, a)
        refine ⟨.nil, .nil, _, _, ?_, Prog.foldBody_step F.closed _ _ _ _ t hrun,
          ⟨pre ++ [a], xs, by rw [hl, List.append_assoc, List.singleton_append], ?_⟩, ?_⟩
        · -- the cost of the step
          have h1 := hacc pre (a :: xs) hl
          have h2 := hacc (pre ++ [a]) xs (by rw [hl, List.append_assoc, List.singleton_append])
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h2
          have ha : esize a + 1 ≤ esize l := esize_mem_le (by rw [hl]; simp)
          have hxs : esize xs ≤ esize l := by
            have := esize_list_append pre (a :: xs); rw [← hl] at this
            simp only [esize_list_cons] at this; omega
          have hF : t ≤ F.timeBound.eval (B.eval N + N + 1) := by
            refine ht.trans (polynomial_eval_mono _ ?_)
            simp only [esize_prod]; omega
          simp only [foldStepBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_one, Polynomial.eval_ofNat]
          change esize (pre.foldl F.step s₀) + esize a + esize xs + esize (F.step _ a) + t + 14 ≤ _
          omega
        · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
        · show (encode xs : Data).size < (encode (a :: xs) : Data).size
          rw [encode_list_cons]; simp only [Data.size_cons]; omega

@[simp] theorem foldl_apply (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ) (hB : FoldBounded F B)
    (l : List α) (s₀ : σ) : foldl F B hB (l, s₀) = l.foldl (fun s a => F (s, a)) s₀ := rfl

/-- Folding under the additive condition. -/
noncomputable def foldlAdd (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ)
    (hB : ∀ s a, esize (F (s, a)) ≤ esize s + B.eval (esize a)) : PolyTimeFun (List α × σ) σ :=
  foldl F (X + X * B) (foldBounded_of_additive F B hB)

@[simp] theorem foldlAdd_apply (F : PolyTimeFun (σ × α) σ) (B : Polynomial ℕ)
    (hB : ∀ s a, esize (F (s, a)) ≤ esize s + B.eval (esize a)) (l : List α) (s₀ : σ) :
    foldlAdd F B hB (l, s₀) = l.foldl (fun s a => F (s, a)) s₀ := rfl

/-! ## Derived combinators -/

/-- Replacing the function of a `PolyTimeFun` by an extensionally equal one. -/
noncomputable def congr (F : PolyTimeFun α β) (f : α → β) (h : ∀ a, F a = f a) :
    PolyTimeFun α β where
  toFun := f
  code := F.code
  closed := F.closed
  timeBound := F.timeBound
  computes a := h a ▸ F.computes a

@[simp] theorem congr_apply (F : PolyTimeFun α β) (f : α → β) (h : ∀ a, F a = f a) (a : α) :
    congr F f h a = f a := rfl

/-- A function whose output encodes exactly as its input is computed by `var 0`. -/
noncomputable def ofEncodeEq (f : α → β) (h : ∀ a, (encode (f a) : Data) = encode a) :
    PolyTimeFun α β where
  toFun := f
  code := .var 0
  closed := Nat.zero_lt_one
  timeBound := X + 1
  computes a := ⟨esize a + 1, by simp, by rw [h]; exact Eval.var _ _⟩

@[simp] theorem ofEncodeEq_apply (f : α → β) (h : ∀ a, (encode (f a) : Data) = encode a) (a : α) :
    ofEncodeEq f h a = f a := rfl

/-- Retyping the output: a function whose values encode as the values of `F` is computed by
the program of `F`. -/
noncomputable def cast (F : PolyTimeFun α β) (f : α → γ)
    (h : ∀ a, (encode (f a) : Data) = encode (F a)) : PolyTimeFun α γ where
  toFun := f
  code := F.code
  closed := F.closed
  timeBound := F.timeBound
  computes a := by
    obtain ⟨t, ht, e⟩ := F.computes a
    exact ⟨t, ht, by rw [h]; exact e⟩

@[simp] theorem cast_apply (F : PolyTimeFun α β) (f : α → γ)
    (h : ∀ a, (encode (f a) : Data) = encode (F a)) (a : α) : cast F f h a = f a := rfl

/-- Consing. -/
noncomputable def cons (F : PolyTimeFun α β) (G : PolyTimeFun α (List β)) :
    PolyTimeFun α (List β) where
  toFun a := F a :: G a
  code := .cons F.code G.code
  closed := ⟨F.closed, G.closed⟩
  timeBound := F.timeBound + G.timeBound + 1
  computes a := by
    obtain ⟨t₁, h₁, e₁⟩ := F.computes a
    obtain ⟨t₂, h₂, e₂⟩ := G.computes a
    refine ⟨t₁ + t₂ + 1, ?_, Eval.cons e₁ e₂⟩
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    omega

@[simp] theorem cons_apply (F : PolyTimeFun α β) (G : PolyTimeFun α (List β)) (a : α) :
    F.cons G a = F a :: G a := rfl

/-- Reversal. -/
noncomputable def reverse : PolyTimeFun (List α) (List α) where
  toFun := List.reverse
  code := Prog.revProg
  closed := Prog.revProg_wellScoped
  timeBound := (X + 2) * (X + 13)
  computes l := by
    obtain ⟨t, ht, hrun⟩ := Prog.revProg_runs (l.map encode)
    refine ⟨t, ?_, ?_⟩
    · refine ht.trans ?_
      have h1 := length_le_esize_list l
      have h2 : (Data.list (l.map encode)).size = esize l := by
        rw [esize, encode_list_eq_list]
      simp only [List.length_map, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_ofNat, h2]
      exact Nat.mul_le_mul (by omega) (by omega)
    · rw [encode_list_eq_list, encode_list_eq_list, List.map_reverse]
      exact hrun

@[simp] theorem reverse_apply (l : List α) : (reverse : PolyTimeFun (List α) (List α)) l = l.reverse :=
  rfl

/-- Case analysis on a list: the function of `casesList`. -/
def casesListFun (N : α → β) (K : α × (γ × List γ) → β) : α × List γ → β
  | (a, []) => N a
  | (a, h :: t) => K (a, (h, t))

/-- Case analysis on a list component: `casesList N K (a, [])` is `N a` and
`casesList N K (a, h :: t)` is `K (a, (h, t))`. -/
noncomputable def casesList (N : PolyTimeFun α β) (K : PolyTimeFun (α × (γ × List γ)) β) :
    PolyTimeFun (α × List γ) β where
  toFun := casesListFun N K
  code := .elim 0 .nil (.elim 1 (Prog.callVar 0 N.code)
    (.let_ (.cons (.var 2) (.cons (.var 0) (.var 1))) K.code))
  closed := by
    simp [Prog.WellScoped, Prog.callVar, N.closed.mono (show 1 ≤ 4 by omega) _,
      K.closed.mono (show 1 ≤ 6 by omega) _]
  timeBound := X + N.timeBound + K.timeBound + Polynomial.C 6
  computes p := by
    obtain ⟨a, l⟩ := p
    rcases l with _ | ⟨h, t⟩
    · obtain ⟨t₀, ht₀, e₀⟩ := N.computes a
      have hm := polynomial_eval_mono N.timeBound (show esize a ≤ esize a + 1 + 1 by omega)
      refine ⟨(esize a + 1 + t₀ + 1) + 1 + 1, ?_, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod,
          esize_list_nil]
        omega
      · refine Eval.elim_cons (env := [encode (a, [])]) (i := 0) (a := encode a)
          (b := encode ([] : List γ)) (by simp [encode_prod]) ?_
        refine Eval.elim_nil (i := 1) (by simp [encode_list_nil]) ?_
        exact Prog.callVar_eval (i := 0) N.closed (by simp) e₀
    · obtain ⟨t₀, ht₀, e₀⟩ := K.computes (a, (h, t))
      simp only [esize_prod] at ht₀
      refine ⟨((esize a + 1 + ((esize h + 1) + (esize t + 1) + 1) + 1) + t₀ + 1) + 1 + 1, ?_, ?_⟩
      · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod,
          esize_list_cons]
        omega
      · refine Eval.elim_cons (env := [encode (a, h :: t)]) (i := 0) (a := encode a)
          (b := encode (h :: t)) (by simp [encode_prod]) ?_
        refine Eval.elim_cons (i := 1) (a := encode h) (b := encode t)
          (by simp [encode_list_cons]) ?_
        refine Eval.let_ (Eval.cons (Eval.var_of_get (i := 2) (v := encode a) (by simp))
          (Eval.cons (Eval.var_of_get (i := 0) (v := encode h) (by simp))
            (Eval.var_of_get (i := 1) (v := encode t) (by simp)))) ?_
        exact Eval.append_of_wellScoped (e₀ : Eval [encode (a, (h, t))] K.code _ t₀) K.closed _

@[simp] theorem casesList_nil (N : PolyTimeFun α β) (K : PolyTimeFun (α × (γ × List γ)) β) (a : α) :
    casesList N K (a, []) = N a := rfl

@[simp] theorem casesList_cons (N : PolyTimeFun α β) (K : PolyTimeFun (α × (γ × List γ)) β)
    (a : α) (h : γ) (t : List γ) : casesList N K (a, h :: t) = K (a, (h, t)) := rfl

end PolyTimeFun

/-! ## The list functions underlying the combinators -/

section ListLemmas

variable {α β : Type*}

/-- The fold underlying `map`. -/
theorem foldl_cons_map (f : α → β) (l : List α) (init : List β) :
    (l.foldl (fun acc a => f a :: acc) init).reverse = init.reverse ++ l.map f := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp

/-- The fold underlying `append`. -/
theorem foldl_cons_reverse (l₁ l₂ : List α) :
    l₁.reverse.foldl (fun acc a => a :: acc) l₂ = l₁ ++ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons a l ih => simp [List.foldl_append, ih]

/-- The step of the zip fold: on the state `(l₂, acc)` and the element `a`, consume the head
of `l₂`. -/
def zipStep (s : List β × List (α × β)) (a : α) : List β × List (α × β) :=
  match s.1 with
  | [] => ([], s.2)
  | b :: l₂ => (l₂, (a, b) :: s.2)

theorem foldl_zipStep_nil (l : List α) (acc : List (α × β)) :
    l.foldl zipStep ([], acc) = ([], acc) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem foldl_zipStep (l₁ : List α) (l₂ : List β) (acc : List (α × β)) :
    ((l₁.foldl zipStep (l₂, acc)).2).reverse = acc.reverse ++ l₁.zip l₂ := by
  induction l₁ generalizing l₂ acc with
  | nil => simp
  | cons a l₁ ih =>
    rcases l₂ with _ | ⟨b, l₂⟩
    · simp only [List.foldl_cons, zipStep, List.zip_nil_right, List.append_nil, foldl_zipStep_nil]
    · simp [List.foldl_cons, zipStep, ih]

/-- The fold underlying `replicate`: the state carries the value to replicate. -/
theorem foldl_replicate (u : List Unit) (acc : List β) (b : β) :
    (u.foldl (fun (s : List β × β) (_ : Unit) => (s.2 :: s.1, s.2)) (acc, b)) =
      (List.replicate u.length b ++ acc, b) := by
  induction u generalizing acc with
  | nil => rfl
  | cons _ u ih => rw [List.foldl_cons, ih, List.length_cons, List.replicate_succ', List.append_assoc]; rfl

end ListLemmas

namespace PolyTimeFun

variable {α β γ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ]

/-- Mapping a polynomial-time function over a list. -/
noncomputable def map (F : PolyTimeFun α β) : PolyTimeFun (List α) (List β) :=
  congr (reverse.comp ((foldlAdd (cons (F.comp snd) fst) (F.timeBound + 1) (by
      intro s a
      have := F.esize_apply_le a
      simp only [cons_apply, comp_apply, snd_apply, fst_apply, esize_list_cons,
        Polynomial.eval_add, Polynomial.eval_one]
      omega)).comp ((id _).pair (const []))))
    (fun l => l.map F) (by
      intro l
      simp only [comp_apply, reverse_apply, foldlAdd_apply, cons_apply, snd_apply, fst_apply,
        pair_apply, id_apply, const_apply]
      exact foldl_cons_map F l [])

@[simp] theorem map_apply (F : PolyTimeFun α β) (l : List α) : map F l = l.map F := rfl

/-- Appending. -/
noncomputable def append : PolyTimeFun (List α × List α) (List α) :=
  congr ((foldlAdd (cons snd fst) (X + 1) (by
      intro s a
      simp only [cons_apply, snd_apply, fst_apply, esize_list_cons, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one]
      omega)).comp ((reverse.comp fst).pair snd))
    (fun p => p.1 ++ p.2) (by
      rintro ⟨l₁, l₂⟩
      simp only [comp_apply, foldlAdd_apply, cons_apply, snd_apply, fst_apply, pair_apply,
        reverse_apply]
      exact foldl_cons_reverse l₁ l₂)

@[simp] theorem append_apply (p : List α × List α) :
    (append : PolyTimeFun (List α × List α) (List α)) p = p.1 ++ p.2 := rfl

/-- The zip step as a polynomial-time function. -/
noncomputable def zipStepF : PolyTimeFun ((List β × List (α × β)) × α) (List β × List (α × β)) :=
  congr ((casesList ((const []).pair snd)
      ((snd.comp snd).pair (cons ((fst.comp fst).pair (fst.comp snd)) (snd.comp fst)))).comp
      ((snd.pair (snd.comp fst)).pair (fst.comp fst)))
    (fun p => zipStep p.1 p.2) (by
      rintro ⟨⟨l₂, acc⟩, a⟩
      rcases l₂ with _ | ⟨b, l₂⟩ <;> simp [zipStep])

@[simp] theorem zipStepF_apply (p : (List β × List (α × β)) × α) : zipStepF p = zipStep p.1 p.2 :=
  rfl

/-- Zipping two lists. -/
noncomputable def zip : PolyTimeFun (List α × List β) (List (α × β)) :=
  congr (reverse.comp (snd.comp ((foldlAdd zipStepF (X + 2) (by
      rintro ⟨l₂, acc⟩ a
      rcases l₂ with _ | ⟨b, l₂⟩
      · simp only [zipStepF_apply, zipStep, esize_prod, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_ofNat]
        omega
      · simp only [zipStepF_apply, zipStep, esize_prod, esize_list_cons, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_ofNat]
        omega)).comp (fst.pair (snd.pair (const []))))))
    (fun p => p.1.zip p.2) (by
      rintro ⟨l₁, l₂⟩
      simp only [comp_apply, reverse_apply, snd_apply, foldlAdd_apply, pair_apply, fst_apply,
        const_apply, zipStepF_apply]
      exact foldl_zipStep l₁ l₂ [])

@[simp] theorem zip_apply (p : List α × List β) :
    (zip : PolyTimeFun (List α × List β) (List (α × β))) p = p.1.zip p.2 := rfl

end PolyTimeFun

/-! ## Unary numerals as lists of units -/

/-- The unit encodes as the atom, so that a list of `n` units is the unary numeral
`Data.ofNat n`. -/
instance : SizedEncoding Unit where
  encode _ := .nil
  decode _ := some ()
  decode_encode _ := rfl

/-- Unary numerals: lists of units. -/
abbrev Unary := List Unit

/-- The unary numeral of `n`. -/
def unary (n : ℕ) : Unary := List.replicate n ()

@[simp] theorem length_unary (n : ℕ) : (unary n).length = n := List.length_replicate

theorem encode_unary (n : ℕ) : (encode (unary n) : Data) = Data.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unary, List.replicate_succ, encode_list_cons, ← unary, ih]; rfl

@[simp] theorem esize_unary (n : ℕ) : esize (unary n) = 2 * n + 1 := by
  rw [esize, encode_unary, Data.size_ofNat]

theorem unary_length (u : Unary) : unary u.length = u := by
  induction u with
  | nil => rfl
  | cons _ u ih => rw [List.length_cons, unary, List.replicate_succ, ← unary, ih]

namespace PolyTimeFun

variable {α β γ : Type*} [SizedEncoding α] [SizedEncoding β] [SizedEncoding γ]

/-- The length of a list, in unary. -/
noncomputable def length : PolyTimeFun (List α) Unary :=
  congr (map (const ())) (fun l => unary l.length) (by
    intro l; simp only [map_apply, unary]
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.replicate_succ, ih])

@[simp] theorem length_apply (l : List α) : (length : PolyTimeFun (List α) Unary) l = unary l.length :=
  rfl

/-- `replicate (u, b) = List.replicate |u| b`, by a fold over the unary numeral `u` whose state
carries `b`. -/
noncomputable def replicate : PolyTimeFun (Unary × β) (List β) :=
  congr (fst.comp ((foldl (α := Unit) ((cons (snd.comp fst) (fst.comp fst)).pair (snd.comp fst))
      ((X + 1) * X) (by
        intro l s₀ pre xs hl
        obtain ⟨acc, b⟩ := s₀
        have hpre : pre.length ≤ l.length := by
          have := congrArg List.length hl; simp only [List.length_append] at this; omega
        have hlen := length_le_esize_list l
        have hf : List.foldl (((cons (snd.comp fst) (fst.comp fst)).pair (snd.comp fst)).step)
            (acc, b) pre = (List.replicate pre.length b ++ acc, b) := foldl_replicate pre acc b
        rw [hf]
        have hr : ∀ k, esize (List.replicate k b ++ acc) ≤ k * (esize b + 1) + esize acc := by
          intro k; induction k with
          | zero => simp
          | succ k ih =>
            simp only [List.replicate_succ, List.cons_append, esize_list_cons]
            rw [Nat.succ_mul]; omega
        have := hr pre.length
        set N := esize (l, (acc, b)) with hN
        have hNe : N = esize l + (esize acc + esize b + 1) + 1 := by simp [hN]
        have hk : pre.length * (esize b + 1) ≤ N * N :=
          Nat.mul_le_mul (by omega) (by omega)
        simp only [esize_prod, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one]
        have hm : (N + 1) * N = N * N + N := Nat.succ_mul _ _
        omega)).comp ((fst (α := Unary) (β := β)).pair ((const []).pair snd))))
    (fun p => List.replicate p.1.length p.2) (by
      rintro ⟨u, b⟩
      have hf : List.foldl (((cons (snd.comp fst) (fst.comp fst)).pair (snd.comp fst)).step)
          ([], b) u = (List.replicate u.length b ++ [], b) := foldl_replicate u [] b
      show (List.foldl _ ([], b) u).1 = _
      rw [hf, List.append_nil])

@[simp] theorem replicate_apply (p : Unary × β) : replicate p = List.replicate p.1.length p.2 := rfl

/-- Mapping with a parameter: `mapWith F (l, c) = l.map (fun a => F (a, c))`, by zipping `l`
with copies of `c`. -/
noncomputable def mapWith (F : PolyTimeFun (α × β) γ) : PolyTimeFun (List α × β) (List γ) :=
  congr ((map F).comp (zip.comp (fst.pair (replicate.comp ((length.comp fst).pair snd)))))
    (fun p => p.1.map fun a => F (a, p.2)) (by
      rintro ⟨l, c⟩
      simp only [comp_apply, map_apply, zip_apply, pair_apply, fst_apply, snd_apply, length_apply,
        replicate_apply, length_unary]
      induction l with
      | nil => rfl
      | cons a l ih =>
        rw [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.map_cons, List.map_cons, ih])

@[simp] theorem mapWith_apply (F : PolyTimeFun (α × β) γ) (p : List α × β) :
    mapWith F p = p.1.map fun a => F (a, p.2) := rfl

end PolyTimeFun

end MIPRE.Cost


