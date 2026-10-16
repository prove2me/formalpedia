-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Reader
-- name    : MIPRE_Foundations_Cost_Reader
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:45:31.345772+00:00
-- url     : https://prove2.me/theorems/a4e67a86-8ae6-47cb-8d9b-059411df0d85
-- title:
--   Programs as readers of a shared input: applicative combinators and generic list operations
-- statement:
--   Let `PolyTimeFun α β` be the polynomial-time functions of the ambient model (a function, a closed program, a polynomial time bound and a correctness proof), with `comp`, `pair`, `fst`, `snd`, `const`, `cons`, `map`, `zip`, `casesList` and `foldl` from earlier bundles, and `Unary = List Unit`. A `PolyTimeFun ι α` is read as a *reader* of a shared input `ι`. Names are in `MIPRE.Cost.PolyTimeFun`.
--
--   Applicative combinators. For a program `F` and readers `f`, `g`, `h` of `ι`: `ap₁ F f := F.comp f`; `ap₂ F f g := F.comp (f.pair g)`; `ap₃ F f g h := F.comp (f.pair (g.pair h))`; `ap₂' F f : PolyTimeFun (ι × β) γ := F.comp ((f.comp fst).pair snd)`, a two-argument program whose left argument the reader `f` supplies; and `listOf : List (PolyTimeFun ι α) → PolyTimeFun ι (List α)` (`[] ↦ const []`, `f :: fs ↦ f.cons (listOf fs)`). Their application equations are
--
--   $$\mathrm{ap}_3\ F\ f\ g\ h\ (i) = F\big(f(i), g(i), h(i)\big), \qquad \mathrm{listOf}\ [f_1, \dots, f_m]\ (i) = [f_1(i), \dots, f_m(i)] ,$$
--
--   and likewise `ap₁_apply`, `ap₂_apply`, `ap₂'_apply` (`ap₂' F f (i, b) = F (f i, b)`).
--
--   List operations, each with `toFun` the `List` function: `take : PolyTimeFun (List α × Unary) (List α)` (`(l, u) ↦ l.take u.length`, as `map fst` of `zip`), `tail` (`l ↦ l.tail`, by `casesList`), `headD d` (`l ↦ l.headD d`), `tailStep : PolyTimeFun (List α × Unit) (List α) := tail.comp fst`, `drop` (`(l, u) ↦ l.drop u.length`, a `foldl` of `tailStep` under the Cobham bound `X`) and `nthD d : ℕ → PolyTimeFun (List α) α` (`nthD d 0 = headD d`, `nthD d (k + 1) = (nthD d k).comp tail`).
--
--   Lemmas: `map_fst_zip` (`(l.zip u).map Prod.fst = l.take u.length`), `take_apply`, `tail_apply`, `headD_apply`, `esize_tail_le`, `tailStep_apply`, `esize_foldl_tailStep`, `tailStep_bounded` (`FoldBounded tailStep X`), `foldl_tailStep` (iterated `tail` is `drop`), `drop_apply` and `nthD_apply` (`nthD d k l = l.getD k d`).
--
--   **Formalization Note**. A point-free term built from `comp`, `pair`, `fst`, `snd` for a formula of many conjuncts is unreadable; in the applicative reading a program transcribes its mathematical definition line for line and its `toFun` is definitionally the function transcribed, so the `congr` that names it closes by `rfl`. Lengths are passed in unary. `tailStep` has no docstring in the source. Definitions carrying a `Polynomial ℕ` are noncomputable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Reader.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Reader.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_Fold

/-!
# Programs as readers of a shared input

A program built by composition out of `comp`, `pair`, `fst` and `snd` is written point-free,
and a point-free term for a formula of forty conjuncts is unreadable. This file gives the
applicative reading instead: a `PolyTimeFun ι α` is a *reader* of the shared input `ι`, and
`ap₁`, `ap₂`, `ap₃` and `listOf` apply a program to readers. In that style a program
transcribes its mathematical definition line for line, and its `toFun` is definitionally the
function it transcribes, so the `congr` that names it closes by `rfl`.

Also here, because they are the list operations the describer's programs need and they are
generic: `take`, `tail`, `headD` and `nthD` (`planning/succinct-cook-levin.md`, S3).
-/

namespace MIPRE.Cost.PolyTimeFun

variable {ι α β γ δ : Type*} [SizedEncoding ι] [SizedEncoding α] [SizedEncoding β]
  [SizedEncoding γ] [SizedEncoding δ]

/-! ## Applying a program to readers -/

/-- Apply a one-argument program to a reader. -/
noncomputable def ap₁ (F : PolyTimeFun α β) (f : PolyTimeFun ι α) : PolyTimeFun ι β := F.comp f

@[simp] theorem ap₁_apply (F : PolyTimeFun α β) (f : PolyTimeFun ι α) (i : ι) :
    ap₁ F f i = F (f i) := rfl

/-- Apply a two-argument program to two readers. -/
noncomputable def ap₂ (F : PolyTimeFun (α × β) γ) (f : PolyTimeFun ι α) (g : PolyTimeFun ι β) :
    PolyTimeFun ι γ := F.comp (f.pair g)

@[simp] theorem ap₂_apply (F : PolyTimeFun (α × β) γ) (f : PolyTimeFun ι α)
    (g : PolyTimeFun ι β) (i : ι) : ap₂ F f g i = F (f i, g i) := rfl

/-- Apply a three-argument program to three readers. -/
noncomputable def ap₃ (F : PolyTimeFun (α × β × γ) δ) (f : PolyTimeFun ι α)
    (g : PolyTimeFun ι β) (h : PolyTimeFun ι γ) : PolyTimeFun ι δ :=
  F.comp (f.pair (g.pair h))

@[simp] theorem ap₃_apply (F : PolyTimeFun (α × β × γ) δ) (f : PolyTimeFun ι α)
    (g : PolyTimeFun ι β) (h : PolyTimeFun ι γ) (i : ι) : ap₃ F f g h i = F (f i, g i, h i) := rfl

/-- A two-argument program with its left argument curried away: the reader `f` of the shared
input supplies it. -/
noncomputable def ap₂' (F : PolyTimeFun (α × β) γ) (f : PolyTimeFun ι α) :
    PolyTimeFun (ι × β) γ :=
  F.comp ((f.comp fst).pair snd)

@[simp] theorem ap₂'_apply (F : PolyTimeFun (α × β) γ) (f : PolyTimeFun ι α) (p : ι × β) :
    ap₂' F f p = F (f p.1, p.2) := rfl

/-- A list of readers as a reader of the list of their values. -/
noncomputable def listOf : List (PolyTimeFun ι α) → PolyTimeFun ι (List α)
  | [] => const []
  | f :: fs => f.cons (listOf fs)

@[simp] theorem listOf_apply : ∀ (fs : List (PolyTimeFun ι α)) (i : ι),
    listOf fs i = fs.map fun f => f i
  | [], _ => rfl
  | f :: fs, i => by rw [listOf, cons_apply, listOf_apply fs i, List.map_cons]

/-! ## Prefixes, tails and heads -/

omit [SizedEncoding α] in
theorem map_fst_zip : ∀ (l : List α) (u : Unary), (l.zip u).map Prod.fst = l.take u.length
  | [], u => by simp
  | _ :: _, [] => by simp
  | a :: l, () :: u => by
    rw [List.zip_cons_cons, List.map_cons, map_fst_zip l u, List.length_cons, List.take_succ_cons]

/-- Taking a prefix, the length in unary. -/
noncomputable def take : PolyTimeFun (List α × Unary) (List α) :=
  congr ((map fst).comp zip) (fun p => p.1.take p.2.length) (by
    intro p
    simp only [comp_apply, map_apply, zip_apply]
    exact map_fst_zip p.1 p.2)

@[simp] theorem take_apply (p : List α × Unary) :
    (take : PolyTimeFun (List α × Unary) (List α)) p = p.1.take p.2.length := rfl

/-- The tail of a list. -/
noncomputable def tail : PolyTimeFun (List α) (List α) :=
  congr ((casesList (const []) (snd.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    List.tail (by
      intro l
      cases l with
      | nil => rfl
      | cons _ _ => rfl)

@[simp] theorem tail_apply (l : List α) : (tail : PolyTimeFun (List α) (List α)) l = l.tail := rfl

/-- The head of a list, or a default. -/
noncomputable def headD (d : α) : PolyTimeFun (List α) α :=
  congr ((casesList (const d) (fst.comp snd)).comp ((const ()).pair (PolyTimeFun.id _)))
    (fun l => l.headD d) (by
      intro l
      cases l with
      | nil => rfl
      | cons _ _ => rfl)

@[simp] theorem headD_apply (d : α) (l : List α) : headD d l = l.headD d := rfl

/-- Dropping a prefix, the length in unary: iterated `tail`. -/
theorem esize_tail_le (l : List α) : esize l.tail ≤ esize l := by
  cases l with
  | nil => exact le_rfl
  | cons a l => rw [List.tail_cons, esize_list_cons]; omega

noncomputable def tailStep : PolyTimeFun (List α × Unit) (List α) := tail.comp fst

@[simp] theorem tailStep_apply (p : List α × Unit) :
    (tailStep : PolyTimeFun (List α × Unit) (List α)) p = p.1.tail := rfl

theorem esize_foldl_tailStep : ∀ (pre : Unary) (s : List α),
    esize (pre.foldl (tailStep : PolyTimeFun (List α × Unit) (List α)).step s) ≤ esize s
  | [], _ => le_rfl
  | _ :: p, s => (esize_foldl_tailStep p _).trans (esize_tail_le s)

theorem tailStep_bounded :
    FoldBounded (tailStep : PolyTimeFun (List α × Unit) (List α)) Polynomial.X := by
  intro l s₀ pre _ _
  have h := esize_foldl_tailStep pre s₀
  rw [Polynomial.eval_X, esize_prod]
  omega

theorem foldl_tailStep : ∀ (u : Unary) (l : List α),
    u.foldl (tailStep : PolyTimeFun (List α × Unit) (List α)).step l = l.drop u.length
  | [], l => by rw [List.foldl_nil, List.length_nil, List.drop_zero]
  | () :: u, l => by
    rw [List.foldl_cons, foldl_tailStep u _, List.length_cons]
    show l.tail.drop u.length = _
    rw [← List.drop_one, List.drop_drop, Nat.add_comm]

/-- Dropping a prefix, the length in unary. -/
noncomputable def drop : PolyTimeFun (List α × Unary) (List α) :=
  congr ((foldl tailStep Polynomial.X tailStep_bounded).comp (snd.pair fst))
    (fun p => p.1.drop p.2.length) (by
      rintro ⟨l, u⟩
      simp only [comp_apply, pair_apply, fst_apply, snd_apply, foldl_apply]
      exact foldl_tailStep u l)

@[simp] theorem drop_apply (p : List α × Unary) :
    (drop : PolyTimeFun (List α × Unary) (List α)) p = p.1.drop p.2.length := rfl

/-- The `k`-th entry of a list, or a default. -/
noncomputable def nthD (d : α) : ℕ → PolyTimeFun (List α) α
  | 0 => headD d
  | k + 1 => (nthD d k).comp tail

@[simp] theorem nthD_apply : ∀ (d : α) (k : ℕ) (l : List α), nthD d k l = l.getD k d
  | d, 0, [] => rfl
  | d, 0, _ :: _ => rfl
  | d, k + 1, [] => by
    rw [nthD, comp_apply, tail_apply, List.tail_nil, nthD_apply d k []]
    simp
  | d, k + 1, a :: l => by
    rw [nthD, comp_apply, tail_apply, List.tail_cons, nthD_apply d k l]
    simp [List.getD_eq_getElem?_getD]

end MIPRE.Cost.PolyTimeFun


