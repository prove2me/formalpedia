-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Toolkit
-- name    : MIPRE_Foundations_Cost_Toolkit
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:07:17.318981+00:00
-- url     : https://prove2.me/theorems/de62090d-e146-4471-b19d-20f725896f8f
-- title:
--   The efficient computability toolkit: s-m-n by hardcoding, and the universal machine structures
-- statement:
--   This bundle states the interface of the efficient computability toolkit — universal machine, s-m-n and Kleene recursion in the ambient cost model, following [MNY, Lemmas 2.1–2.3].
--
--   **Efficient s-m-n.** `MIPRE.Cost.hardcode` $p\ d = \mathtt{let}\ (\mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0))\ p$ is the program that runs $p$ on the pair $(d, \mathrm{input})$: the s-m-n map $s(p, d)$, with the value $d$ hardcoded as the first argument. `MIPRE.Cost.smnProg` is the fixed program computing this map on descriptions: on $\mathtt{cons}(\mathrm{toData}\ p, \mathrm{encode}\ a)$ it assembles $\mathrm{toData}(\mathrm{hardcode}\ p\ (\mathrm{encode}\ a))$, a tree of fixed shape around its two inputs. `MIPRE.Cost.PolyTimeFun.smn` $\alpha$ packages it as a polynomial-time function $\mathrm{Prog} \times \alpha \to \mathrm{Prog}$,
--   $$(p, a) \longmapsto \mathrm{hardcode}\ p\ (\mathrm{encode}\ a),$$
--   with time bound $X + 38$, generically in the type $\alpha$ of the hardcoded value.
--
--   **Universal machines.** `MIPRE.Cost.UniversalMachine` is a structure consisting of a closed program $\mathrm{univ}$ and an overhead polynomial $p_U \in \mathbb{N}[X]$ (the field `bound`) such that:
--
--   1. (*time transfer*) whenever a program $c$ on an input $v$ halts with the result $r$ at cost $t$, the program $\mathrm{univ}$ on the input $\mathtt{cons}(\mathrm{encode}\ c, v)$ halts with the same result $r$ at some cost $t' \le p_U(\mathrm{esize}(c) + \mathrm{size}(v) + t)$;
--   2. (*soundness*) whenever $\mathrm{univ}$ halts on $\mathtt{cons}(\mathrm{encode}\ c, v)$ with the result $r$, the program $c$ halts on $v$ with the result $r$.
--
--   For the clocked variant, `MIPRE.Cost.evalWithin` $c\ v\ k$ is the result of $c$ on $v$ if it halts within cost $k$, and undefined otherwise (an `Option`, well defined because the semantics is deterministic), and `MIPRE.Cost.clockedResult` $c\ v\ k$ is the value a clocked simulation returns: $\mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), r)$ ("halted, with result $r$") when $\mathrm{evalWithin}\ c\ v\ k = r$, and $\mathtt{nil}$ ("timeout") otherwise. `MIPRE.Cost.ClockedUniversalMachine` is a structure consisting of a closed program $\mathrm{univT}$ and a polynomial $p_{UT}$ such that for all programs $c$, inputs $v$ and budgets $k \in \mathbb{N}$, the program $\mathrm{univT}$ on the input $\mathtt{cons}(\mathrm{ofNat}\ k, \mathtt{cons}(\mathrm{encode}\ c, v))$ (budget in unary) halts with $\mathrm{clockedResult}\ c\ v\ k$ at some cost $t \le p_{UT}(k + \mathrm{esize}(c) + \mathrm{size}(v))$: a total, budget-bounded simulation.
--
--   The lemmas proved in the bundle are the well-scopedness of `smnProg`, its exact run (on $\mathtt{cons}(x, d)$ it produces the tree encoding of the hardcoded program at cost $\mathrm{size}(x) + \mathrm{size}(d) + 38$), and the application equation of `PolyTimeFun.smn`.
--
--   **Formalization Note**. The universal machines are *structures*, not existence statements, so that downstream definitions (the deciders of the compression argument, which simulate other programs under a budget) can name the program and its polynomial as data without any placeholder definition; their existence, `exists_efficient_universal` and `exists_clocked_universal` (blueprint `lem:universal-tm`), is proved in the `Universal` bundle by a self-interpreter. The s-m-n witness is stronger than the paper's: the time overhead of hardcoding is additive and linear in the sizes of $d$ and of the input, and the description grows by exactly $\mathrm{size}(d) + 35$ nodes, $\mathrm{esize}(\mathrm{hardcode}\ p\ d) = \mathrm{esize}(p) + \mathrm{size}(d) + 35$, where the paper has a polynomial. The Kleene recursion theorem (blueprint `lem:kleene`) is stated, in the `Kleene` bundle, in the one direction the compression argument uses. Mathlib has the computability halves of these results for `Nat.Partrec.Code`; everything with a time bound is new.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean; blueprint sec:rr-computability (lem:universal-tm, lem:smn, lem:kleene); [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemmas 2.1–2.3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (definition bundle: declarations the uploaded statements rest on);
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
# The efficient computability toolkit

The efficient versions of the universal machine, the s-m-n theorem, and Kleene's
recursion theorem, in the ambient cost model — blueprint Section
`sec:rr-computability` (`lem:universal-tm`, `lem:smn`, `lem:kleene`), following
[MNY, Lemmas 2.1–2.3]. Mathlib has the computability halves for `Nat.Partrec.Code`
(`Nat.Partrec.Code.smn`, `eval_part`, `fixed_point`); everything with a time bound
is new.

Contents:

* `hardcode`: the **efficient s-m-n**. `hardcode p d = let_ (cons (const d) (var 0)) p`
  binds the pair `(d, input)` as the input of `p`. The witness makes [MNY, Lemma 2.2]
  quantitative and stronger than stated there: the time overhead is *additive and linear*
  in the sizes of `d` and of the input, and the description grows by exactly `d.size + 35`
  nodes (paper: polynomial). `smn_polyTime` is the runtime version — the map is itself
  polynomial-time computable in the model (`smnProg`, linear time) — generic in the type of
  the hardcoded value.
* `UniversalMachine` / `exists_efficient_universal` (`lem:universal-tm`): a fixed closed
  program `univ` that, on the pair `(encode c, v)`, halts exactly when `c` halts on `v`,
  with the same result and polynomial time overhead — packaged as data (the program and its
  overhead polynomial); its existence is proved in `Cost/Universal.lean` by a
  self-interpreter.
* `ClockedUniversalMachine` / `exists_clocked_universal`: the time-bounded variant ("run
  `c` on `v` for `k` steps"), used by the recursive compression argument and by the
  pipeline's deciders (introspection and repetition simulate other deciders under a budget).
* `efficient_fixed_point` (`lem:kleene`, in `Cost/Kleene.lean`): Kleene's recursion theorem
  for a polynomial-time map on programs, with the runs of the fixed point bounded by those
  of its image at polynomial overhead — proved from the universal machine and `hardcode`.

The statement shapes were audited against the proof of the recursive compression lemma
(`planning/compression-track.md`, K0): the universal machines are structures so that
downstream definitions can name the program and its polynomial without any sorried `def`;
the runtime s-m-n is generic in the hardcoded type; Kleene is stated in the one direction
the argument uses (see its docstring).

Effort notes (matching the blueprint's `\effortHard` on this section): the s-m-n lemmas
are elementary. The two universal-machine theorems are the hard core — a self-interpreter
of `Prog` written in `Prog` with polynomial overhead (`Cost/Interpreter.lean`,
`Cost/MachineBound.lean`, `Cost/Universal.lean`); this is the same kind of artifact as the
interpreter underlying the succinct Cook–Levin gateway (`thm:succinct-sat`), and the two
developments should share design.
-/

namespace MIPRE.Cost

open Polynomial

/-! ## The efficient s-m-n (blueprint `lem:smn`; [MNY, Lemma 2.2]) -/

/-- The s-m-n transformation: `hardcode p d` runs `p` on the pair `(d, input)`. -/
def hardcode (p : Prog) (d : Data) : Prog := .let_ (.cons (.const d) (.var 0)) p

/-- The program computing the s-m-n map on descriptions: from `(toData p, encode a)` it
assembles `toData (hardcode p (encode a))` — a fixed-shape tree around the two inputs. -/
def smnProg : Prog :=
  .elim 0 .nil (.cons (.const (.ofNat 4)) (.cons (.cons (.const (.ofNat 2))
    (.cons (.cons (.const (.ofNat 6)) (.var 1)) (.const (.cons .nil .nil)))) (.var 0)))

theorem smnProg_wellScoped : smnProg.WellScoped 1 := by simp [smnProg, Prog.WellScoped]

theorem smnProg_runs (x d : Data) :
    smnProg.Runs (.cons x d) (.cons (.ofNat 4) (.cons (.cons (.ofNat 2)
      (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) x)) (x.size + d.size + 38) := by
  have h := Eval.elim_cons (env := [Data.cons x d]) (i := 0) (n := .nil) (by simp)
    (Eval.cons (Eval.const _ (.ofNat 4)) (Eval.cons (Eval.cons (Eval.const _ (.ofNat 2))
      (Eval.cons (Eval.cons (Eval.const _ (.ofNat 6))
        (Eval.var_of_get (env := [x, d, Data.cons x d]) (i := 1) (v := d) (by simp)))
        (Eval.const _ (.cons .nil .nil))))
      (Eval.var_of_get (env := [x, d, Data.cons x d]) (i := 0) (v := x) (by simp))))
  exact h.cast_cost (by simp only [Data.size_ofNat, Data.size_cons, Data.size_nil]; omega)

/-- The s-m-n map as a polynomial-time function: `(p, a) ↦ hardcode p (encode a)`, computed
by `smnProg` in linear time. -/
noncomputable def PolyTimeFun.smn (α : Type*) [SizedEncoding α] :
    PolyTimeFun (Prog × α) Prog where
  toFun pa := hardcode pa.1 (encode pa.2)
  code := smnProg
  closed := smnProg_wellScoped
  timeBound := X + C 38
  computes := by
    rintro ⟨p, a⟩
    refine ⟨esize p + esize a + 38, ?_, smnProg_runs p.toData (encode a)⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
    omega

@[simp] theorem PolyTimeFun.smn_apply (α : Type*) [SizedEncoding α] (p : Prog) (a : α) :
    PolyTimeFun.smn α (p, a) = hardcode p (encode a) := rfl

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1])

The two universal machines are *structures*: the program and its overhead polynomial are
fields, so that downstream definitions (deciders simulating other deciders under a budget;
the λ-bookkeeping of [JNVWY, §12.2], which chooses λ above the concrete overhead
polynomials) can refer to them as data. Their existence is proved in `Cost/Universal.lean`
(`selfUniversal`, `selfClockedUniversal`). -/

/-- **Efficient universal machine.** A fixed closed program `univ` simulating any `c` on
any `v` — with the same halting behavior and result — at polynomial time overhead in
`esize c + v.size + runtime`. Its input is the pair `(encode c, v)`. -/
structure UniversalMachine where
  /-- The universal program. -/
  univ : Prog
  /-- It is closed. -/
  closed : univ.WellScoped 1
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- A run of `c` yields a run of the simulation, with the same result, at polynomial
  overhead. -/
  time_le : ∀ (c : Prog) (v r : Data) (t : ℕ), c.Runs v r t →
    ∃ t' ≤ bound.eval (esize c + v.size + t), univ.Runs (.cons (encode c) v) r t'
  /-- The simulation halts only if the simulated program does, with the same result. -/
  halts_of : ∀ (c : Prog) (v r : Data) (t' : ℕ), univ.Runs (.cons (encode c) v) r t' →
    ∃ t, c.Runs v r t

/-! `exists_efficient_universal : Nonempty UniversalMachine` (blueprint `lem:universal-tm`)
is proved in `Cost/Universal.lean` by the self-interpreter. -/

open Classical in
/-- The result of running `c` on `v` for at most `k` cost, if it halts within the budget
(well-defined by `Eval.deterministic`). -/
noncomputable def evalWithin (c : Prog) (v : Data) (k : ℕ) : Option Data :=
  if h : ∃ r t, t ≤ k ∧ c.Runs v r t then some h.choose else none

/-- The value a clocked simulation returns: `cons (cons nil nil) r` ("halted, with result
`r`") on in-budget halting, and `nil` ("timeout") on budget exhaustion. -/
noncomputable def clockedResult (c : Prog) (v : Data) (k : ℕ) : Data :=
  match evalWithin c v k with
  | some r => .cons (.cons .nil .nil) r
  | none => .nil

/-- **Clocked universal machine**: total simulation under a step budget `k` (supplied in
unary), returning `clockedResult c v k` in time polynomial in the budget, the program size
and the input size. Its input is `(ofNat k, (encode c, v))`. This is the primitive with which
deciders of the pipeline run other deciders, and with which the recursive compression
argument runs "`e` for `log n` steps". -/
structure ClockedUniversalMachine where
  /-- The clocked universal program. -/
  univT : Prog
  /-- It is closed. -/
  closed : univT.WellScoped 1
  /-- The overhead polynomial. -/
  bound : Polynomial ℕ
  /-- Total, budget-bounded simulation. -/
  run : ∀ (c : Prog) (v : Data) (k : ℕ),
    ∃ t ≤ bound.eval (k + esize c + v.size),
      univT.Runs (.cons (.ofNat k) (.cons (encode c) v)) (clockedResult c v k) t

/-! `exists_clocked_universal : Nonempty ClockedUniversalMachine` (blueprint
`lem:universal-tm`) is proved in `Cost/Universal.lean` by the clocked self-interpreter. -/

/-! ## Efficient Kleene recursion

`efficient_fixed_point` (blueprint `lem:kleene`; [MNY, Lemma 2.3]) is proved in
`Cost/Kleene.lean` from `hardcode`, `smnProg` and a `UniversalMachine`. -/

end MIPRE.Cost


