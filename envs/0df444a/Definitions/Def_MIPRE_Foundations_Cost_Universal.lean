-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Universal
-- name    : MIPRE_Foundations_Cost_Universal
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:23:20.98519+00:00
-- url     : https://prove2.me/theorems/b67ef2cb-1eea-4453-9062-1885219b0d9e
-- title:
--   The self-interpreter II: the universal program and its clocked variant, with explicit polynomial bounds
-- statement:
--   This bundle builds the two universal machines of the toolkit from the step program `stepProg`: a fixed program of the ambient model that simulates any program with polynomial overhead, and a clocked variant that simulates under a cost budget. It discharges the existence statements of blueprint `lem:universal-tm`.
--
--   **The universal program.** `MIPRE.Cost.Machine.isFinalProg` tests, on the encoding of a configuration, whether it is final, returning $\mathtt{cons}(\mathtt{nil}, r)$ with its value $r$ if so and $\mathtt{nil}$ otherwise. `MIPRE.Cost.Machine.interpBody` is the body of the interpreter loop: stop with the value of a final configuration, otherwise continue with the next configuration computed by `stepProg`; `MIPRE.Cost.Machine.interpBodyBound` $S = \mathrm{stepBound}(S) + 3S + 30$ bounds one iteration on a configuration of size at most $S$. `MIPRE.Cost.Machine.univPrelude` builds, from the pair $\mathtt{cons}(c, v)$, the initial configuration of $c$ on $v$ as data, and `MIPRE.Cost.Machine.univProg` $= \mathtt{let}\ \mathrm{univPrelude}\ (\mathtt{loop}\ \mathrm{interpBody})$ is the universal program: on $\mathtt{cons}(\mathrm{encode}\ c, v)$ it runs the evaluation machine from the initial configuration until a final one and returns its value. `MIPRE.Cost.Machine.sigmaFun` $X = \mathrm{cfgSizeBound}(X, 3X, X, 2X)$ bounds the size of every configuration of a halting run in terms of $X = \mathrm{esize}(c) + \mathrm{size}(v) + t$, where $t$ is the cost of the simulated run, and `MIPRE.Cost.Machine.univBoundFun` is the time bound of the universal program,
--   $$\mathrm{univBoundFun}(X) = (3X + 1)\,\bigl(\mathrm{interpBodyBound}(\sigma(X)) + 1\bigr) + 2X + 11,$$
--   a run of cost $t$ taking at most $3t$ machine steps.
--
--   **Unary arithmetic for the clock.** `MIPRE.Cost.Machine.subBody` and `MIPRE.Cost.Machine.subProg` compute unary subtraction with comparison: on $\mathtt{cons}(\mathrm{ofNat}\ a, \mathrm{ofNat}\ b)$ the result is `MIPRE.Cost.Machine.subResult` $a\ b$, the flagged difference $\mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), \mathrm{ofNat}(b - a))$ if $a \le b$ and $\mathtt{nil}$ if $b < a$, within `MIPRE.Cost.Machine.subBound` $a\ b = (a + 1)(2a + 2b + 14)$. `MIPRE.Cost.Machine.tripleBody` and `MIPRE.Cost.Machine.tripleProg` compute $(n, m) \mapsto 3n + m$ on unary numerals, within `MIPRE.Cost.Machine.tripleBound` $n\ m = (n + 1)(8n + 2m + 30)$. `MIPRE.Cost.Machine.repBody` and `MIPRE.Cost.Machine.repProg` compute, from $\mathtt{cons}(\mathrm{ofNat}\ n, \mathtt{cons}(d, \mathit{acc}))$, the list of $n$ copies of $d$ prepended to $\mathit{acc}$, within `MIPRE.Cost.Machine.repBound` $n\ d\ a = (n + 1)(4n + 4d + 2a + 30) + n(n + 1)(d + 1)$ for a value of size $d$ and an accumulator of size $a$. `MIPRE.Cost.Machine.addBound` $a\ b = (a + 1)(4a + 2b + 15)$ restates the bound of the unary addition program.
--
--   **The cost of a step, as a program.** `MIPRE.Cost.Machine.costVar` computes the cost $\mathrm{size}(\text{value}) + 1$ of a $\mathtt{var}$ step (looking the variable up with `getListProg` and measuring it with `sizeProg`) and `MIPRE.Cost.Machine.costConst` the cost $\mathrm{size}(d)$ of a $\mathtt{const}$ step; `MIPRE.Cost.Machine.costCases` lists the cost programs of the seven "evaluate" cases (unit cost for $\mathtt{nil}$, $\mathtt{cons}$, $\mathtt{elim}$ and $\mathtt{let}$, zero for $\mathtt{loop}$); `MIPRE.Cost.Machine.stepCostEv` and `MIPRE.Cost.Machine.stepCostRet` compute the cost of an "evaluate" and of a "return" step (one unit at a $\mathtt{loop1}$ frame, zero otherwise); and `MIPRE.Cost.Machine.stepCostProg` combines them: on the encoding of a configuration $c$ it returns $\mathrm{ofNat}(\mathrm{stepCost}\ c)$, within `MIPRE.Cost.Machine.stepCostBound` $S = (S + 1)(7S + 32) + 13S + 50$.
--
--   **The clocked loop.** `MIPRE.Cost.Machine.clockState` $d\ \mathit{rem}\ \mathit{budget}\ \theta = \mathtt{cons}(d, \mathtt{cons}(\mathit{rem}, \mathtt{cons}(\mathit{budget}, \theta)))$ is the loop state: the configuration, the remaining cost budget, the remaining step budget and the size guard, the last three in unary. `MIPRE.Cost.Machine.clockRest` is the second half of an iteration, after the cost of the step has been subtracted successfully from the cost budget: perform the step, measure the new configuration with `sizeProg`, and stop with the timeout value $\mathtt{nil}$ if it exceeds the guard, otherwise continue. `MIPRE.Cost.Machine.clockStep` is the iteration on a non-final configuration: stop with $\mathtt{nil}$ if the step budget is exhausted or the cost of the step exceeds the remaining cost budget, otherwise `clockRest`. `MIPRE.Cost.Machine.clockBody` is the loop body: on a final configuration stop with the flagged value $\mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), r)$, otherwise `clockStep`. The bounds `MIPRE.Cost.Machine.sizeBound` $s = (s + 1)(5s + 20) + s + 6$ (the cost of `sizeProg` on a value of size $s$), `MIPRE.Cost.Machine.clockRestBound` $S\ \Theta\ \mathit{rem}\ b$ and `MIPRE.Cost.Machine.clockBodyBound` $\Theta\ k$ bound one iteration in terms of the configuration size $S \le \Theta$, the guard $\Theta$, the remaining cost $\mathit{rem} \le k$ and the step budget $b \le 3k + 1$; `MIPRE.Cost.Machine.clockEnv` $c\ \mathit{rem}\ b\ \Theta\ \mathit{env}$ records the exact environment of `clockStep` after the cost subtraction, for the correctness proof.
--
--   **Semantics of the clocked loop.** `MIPRE.Cost.Machine.Cfg.val` is the value of a configuration (the returned value, and $\mathtt{nil}$ on an "evaluate" control), and `MIPRE.Cost.Machine.clockRun` $c_0\ k\ \Theta\ b\ n$ is the mathematical specification of the loop's result from the $n$-th configuration of the run of $c_0$, with step budget $b$, cost budget $k$ and size guard $\Theta$: the flagged value if that configuration is final; otherwise, if steps remain, the accumulated cost of $n + 1$ steps is at most $k$ and the next configuration has encoded size at most $\Theta$, the result from the next configuration with one step fewer; and the timeout value $\mathtt{nil}$ in every other case.
--
--   **The clocked universal program.** The size guard is computed in unary from $X = k + \mathrm{esize}(c) + \mathrm{size}(v)$: `MIPRE.Cost.Machine.guardFun` $X = 3(3X + 1) + 1 = 9X + 4$ (two applications of `tripleProg`), then `MIPRE.Cost.Machine.t1Fun` $X = Y(2Y + 2) + 1$ with $Y = \mathrm{guardFun}(X)$ (the size of $Y$ copies of $\mathrm{ofNat}\ Y$), and `MIPRE.Cost.Machine.thetaFun` $X = Y\,(\mathrm{t1Fun}(X) + 1) + 1$ (the size of $Y$ copies of that list): the guard $\Theta$, a polynomial in $X$ dominating the configuration sizes of every run of cost at most $k$. `MIPRE.Cost.Machine.univTProg` is the clocked universal program: on $\mathtt{cons}(\mathrm{ofNat}\ k, \mathtt{cons}(\mathrm{encode}\ c, v))$ it computes $X$ and $\Theta$ in unary (with `sizeProg`, `addProg`, `tripleProg` and `repProg`), builds the initial configuration and the loop state with cost budget $k$ and step budget $3k + 1$, and runs the clocked loop, returning $\mathrm{clockedResult}\ c\ v\ k$. `MIPRE.Cost.Machine.univTBoundFun` $X$ is its explicit time bound: the costs of the prelude plus $3X + 2$ iterations each bounded by $\mathrm{clockBodyBound}(\Theta(X), X)$.
--
--   **Polynomial packaging.** The bounds above are functions $\mathbb{N} \to \mathbb{N}$, while the structures `UniversalMachine` and `ClockedUniversalMachine` require polynomials. `MIPRE.Cost.Machine.stepPoly`, `MIPRE.Cost.Machine.interpBodyPoly`, `MIPRE.Cost.Machine.sigmaPoly` and `MIPRE.Cost.Machine.univPoly` are the polynomials in $\mathbb{N}[X]$ whose evaluations are `stepBound`, `interpBodyBound`, `sigmaFun` and `univBoundFun`; `MIPRE.Cost.Machine.sizePoly`, `MIPRE.Cost.Machine.addPoly`, `MIPRE.Cost.Machine.triplePoly`, `MIPRE.Cost.Machine.repPoly`, `MIPRE.Cost.Machine.subPoly`, `MIPRE.Cost.Machine.stepCostPoly` and `MIPRE.Cost.Machine.clockBodyPoly` are the polynomial versions of the corresponding bounds, taking polynomials as arguments; and `MIPRE.Cost.Machine.guardPoly`, `MIPRE.Cost.Machine.t1Poly`, `MIPRE.Cost.Machine.thetaPoly` and `MIPRE.Cost.Machine.univTPoly` are the polynomials evaluating to `guardFun`, `t1Fun`, `thetaFun` and `univTBoundFun`.
--
--   No lemma is proved inside this bundle; the theorems that `univProg` and `univTProg` are correct within these bounds (`univTProg_runs`, `halts_iff`, and the packaged machines `selfUniversal` and `selfClockedUniversal`, which give `exists_efficient_universal` and `exists_clocked_universal`) are uploaded separately.
--
--   **Formalization Note**. A halting run of cost $t$ takes at most $3t$ machine steps, each on a configuration of size at most $\sigma(\mathrm{esize}(c) + \mathrm{size}(v) + t)$, which gives the polynomial overhead of the universal program; conversely, any run of the interpreter loop is a machine run reaching a final configuration, hence a derivation with the same result. In the clocked variant the step budget $3k + 1$ guarantees termination; the cost budget, decremented by the *exact* cost of each step (`stepCostProg` matches `stepCost`), decides whether the simulated run halts within cost $k$; and the size guard $\Theta$ keeps every configuration handled by the loop polynomially bounded even when the simulated run does not halt, while never firing on a run that halts within the budget, whose configurations are bounded by $\Theta$. All budgets are in unary, because a loop can only count down by structural recursion, and every bound is stated both as a function (for the proofs, by `omega` and `nlinarith`) and as a polynomial (for the structures of the toolkit).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean; blueprint lem:universal-tm; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound

/-!
# The self-interpreter, II: the universal machines

The two universal machines of the toolkit (`Cost/Toolkit.lean`), built from the step
program `stepProg` of `Cost/Interpreter.lean`:

* `univProg` runs the evaluation machine (`Cost/Machine.lean`) from the initial
  configuration of `c` on `v` until a final configuration, as a `loop` whose body tests
  finality (`isFinalProg`) and otherwise steps. A halting run of cost `t` takes at most
  `3 t` machine steps (`eval_steps_count`), each on a configuration of size polynomial in
  `esize c + v.size + t` (`eval_steps_bound_forever`, `size_toData_le`), which gives the
  polynomial overhead (`UniversalMachine.time_le`); conversely a run of the loop is a
  machine run reaching a final configuration, hence a derivation (`halts_iff`).
* `univTProg` is the clocked variant: the loop additionally carries the remaining cost
  budget and a step budget `3 k + 1`, both in unary, and a size guard `Θ` (a polynomial in
  `k + esize c + v.size` computed in unary). The step budget makes the loop terminate; the
  cost budget, decremented by the exact cost of each step (`stepCostProg`, matching
  `stepCost`), decides whether the simulated run halts within cost `k`; the size guard keeps
  the configurations handled by the loop polynomially bounded even when the simulated run
  does not halt — it never fires on a run that halts within the budget, whose
  configurations are bounded by `Θ`.

This discharges `exists_efficient_universal` and `exists_clocked_universal` (blueprint
`lem:universal-tm`).
-/

namespace MIPRE.Cost

open Polynomial

namespace Machine

open Prog

/-! ## The final-configuration test -/

/-- On the encoding of a configuration: `cons nil r` if it is final with value `r`, `nil`
otherwise. -/
def isFinalProg : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 5 .nil (.elim 1 (.cons .nil (.var 5)) .nil))))

/-! ## The interpreter loop -/

/-- Body of the interpreter loop: on a configuration, stop with its value if it is final,
otherwise continue with the next configuration. -/
def interpBody : Prog :=
  .let_ (callVar 0 isFinalProg)
    (.elim 0 (.cons (.cons .nil .nil) (callVar 1 stepProg)) (.cons .nil (.var 1)))

/-- Cost of one iteration of the interpreter loop on a configuration of size at most `S`. -/
def interpBodyBound (S : ℕ) : ℕ := stepBound S + 3 * S + 30

/-! ## The universal program -/

/-- On `cons c v`: the initial configuration of `c` on `v`, as data. -/
def univPrelude : Prog :=
  .elim 0 .nil (.cons (.cons .nil (.var 0)) (.cons (.cons (.var 1) .nil) .nil))

/-- The universal program: on `cons (encode c) v`, build the initial configuration of `c`
on `v` and run the interpreter loop. -/
def univProg : Prog := .let_ univPrelude (.loop interpBody)

/-- The size bound on the configurations of a halting run, in terms of
`X = esize c + v.size + t`. -/
def sigmaFun (X : ℕ) : ℕ := cfgSizeBound X (3 * X) X (2 * X)

/-- The time bound of the universal program, in terms of `X = esize c + v.size + t`. -/
def univBoundFun (X : ℕ) : ℕ := (3 * X + 1) * (interpBodyBound (sigmaFun X) + 1) + 2 * X + 11

/-! ## Unary arithmetic for the clock -/

/-- Loop body of `subProg`: on `cons a b` (unary), stop with the flagged difference
`cons (cons nil nil) (b - a)` if `a ≤ b`, with `nil` otherwise. -/
def subBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.cons (.cons .nil .nil) (.var 1)))
    (.elim 3 (.cons .nil .nil) (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1)))))

/-- Unary subtraction with comparison: `subProg` on `cons (ofNat a) (ofNat b)` computes
`subResult a b`. -/
def subProg : Prog := .loop subBody

/-- The value of `subProg`: the flagged difference, or `nil` when `b < a`. -/
def subResult (a b : ℕ) : Data :=
  if a ≤ b then .cons (.cons .nil .nil) (.ofNat (b - a)) else .nil

/-- Cost bound of `subProg` on `cons (ofNat a) (ofNat b)`. -/
def subBound (a b : ℕ) : ℕ := (a + 1) * (2 * a + 2 * b + 14)

/-- Loop body of `tripleProg`: on `cons (ofNat n) (ofNat m)`, `ofNat (3 n + m)`. -/
def tripleBody : Prog :=
  .elim 0 .nil (.elim 0 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil)
      (.cons (.var 1) (.cons .nil (.cons .nil (.cons .nil (.var 3)))))))

/-- `tripleProg` on `cons (ofNat n) (ofNat m)` computes `ofNat (3 n + m)`. -/
def tripleProg : Prog := .loop tripleBody

/-- Loop body of `repProg`: on `cons (ofNat n) (cons d acc)`, `n` copies of `d` consed
onto `acc`. -/
def repBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 2 (.cons .nil (.var 1))
    (.cons (.cons .nil .nil) (.cons (.var 1) (.cons (.var 2) (.cons (.var 2) (.var 3)))))))

/-- `repProg` on `cons (ofNat n) (cons d (list acc))` computes `list (replicate n d ++ acc)`. -/
def repProg : Prog := .loop repBody

/-- Cost bound of `repProg` for `n` copies of a value of size `d` onto an accumulator of
size `a`. -/
def repBound (n d a : ℕ) : ℕ := (n + 1) * (4 * n + 4 * d + 2 * a + 30) + n * (n + 1) * (d + 1)

/-! ## The cost of a step, as a program -/

/-- Cost of a `var` step: `cons body env ↦ ofNat ((getList env body).size + 1)`. -/
def costVar : Prog :=
  .elim 0 .nil (.let_ (.cons (.var 1) (.var 0)) (.let_ (callVar 0 getListProg)
    (.let_ (callVar 0 sizeProg) (.cons .nil (.var 0)))))

/-- Cost of a `const` step: `cons d env ↦ ofNat d.size`. -/
def costConst : Prog := .elim 0 .nil (callVar 0 sizeProg)

/-- The case programs of the cost of an "evaluate" step, indexed by the tag. -/
def costCases : List Prog :=
  [costVar, .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .const (.ofNat 1), .nil,
    costConst]

/-- The cost of an "evaluate" step; environment `[tag, payload, ctrl, rest, d]`. -/
def stepCostEv : Prog :=
  .elim 1 .nil (.let_ (.cons (.var 1) (projLeft 5)) (dispatch costCases 1 0))

/-- The cost of a "return" step: `1` at a `loop1` frame, `0` otherwise; environment
`[t₁, t₂, tag, payload, ctrl, rest, d]`. -/
def stepCostRet : Prog :=
  .elim 5 .nil (.elim 1 .nil (.elim 0 .nil (.elim 0 .nil (.elim 1 .nil
    (.elim 1 .nil (.const (.ofNat 1)))))))

/-- On the encoding of a configuration `c`: `ofNat (stepCost c)`. -/
def stepCostProg : Prog := .elim 0 .nil (.elim 0 .nil (.elim 0 stepCostEv stepCostRet))

/-- Cost bound of `stepCostProg` on a configuration of size `S`. -/
def stepCostBound (S : ℕ) : ℕ := (S + 1) * (7 * S + 32) + 13 * S + 50

/-! ## The clocked interpreter loop -/

/-- The state of the clocked loop: the configuration, the remaining cost budget, the
remaining step budget and the size guard (the last three in unary). -/
def clockState (d rem budget theta : Data) : Data := .cons d (.cons rem (.cons budget theta))

/-- Second half of a step of the clocked loop, after the cost subtraction succeeded:
step, then check the size of the new configuration against the guard; environment
`[cons nil nil, rem', sub, cr, nil, budget', nil, budget, theta, rem, r₂, d, r₁, s]`. -/
def clockRest : Prog :=
  .let_ (callVar 11 stepProg)
    (.let_ (.let_ (callVar 0 sizeProg) (.cons (.var 0) (.var 10)))
      (.let_ (callVar 0 subProg)
        (.elim 0 (.cons .nil .nil)
          (.cons (.cons .nil .nil)
            (.cons (.var 4) (.cons (.var 6) (.cons (.var 10) (.var 13))))))))

/-- The step of the clocked loop on a non-final configuration; environment
`[flag, budget, theta, rem, r₂, d, r₁, s]` with `flag = nil`: stop with `nil` if the step
budget is exhausted or the cost of the step exceeds the remaining cost budget, else
`clockRest`. -/
def clockStep : Prog :=
  .elim 1 (.cons .nil .nil)
    (.let_ (.cons (callVar 7 stepCostProg) (.var 5))
      (.let_ (callVar 0 subProg) (.elim 0 (.cons .nil .nil) clockRest)))

/-- Body of the clocked loop: stop with the flagged value of a final configuration,
otherwise `clockStep`. -/
def clockBody : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.let_ (callVar 4 isFinalProg)
    (.elim 0 clockStep (.cons .nil (.cons (.cons .nil .nil) (.var 1)))))))

/-- Cost bound of `sizeProg` on a value of size `s` (as in `sizeProg_runs`). -/
def sizeBound (s : ℕ) : ℕ := (s + 1) * (5 * s + 20) + s + 6

/-- Bound on the second half of a step of the clocked loop, in terms of the configuration
size `S`, the guard `Θ`, the remaining cost `rem` and the step budget `b`. -/
def clockRestBound (S Θ rem b : ℕ) : ℕ :=
  S + stepBound S + sizeBound (stepBound S) + subBound (stepBound S) Θ + 6 * stepBound S +
    6 * Θ + 2 * rem + 2 * b + 50

/-- Bound of one iteration of the clocked loop, on configurations of size at most `Θ`,
with cost budget at most `k` (and step budget at most `3 k + 1`). -/
def clockBodyBound (Θ k : ℕ) : ℕ :=
  stepCostBound Θ + subBound Θ k + stepBound Θ + sizeBound (stepBound Θ) +
    subBound (stepBound Θ) Θ + 6 * stepBound Θ + 12 * Θ + 30 * k + 200

/-- The environment of `clockStep` after the cost subtraction, on a configuration `c` with
remaining cost `rem`, step budget `b + 1` and guard `Θ`. -/
def clockEnv (c : Cfg) (rem b Θ : ℕ) (env : Env) : Env :=
  subResult (stepCost c) rem :: .cons (.ofNat (stepCost c)) (.ofNat rem) :: .nil :: .ofNat b ::
    .nil :: .ofNat (b + 1) :: .ofNat Θ :: .ofNat rem :: .cons (.ofNat (b + 1)) (.ofNat Θ) ::
    c.toData :: .cons (.ofNat rem) (.cons (.ofNat (b + 1)) (.ofNat Θ)) ::
    clockState c.toData (.ofNat rem) (.ofNat (b + 1)) (.ofNat Θ) :: env

/-! ## The semantics of the clocked loop -/

/-- The value of a configuration: the returned value, `nil` on an "evaluate" control. -/
def Cfg.val : Cfg → Data
  | ⟨.ret v, _, _⟩ => v
  | ⟨.ev _, _, _⟩ => .nil

open Classical in
/-- The result of the clocked loop from the `n`-th configuration of the run of `c₀`, with
step budget `b`, cost budget `k` and size guard `Θ`. -/
noncomputable def clockRun (c₀ : Cfg) (k Θ : ℕ) : ℕ → ℕ → Data
  | 0, n => if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val else .nil
  | b + 1, n =>
    if IsFinal (step^[n] c₀) then .cons (.cons .nil .nil) (step^[n] c₀).val
    else if costSum c₀ (n + 1) ≤ k ∧ (step^[n + 1] c₀).toData.size ≤ Θ then
      clockRun c₀ k Θ b (n + 1)
    else .nil

/-! ## The clocked universal program -/

/-- The size guard of the clocked simulation, as a function of `X = k + esize c + v.size`:
`Y = 9 X + 4` (two applications of `tripleProg`)... -/
def guardFun (X : ℕ) : ℕ := 3 * (3 * X + 1) + 1

/-- ...the size of `Y` copies of `ofNat Y`... -/
def t1Fun (X : ℕ) : ℕ := guardFun X * (2 * guardFun X + 1 + 1) + 1

/-- ...and the size of `Y` copies of that list: the guard `Θ`. -/
def thetaFun (X : ℕ) : ℕ := guardFun X * (t1Fun X + 1) + 1

/-- The clocked universal program: on `cons (ofNat k) (cons (encode c) v)`, compute
`X = k + esize c + v.size` and the guard `Θ` in unary, build the initial configuration and
the state of the clocked loop, and run it with step budget `3 k + 1`. -/
def univTProg : Prog :=
  .elim 0 .nil (.elim 1 .nil
    (.let_ (callVar 0 sizeProg)
    (.let_ (callVar 2 sizeProg)
    (.let_ (.cons (.var 0) (.var 1))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 6) (.var 0))
    (.let_ (callVar 0 addProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 0) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (.cons (.var 2) (.cons (.var 0) .nil))
    (.let_ (callVar 0 repProg)
    (.let_ (callVar 0 sizeProg)
    (.let_ (.cons (.cons .nil (.var 15)) (.cons (.cons (.var 16) .nil) .nil))
    (.let_ (.cons (.var 18) (.cons .nil .nil))
    (.let_ (callVar 0 tripleProg)
    (.let_ (.cons (.var 2) (.cons (.var 20) (.cons (.var 0) (.var 3))))
      (.loop clockBody)))))))))))))))))))))

/-- Cost bound of `addProg` (as in `addProg_runs`). -/
def addBound (a b : ℕ) : ℕ := (a + 1) * (4 * a + 2 * b + 15)

/-- Cost bound of `tripleProg` (as in `tripleProg_runs`). -/
def tripleBound (n m : ℕ) : ℕ := (n + 1) * (8 * n + 2 * m + 30)

/-- The time bound of the clocked universal program, as a function of
`X = k + esize c + v.size`. -/
def univTBoundFun (X : ℕ) : ℕ :=
  2 * sizeBound X + addBound X X + addBound X X + tripleBound X 1 + tripleBound (3 * X + 1) 1 +
    tripleBound X 1 + repBound (guardFun X) (2 * guardFun X + 1) 1 +
    repBound (guardFun X) (t1Fun X) 1 + sizeBound (thetaFun X) +
    (3 * X + 2) * (clockBodyBound (thetaFun X) X + 1) +
    20 * thetaFun X + 20 * t1Fun X + 60 * guardFun X + 100 * X + 500

/-! ## Polynomial packaging -/

/-- `stepBound` as a polynomial. -/
noncomputable def stepPoly : Polynomial ℕ := (X + C 1) * (X + C 40) + C 200

/-- `interpBodyBound` as a polynomial. -/
noncomputable def interpBodyPoly : Polynomial ℕ := stepPoly + C 3 * X + C 30

/-- `sigmaFun` as a polynomial. -/
noncomputable def sigmaPoly : Polynomial ℕ :=
  X + X + (C 3 * X) * X + C 3 * X + (C 2 * X) * (X + X + (C 3 * X) * X + C 3 * X + C 10) +
    C 2 * X + C 8

/-- `univBoundFun` as a polynomial. -/
noncomputable def univPoly : Polynomial ℕ :=
  (C 3 * X + C 1) * (interpBodyPoly.comp sigmaPoly + C 1) + C 2 * X + C 11

/-- `sizeBound` of a polynomial. -/
noncomputable def sizePoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 5 * p + C 20) + p + C 6

/-- `addBound` of polynomials. -/
noncomputable def addPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 2 * q + C 15)

/-- `tripleBound` of polynomials. -/
noncomputable def triplePoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 8 * p + C 2 * q + C 30)

/-- `repBound` of polynomials. -/
noncomputable def repPoly (p q r : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 4 * p + C 4 * q + C 2 * r + C 30) + p * (p + C 1) * (q + C 1)

/-- `subBound` of polynomials. -/
noncomputable def subPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 2 * p + C 2 * q + C 14)

/-- `stepCostBound` of a polynomial. -/
noncomputable def stepCostPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  (p + C 1) * (C 7 * p + C 32) + C 13 * p + C 50

/-- `clockBodyBound` of polynomials. -/
noncomputable def clockBodyPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  stepCostPoly p + subPoly p q + stepPoly.comp p + sizePoly (stepPoly.comp p) +
    subPoly (stepPoly.comp p) p + C 6 * stepPoly.comp p + C 12 * p + C 30 * q + C 200

/-- `guardFun`, `t1Fun`, `thetaFun` as polynomials. -/
noncomputable def guardPoly : Polynomial ℕ := C 3 * (C 3 * X + C 1) + C 1

noncomputable def t1Poly : Polynomial ℕ := guardPoly * (C 2 * guardPoly + C 1 + C 1) + C 1

noncomputable def thetaPoly : Polynomial ℕ := guardPoly * (t1Poly + C 1) + C 1

/-- `univTBoundFun` as a polynomial. -/
noncomputable def univTPoly : Polynomial ℕ :=
  C 2 * sizePoly X + addPoly X X + addPoly X X + triplePoly X (C 1) +
    triplePoly (C 3 * X + C 1) (C 1) + triplePoly X (C 1) +
    repPoly guardPoly (C 2 * guardPoly + C 1) (C 1) + repPoly guardPoly t1Poly (C 1) +
    sizePoly thetaPoly + (C 3 * X + C 2) * (clockBodyPoly thetaPoly X + C 1) +
    C 20 * thetaPoly + C 20 * t1Poly + C 60 * guardPoly + C 100 * X + C 500

end Machine

end MIPRE.Cost


