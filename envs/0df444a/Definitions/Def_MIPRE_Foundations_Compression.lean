-- Prove2me | Definitions.Def_MIPRE_Foundations_Compression
-- name    : MIPRE_Foundations_Compression
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:25:55.780543+00:00
-- url     : https://prove2.me/theorems/c503a8e4-f9fb-4e7d-8948-b6346c851c84
-- title:
--   The self-referential deciders and recursion levels of the abstract compression lemmas
-- statement:
--   This bundle defines the self-referential deciders at the heart of the two abstract compression lemmas: the recursive compression lemma of Marks–Nezhadi–Yuen (blueprint `lem:recursive-compression`, [MNY, Lemma 5.1]) and Lin's compressibility criterion (blueprint `lem:compressible-criterion`).
--
--   `MIPRE.Cost.decFun` $U\ UT\ \mathrm{Compr}\ y_0$ is the decider of the recursive compression argument, a polynomial-time function $\mathrm{Prog} \times (\mathrm{Prog} \times \mathbb{N}) \to \{0,1\}^*$, given a universal machine $U$, a clocked universal machine $UT$, a polynomial-time compression procedure $\mathrm{Compr} : (\mathrm{Prog} \times \mathbb{N}) \times \mathbb{N} \to \{0,1\}^*$ (a succinct description and a parameter) and a fixed string $y_0$: on $(c', (e, n))$,
--   $$\mathrm{decFun}(c', (e, n)) = \begin{cases} y_0 & \text{if } e \text{ halts on the empty input within cost } |n|,\\ \mathrm{Compr}\bigl((s(\beta, ((c', e), 2n + 1)),\ n),\ n\bigr) & \text{otherwise,}\end{cases}$$
--   where $\beta = \mathrm{bitQueryProg}\ U.\mathrm{univ}$ is the bit-query program and $s(\beta, d) = \mathrm{hardcode}\ \beta\ (\mathrm{encode}\ d)$ the s-m-n map. It is assembled from the combinators `ite`, `haltsWithin`, `const`, `pair`, `fst`, `snd`, `smn` and `next` of the closure library. The self-referential program $c$ of the proof is a Kleene fixed point of $c' \mapsto \mathrm{hardcode}\ (\mathrm{decFun}\ \cdots).\mathrm{code}\ (\mathrm{encode}\ c')$, so that $c$ on $(e, n)$ computes $\mathrm{decFun}(c, (e, n))$, and the hardcoded description is of the string that $c$ itself computes at the next level $2n + 1$.
--
--   `MIPRE.Cost.levels` $R\ k$ are the levels of the recursion started at $R$: $\mathrm{levels}(R, 0) = R$ and $\mathrm{levels}(R, k + 1) = 2\,\mathrm{levels}(R, k) + 1$, that is, $R,\ 2R + 1,\ 4R + 3,\ \dots$
--
--   `MIPRE.Cost.Prog.searchProg` $\mathrm{univ}\ S$ is the program of the *search branch* of the compressibility criterion. On the pair $(d, \mathrm{input})$ with $d = \mathrm{encode}((c', (e, (m, m))), m)$ (the input is ignored) it runs $\mathrm{univ}$ on the first component of $d$, that is, simulates $c'$ on $(e, (m, m))$ to obtain the string at the start level $m$, and then runs the semidecision procedure $S$ on the pair of that string with $m$; hardcoding $d$ into it gives the program whose halting the search branch tests.
--
--   `MIPRE.Cost.decFunV` $U\ UT\ S\ \mathrm{Compr}\ y_{\mathrm{yes}}\ y_{\mathrm{no}}$ is the decider of the compressibility-criterion argument, a polynomial-time function $\mathrm{Prog} \times (\mathrm{Prog} \times (\mathbb{N} \times \mathbb{N})) \to \{0,1\}^*$, now with $\mathrm{Compr} : \mathrm{Prog} \times \mathbb{N} \to \{0,1\}^*$ and a program $S$: on $(c', (e, (m, n)))$ it returns $y_{\mathrm{yes}}$ if $e$ halts on the empty input within cost $|n|$; otherwise $y_{\mathrm{no}}$ if the hardcoded search program $s(\mathrm{searchProg}\ U.\mathrm{univ}\ S,\ ((c', (e, (m, m))), m))$ halts on the empty input within cost $|n|$; and otherwise $\mathrm{Compr}\bigl(s(\beta, ((c', e), (m, 2n + 1))),\ n\bigr)$. As for `decFun`, the self-referential program is a Kleene fixed point of $c' \mapsto \mathrm{hardcode}\ (\mathrm{decFunV}\ \cdots).\mathrm{code}\ (\mathrm{encode}\ c')$.
--
--   The lemmas proved in the bundle are the two recursion equations of `levels`.
--
--   **Formalization Note**. Everything is stated in the ambient cost model: programs are `Prog`, "polynomial-time computable" is `PolyTimeFun`, and the deciders are built from the toolkit alone — `hardcode` and `smn`, a clocked universal machine for "run $e$ for $\log n$ steps", a universal machine inside the bit-query program, and `efficient_fixed_point` to close the self-reference. Departures from the paper, recorded in the module docstring: the succinctness budget is $(n + 1)(|m| + 1)^2$ rather than $n$; the next level is $2n + 1$ rather than $n + 1$ (prepending a bit is one node, incrementing needs a carry propagation); the threshold is the explicit $r(e) = 2^{K + 1 + |e|}$ with $K$ obtained from the overhead polynomial; and the criterion is proved in a per-level form, with the start level $m$ carried as data next to $n$ so that the decider's code does not depend on the threshold, which is chosen afterwards from the decider's time bound. In the instantiation the compressor cannot read the succinct description it is handed (a bit query costs up to $n$, while its own time is polylogarithmic in $n$), so it embeds the description into a decider that reads it at game time, with the verifier it describes frozen at index $2n + 1$. For `recursive_compression` the measure $f$ takes values in $\mathbb{N} \cup \{\infty\}$, matching the entanglement requirement of the pipeline.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean; blueprint lem:recursive-compression, lem:compressible-criterion; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 5.1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
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
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec

/-!
# The abstract compression lemmas

Two abstract compression lemmas, each turning a compression procedure on succinct
descriptions into a reduction from the halting problem, together with their halting-problem
corollaries in the form consumed by `MIPRE.HaltingGameValue`:

* `recursive_compression`: the lemma of Marks–Nezhadi–Yuen ("The recursive compression
  method for proving undecidability results"), in the variant with compression parameter
  `n` ([MNY, Lemma 5.1]) — blueprint `lem:recursive-compression` — whose hypothesis is the
  growth of a measure `f` (the entanglement requirement, in the pipeline of [JNVWY]);
* `compressibility_criterion`: Lin's compression criterion (MIP^co = coRE) — blueprint
  `lem:compressible-criterion` — whose hypothesis is the preservation of two classes, in
  value form, plus the semidecidability of the complement of the second. This is the lemma
  the value-form pipeline of the blueprint uses. The adapted notion of succinct description
(blueprint `def:succinct`, [MNY, Definition 2.4]) is `Cost.IsSuccinctDesc` in
`Cost/Succinct.lean`.

Everything is stated in the ambient cost model (`Cost.Basic`): programs are
`Cost.Prog`, "polynomial-time computable" is `Cost.PolyTimeFun`, runtimes are
`Cost.Eval`. The proof is the fixed-point construction of [MNY, Lemma 3.1/5.1] and uses
precisely the toolkit of `Cost.Toolkit`: `hardcode` (efficient s-m-n) and `PolyTimeFun.smn`
to build the self-referential decider, a `ClockedUniversalMachine` to run "`e` for `log n`
steps" (`PolyTimeFun.haltsWithin`), a `UniversalMachine` to answer bit-queries within the
succinctness budget (`Prog.bitQueryProg`), and `efficient_fixed_point` to close the
self-reference; the time-transfer clauses are what make the constructed program a
*succinct* description at every recursion level (`planning/compression-track.md`, K3).

## Departures from the paper's statement and proof

* **Succinctness time bound.** [MNY, Definition 2.4] requires `runtime(e, m) ≤ n` for
  *all* `m`. In any cost model that charges to read its input (ours does), that bound is
  vacuous for `|m| > n`; we require `≤ (n + 1) * (Nat.size m + 1) ^ 2` instead. Any
  `poly(n, |m|)` bound would do; the choice only shifts polynomial overheads inside the
  proof, but it must be fixed consistently with the compression theorem for games
  (`thm:compression`) whose output verifiers are what get succinctly described. The
  quadratic factor in `|m|` is what the bit-query program `Cost.Prog.bitAtProg` achieves:
  in the list language, a zero test or a decrement of the binary index copies the index,
  so each of the `|y|` steps of the walk costs `O(size y + |m| ^ 2)`
  (`Cost.Prog.bitAtIter_le`). **Design knob (K-D5) — revisit when `thm:compression` is
  stated.**
* **The next level is `2 n + 1`, not `n + 1`.** The paper's decider at level `n` compresses
  a description of the string at level `n + 1`. Incrementing a binary numeral needs a carry
  propagation; prepending a `true` bit is one node (`PolyTimeFun.next`). The argument is
  unchanged: the levels `n, 2n + 1, 4n + 3, …` still grow without bound, and
  `Nat.size (2 n + 1) = Nat.size n + 1` keeps every overhead polynomial in
  `esize e + Nat.size n`.
* **The threshold** is `r e = 2 ^ (K + 1 + esize e)` for a constant `K` obtained from the
  overhead polynomial by `exists_threshold` (`Cost/Growth.lean`): above it, the polynomial
  overhead in `esize e + Nat.size n` is at most `n + 1`. It is computed by
  `PolyTimeFun.threshold K`.
* **The instantiation** (blueprint `rem:compression-abstract`) uses the per-level form
  `compressibility_criterion_levels`: `A n` = descriptions of `n`-bounded normal form
  verifiers whose `n`-th game has a value-`1` PCC strategy, `B n` = those with value at most
  `1/2` at index `n`, and `S` = the enumeration of strategies of value above `1/2`
  (blueprint `lem:value-lower-approx`, `MIPRE.exists_semidecider_lt_quantumValue`) on the
  tabulated `n`-th game. The compressor cannot read the succinct description it is handed —
  a bit query costs up to `n`, its own time is polylogarithmic in `n` — so it embeds the
  description into a decider that reads it at game time, with the verifier it describes
  frozen at index `2n + 1`; that is what the size slack `2 · |c| ≤ n` and the level
  bookkeeping of the per-level form are for. For `recursive_compression`,
  `f = MIPRE.entRequirement (·, 1/2) : _ → ℕ∞`; the `ℕ∞` codomain there matches
  `entRequirement`.
-/

namespace MIPRE.Cost

open Polynomial

/-! ## The self-referential decider -/

/-- The decider of the recursive compression argument, as a polynomial-time function of
`(c', (e, n))`: if `e` halts on the empty input within `Nat.size n` steps, the fixed string
`y₀`; otherwise `Compr` applied to the succinct description `(hardcode β ((c', e), 2n + 1),
n)` — where `β` is the bit-query program — with parameter `n`. The self-referential program
`c` of the proof is a Kleene fixed point of `c' ↦ hardcode (decFun …).code (encode c')`, so
that `c` on `(e, n)` computes `decFun (c, (e, n))`, and the hardcoded description is of
the string that `c` itself computes at the next level. -/
noncomputable def decFun (U : UniversalMachine) (UT : ClockedUniversalMachine)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr) (y₀ : BitStr) :
    PolyTimeFun (Prog × (Prog × ℕ)) BitStr :=
  PolyTimeFun.ite ((PolyTimeFun.haltsWithin UT).comp PolyTimeFun.snd)
    (PolyTimeFun.const y₀)
    (Compr.comp (PolyTimeFun.pair
      (PolyTimeFun.pair
        ((PolyTimeFun.smn ((Prog × Prog) × ℕ)).comp
          (PolyTimeFun.pair (PolyTimeFun.const (Prog.bitQueryProg U.univ))
            (PolyTimeFun.pair
              (PolyTimeFun.pair PolyTimeFun.fst (PolyTimeFun.fst.comp PolyTimeFun.snd))
              (PolyTimeFun.next.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
        (PolyTimeFun.snd.comp PolyTimeFun.snd))
      (PolyTimeFun.snd.comp PolyTimeFun.snd)))

/-! ## The compression lemma -/

/-! ## Lin's compressibility criterion

The value-form abstract lemma (blueprint `lem:compressible-criterion`): Lin's compression
criterion for `RE`-complete problems ([Lin, MIP^co = coRE, "Compression criteria for
RE-complete problems", direction (3) ⇒ (1)]), in the succinct-description formulation of
[MNY]. Compared with `recursive_compression`, the growth hypothesis on a measure `f` is
replaced by a second preserved class `B` whose complement is semidecidable, and the
self-referential decider gains a *search branch*: at level `n` it also runs, for
`Nat.size n` steps, the semidecision procedure on the string at the *start* of the
recursion. The start level `m` is carried as data next to the level `n` (the decider's input
is `(c', (e, (m, n)))`), so that the decider's code does not depend on the threshold, which is
chosen afterwards from the decider's time bound exactly as in `recursive_compression`.

The lemma is proved in a *per-level* form (`compressibility_criterion_levels`): the classes
`A n`, `B n` are indexed by the level, the semidecider runs on `(x, n)`, and the compression
hypothesis is only required of short descriptions with parameter the level, transferring the
class at level `2n + 1` to the class at level `n` — precisely what the proof uses. The
level-free statement (`compressibility_criterion`) is its special case. -/

/-- The levels of the recursion started at `R`: `R, 2R + 1, 4R + 3, …`. -/
def levels (R : ℕ) : ℕ → ℕ
  | 0 => R
  | k + 1 => 2 * levels R k + 1

@[simp] theorem levels_zero (R : ℕ) : levels R 0 = R := rfl

@[simp] theorem levels_succ (R k : ℕ) : levels R (k + 1) = 2 * levels R k + 1 := rfl

namespace Prog

/-- The program of the search branch. On the pair `(d, input)` with
`d = encode ((c', (e, (m, m))), m)` (the input is ignored), run `univ` on the first component
of `d` — that is, `c'` on `encode (e, (m, m))`, the string at the start level `m` — and then
`S` on the pair of the result with the start level `m`. Hardcoding `d`
(`hardcode (searchProg univ S) d`) gives the program the search branch tests for halting. -/
def searchProg (univ S : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil
    (.let_ (callVar 0 univ) (.let_ (.cons (.var 0) (.var 2)) (callVar 0 S))))

end Prog

/-- The decider of the compressibility-criterion argument, as a polynomial-time function of
`(c', (e, (m, n)))`: if `e` halts on the empty input within `Nat.size n` steps, the fixed
string `yYes`; else if the search program for the string at the start level `m` halts within
`Nat.size n` steps, the fixed string `yNo`; otherwise `Compr` applied to the succinct
description `hardcode β ((c', e), (m, 2n + 1))` — where `β` is the bit-query program — with
parameter `n`. As for `decFun`, the self-referential program `c` of the proof is a Kleene
fixed point of `c' ↦ hardcode (decFunV …).code (encode c')`. -/
noncomputable def decFunV (U : UniversalMachine) (UT : ClockedUniversalMachine) (S : Prog)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr) (yYes yNo : BitStr) :
    PolyTimeFun (Prog × (Prog × (ℕ × ℕ))) BitStr :=
  PolyTimeFun.ite
    ((PolyTimeFun.haltsWithin UT).comp
      (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.snd)
        (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))))
    (PolyTimeFun.const yYes)
    (PolyTimeFun.ite
      ((PolyTimeFun.haltsWithin UT).comp
        (PolyTimeFun.pair
          ((PolyTimeFun.smn ((Prog × (Prog × (ℕ × ℕ))) × ℕ)).comp
            (PolyTimeFun.pair (PolyTimeFun.const (Prog.searchProg U.univ S))
              (PolyTimeFun.pair
                (PolyTimeFun.pair PolyTimeFun.fst
                  (PolyTimeFun.pair (PolyTimeFun.fst.comp PolyTimeFun.snd)
                    (PolyTimeFun.pair
                      (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
                      (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
                (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))
          (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))))
      (PolyTimeFun.const yNo)
      (Compr.comp (PolyTimeFun.pair
        ((PolyTimeFun.smn ((Prog × Prog) × (ℕ × ℕ))).comp
          (PolyTimeFun.pair (PolyTimeFun.const (Prog.bitQueryProg U.univ))
            (PolyTimeFun.pair
              (PolyTimeFun.pair PolyTimeFun.fst (PolyTimeFun.fst.comp PolyTimeFun.snd))
              (PolyTimeFun.pair
                (PolyTimeFun.fst.comp (PolyTimeFun.snd.comp PolyTimeFun.snd))
                (PolyTimeFun.next.comp
                  (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))))
        (PolyTimeFun.snd.comp (PolyTimeFun.snd.comp PolyTimeFun.snd)))))

/-! ## Interface with Mathlib computability

The project's headline statement (`MIPRE.HaltingGameValue`) is phrased for
`Nat.Partrec.Code` and Mathlib's `Computable`. Two bridges close the gap, both
computability-only (no time bounds): ambient evaluation is partial recursive, so a
polynomial-time function of the model is Mathlib-computable on computably encoded inputs
(`PolyTimeFun.computable_comp`, `Cost/Partrec.lean`), and the halting problem of
`Nat.Partrec.Code` compiles into the model along a map that is computable on descriptions
(`exists_compile`, `Cost/FromPartrec.lean`). Both work at the level of `Data`: no
`Primcodable` instance for `Prog` is needed, since programs are their own descriptions. -/

end MIPRE.Cost


