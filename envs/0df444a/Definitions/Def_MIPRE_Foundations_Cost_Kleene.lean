-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Kleene
-- name    : MIPRE_Foundations_Cost_Kleene
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:23:42.918978+00:00
-- url     : https://prove2.me/theorems/a9d0030e-b18b-4a79-bab2-8a2c09b5d0f1
-- title:
--   Efficient Kleene recursion: the fixed-point program and its overhead
-- statement:
--   This bundle defines the fixed point of the efficient Kleene recursion theorem (blueprint `lem:kleene`; [MNY, Lemma 2.3]) as explicit data.
--
--   `MIPRE.Cost.Prog.kleeneProg` $\mathrm{univ}\ F$, for a universal program $\mathrm{univ}$ and a polynomial-time map $F : \mathrm{Prog} \to \mathrm{Prog}$, is the two-argument program $G$ of the classical construction: on the input $\mathtt{cons}(x, v)$, where $x = \mathrm{encode}(x')$ is the description of a program $x'$, it computes the description of $s(x', x') = \mathrm{hardcode}\ x'\ (\mathrm{encode}\ x')$ with `smnProg`, applies the program of $F$ to it, and runs the resulting program on $v$ through $\mathrm{univ}$.
--
--   `MIPRE.Cost.kleeneFix` $U\ F$, for a universal machine $U$, is the fixed point itself,
--   $$e = s(G, G) = \mathrm{hardcode}\ G\ (\mathrm{encode}\ G), \qquad G = \mathrm{kleeneProg}\ U.\mathrm{univ}\ F,$$
--   so that $e$ on an input $v$ runs $G$ on $\mathtt{cons}(\mathrm{encode}\ G, v)$, which runs $F(\mathrm{hardcode}\ G\ (\mathrm{encode}\ G)) = F(e)$ on $v$: the programs $e$ and $F(e)$ compute the same partial function, $\varphi_e = \varphi_{F(e)}$.
--
--   `MIPRE.Cost.kleeneOverhead` $U\ F$ is the fixed part of the time overhead of a run of the fixed point over the corresponding run of $F(e)$,
--   $$7\,\mathrm{esize}(G) + \mathrm{esize}(e) + p_F(\mathrm{esize}(e)) + 2\,\mathrm{esize}(F(e)) + 60,$$
--   where $p_F$ is the time bound of $F$: the copies of the program, the computation of $F(e)$, and constants. The time transfer itself, proved separately (`kleeneFix_runs_of`, `efficient_fixed_point`), is the universal machine's overhead plus this quantity and a copy of the input.
--
--   No lemma is proved inside this bundle.
--
--   **Formalization Note**. The theorem is stated in the one direction the recursive compression argument uses: the runs of $e$ are bounded in terms of those of $F(e)$ at polynomial overhead ([MNY] state the runtimes as polynomially equivalent; the converse direction would need a simulator that is never faster than the simulated program). The construction is exposed as data, with its overhead spelled out, because the polynomial-time halting reduction needs the overhead of the fixed point of a *family* of maps to be bounded uniformly in the family parameter, which only the explicit form shows, the existential polynomial of `efficient_fixed_point` depending on $F$. The s-m-n map is the linear-cost `hardcode`, so the fixed point has size exactly $\mathrm{esize}(e) = 2\,\mathrm{esize}(G) + 35$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Kleene.lean; blueprint lem:kleene; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_Universal

/-!
# Efficient Kleene recursion

The efficient fixed-point theorem `efficient_fixed_point` (blueprint `lem:kleene`;
[MNY, Lemma 2.3]), by the classical construction: for a polynomial-time map `F` on
programs, let `G` be the program that on `cons x v` (with `x` the description of a program
`x'`) computes `s(x', x') = hardcode x' (encode x')`, applies `F` to it, and runs the result
on `v` through the universal machine; the fixed point is `e = hardcode G (encode G)`, since
`e` on `v` is `G` on `cons (encode G) v`, which runs `F (hardcode G (encode G)) = F e` on
`v`. The time transfer is the universal machine's, plus the fixed cost of computing `F e`
and a copy of the input.
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-- The two-argument program of the fixed-point construction: on `cons x v`, compute the
description of `hardcode x' (encode x')` (where `x = encode x'`), apply `F` to it, and run
the result on `v` through the universal program `univ`. -/
def kleeneProg (univ : Prog) (F : PolyTimeFun Prog Prog) : Prog :=
  .elim 0 .nil
    (.let_ (.cons (.var 0) (.var 0))
      (.let_ (callVar 0 smnProg)
        (.let_ (callVar 0 F.code)
          (.let_ (.cons (.var 0) (.var 4))
            (callVar 0 univ)))))

end Prog

/-! ## The fixed point, as data

The construction is exposed (`kleeneFix`) with its overhead spelled out (`kleeneFix_runs_of`),
because the polynomial-time halting reduction (`planning/polytime-halting.md`) needs the overhead
of the fixed point of a *family* `F_M` of maps to be bounded uniformly in `M`: the existential
polynomial of `efficient_fixed_point` below depends on `F`, and only the explicit form shows how. -/

/-- The fixed point of `F` through the universal machine `U`: `hardcode G (encode G)` for the
program `G = kleeneProg U.univ F`. -/
def kleeneFix (U : UniversalMachine) (F : PolyTimeFun Prog Prog) : Prog :=
  hardcode (Prog.kleeneProg U.univ F) (encode (Prog.kleeneProg U.univ F))

/-- The fixed part of the overhead of the fixed point: the copies of the program, the
computation of `F (kleeneFix U F)`, and constants. -/
def kleeneOverhead (U : UniversalMachine) (F : PolyTimeFun Prog Prog) : ℕ :=
  7 * esize (Prog.kleeneProg U.univ F) + esize (kleeneFix U F) +
    F.timeBound.eval (esize (kleeneFix U F)) + 2 * esize (F (kleeneFix U F)) + 60

/-! ## The fixed-point theorem (blueprint `lem:kleene`; [MNY, Lemma 2.3]) -/

end MIPRE.Cost


