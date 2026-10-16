-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
-- name    : MIPRE_Foundations_Cost_Toolkit_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:20:05.55652+00:00
-- url     : https://prove2.me/theorems/e2301f3a-3d90-41c6-9147-8e73d58ffcab
-- title:
--   The description of a hardcoded program, spelled out (toolkit addendum)
-- statement:
--   This bundle adds one declaration to the already published bundle `MIPRE_Foundations_Cost_Toolkit`, the efficient computability toolkit (universal machine, s-m-n, Kleene recursion) of the ambient cost model, following [MNY, Lemmas 2.1–2.3]. The toolkit's efficient s-m-n map is $\mathrm{hardcode}\,p\,d = \mathrm{let\_}\,(\mathrm{cons}\,(\mathrm{const}\,d)\,(\mathrm{var}\,0))\,p$, which binds the pair $(d, \text{input})$ as the input of the program $p$. The added theorem computes the data description (`Prog.toData`) of a hardcoded program explicitly: for every program $p$ and datum $d$, writing $\overline{n}$ for the unary numeral `Data.ofNat n`,
--
--   $$\mathrm{toData}(\mathrm{hardcode}\,p\,d) \;=\; \mathrm{cons}\big(\overline{4},\ \mathrm{cons}\big(\mathrm{cons}\big(\overline{2},\ \mathrm{cons}(\mathrm{cons}(\overline{6}, d),\ \mathrm{cons}(\mathrm{nil}, \mathrm{nil}))\big),\ \mathrm{toData}\,p\big)\big).$$
--
--   This is the shape the size count `hardcode_size` ($\mathrm{esize}(\mathrm{hardcode}\,p\,d) = \mathrm{esize}\,p + |d| + 35$) and the runtime s-m-n program rely on when they manipulate descriptions of hardcoded programs as data.
--
--   **Formalization Note** The statement is `toData_hardcode (p : Prog) (d : Data) : (hardcode p d).toData = .cons (.ofNat 4) (.cons (.cons (.ofNat 2) (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) p.toData)`. The tags come from `Prog.toData`: `4` is the tag of `let_`, `2` of `cons`, `6` of `const`, and `cons nil nil` is the description of `var 0` (tag `0` and index `0`, both the numeral `nil`).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean; [MNY, Lemmas 2.1–2.3]

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Toolkit.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Toolkit does not carry);
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
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

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

/-- The description of a hardcoded program, spelled out. -/
theorem toData_hardcode (p : Prog) (d : Data) :
    (hardcode p d).toData = .cons (.ofNat 4) (.cons (.cons (.ofNat 2)
      (.cons (.cons (.ofNat 6) d) (.cons .nil .nil))) p.toData) := rfl

/-! ## The efficient universal machine (blueprint `lem:universal-tm`; [MNY, Lemma 2.1])

The two universal machines are *structures*: the program and its overhead polynomial are
fields, so that downstream definitions (deciders simulating other deciders under a budget;
the λ-bookkeeping of [JNVWY, §12.2], which chooses λ above the concrete overhead
polynomials) can refer to them as data. Their existence is proved in `Cost/Universal.lean`
(`selfUniversal`, `selfClockedUniversal`). -/

/-! `exists_efficient_universal : Nonempty UniversalMachine` (blueprint `lem:universal-tm`)
is proved in `Cost/Universal.lean` by the self-interpreter. -/

/-! `exists_clocked_universal : Nonempty ClockedUniversalMachine` (blueprint
`lem:universal-tm`) is proved in `Cost/Universal.lean` by the clocked self-interpreter. -/

/-! ## Efficient Kleene recursion

`efficient_fixed_point` (blueprint `lem:kleene`; [MNY, Lemma 2.3]) is proved in
`Cost/Kleene.lean` from `hardcode`, `smnProg` and a `UniversalMachine`. -/

end MIPRE.Cost


