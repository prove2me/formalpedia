-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
-- name    : MIPRE_Foundations_Cost_FromPartrec_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:24:22.439791+00:00
-- url     : https://prove2.me/theorems/4aaf9831-24dc-4024-9fe1-68d12f2f6c93
-- title:
--   Halting of a translated `ToPartrec` code is halting of the code (from-partrec addendum)
-- statement:
--   This bundle adds one theorem, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_FromPartrec`, which translates Mathlib's language `Turing.ToPartrec.Code` (a small first-order language on lists of naturals in which every partial recursive function is computable) into the ambient model, construct by construct, through `Prog.ofCode`, with a list of naturals $v$ encoded as the `cons`-chain of unary numerals $\mathrm{encL}\,v$. The added theorem packages the two directions of the correctness of the translation (`ofCode_sound`, `ofCode_complete`) as an equivalence of halting: for every code $c$ and list of naturals $v$,
--
--   $$\mathrm{Halts}\,(\mathrm{ofCode}\,c)\,(\mathrm{encL}\,v) \;\longleftrightarrow\; (c.\mathrm{eval}\,v).\mathrm{Dom},$$
--
--   where `Halts p x` says that the program $p$ has a run on the input $x$, and `(c.eval v).Dom` says that the partial evaluation of the code on $v$ is defined. This is the bridge used by the semidecider construction (`Cost/Semidecide.lean`), which runs a `ToPartrec` code for a recursively enumerable predicate inside the ambient model.
--
--   **Formalization Note** The statement is `ofCode_halts_iff (c : Code) (v : List ℕ) : Halts (ofCode c) (encL v) ↔ (c.eval v).Dom`, with `Halts p x := ∃ r t, Eval [x] p r t` and `Code.eval : Code → List ℕ →. List ℕ` Mathlib's partial evaluation (a `Part`). No cost information is carried: the equivalence is between halting and definedness only.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FromPartrec.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_FromPartrec does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_complete
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_sound

/-!
# From Mathlib's partial recursive functions into the ambient model

Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of naturals
(`zero'`, `succ`, `tail`, `cons`, `comp`, `case`, `fix`) in which every partial recursive
function is computable (`Turing.ToPartrec.Code.exists_code`). It translates construct by
construct into the ambient language (`Prog.ofCode`), with lists of naturals encoded as
`cons`-chains of unary numerals (`encL`) and `fix` as a `loop`; `ofCode_sound` and
`ofCode_complete` are the two directions of the correctness of the translation.

`exists_compile` is the resulting bridge for the halting problem: a map `compile` from
`Nat.Partrec.Code` to programs, computable on descriptions, such that `compile pc` halts on
the empty input iff `pc` does on `0`: `compile pc` hardcodes the code number of `pc` into
the translation of a `ToPartrec.Code` for the universal partial function `n ↦ (ofNat n).eval 0`.
-/

namespace MIPRE.Cost

open Turing.ToPartrec (Code)

namespace Prog

/-! ## Forward runs of the pieces -/

/-! ## Soundness -/

/-! ## Completeness -/

/-- Halting of the translation of `c` on `encL v` is halting of `c` on `v`. -/
theorem ofCode_halts_iff (c : Code) (v : List ℕ) :
    Halts (ofCode c) (encL v) ↔ (c.eval v).Dom := by
  constructor
  · rintro ⟨r, t, h⟩
    obtain ⟨w, -, hw⟩ := ofCode_complete c v r t h
    exact Part.dom_iff_mem.2 ⟨w, hw⟩
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 h
    obtain ⟨t, ht⟩ := ofCode_sound c v w hw
    exact ⟨_, t, ht⟩

end Prog

/-! ## The halting-problem bridge -/

end MIPRE.Cost


