-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Tseitin
-- name    : MIPRE_Foundations_SAT_Tseitin
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:16.823999+00:00
-- url     : https://prove2.me/theorems/21e1f8b3-d565-4f22-a81e-9f14067b7391
-- title:
--   Definitions of Tseitin: The circuit-to-3SAT reduction `Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Tseitin` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The circuit-to-3SAT reduction. `Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its variable is the gate's function of its arguments' variables, and the unit clause on the output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a satisfying assignment carries the…
--
--   **Definitions** (5): `MIPRE.SAT.Circuit.InputsLt` (Every input gate reads an existing input.); `MIPRE.SAT.Circuit.RefsLt` (Every gate reads only earlier gates.); `MIPRE.SAT.Circuit.tseitin` (The circuit-to-3SAT formula of `C`: the consistency clauses of every gate, and the unit clause on the output gate.); `MIPRE.SAT.cl` (A clause from three literals.); `MIPRE.SAT.gateClauses` (The consistency clauses of a gate whose variable is `y`, over the input variables `inp` and the gate variables `gv`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Tseitin` (`MIPRE/Foundations/SAT/Tseitin.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Tseitin.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf

/-!
# The circuit-to-3SAT reduction

`Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its
inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the
output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its
variable is the gate's function of its arguments' variables, and the unit clause on the
output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some
assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a
satisfying assignment carries the gate values. The tableau of the Cook–Levin theorem is
this reduction applied to the local check circuit at every window
(`planning/succinct-cook-levin.md`, S1).
-/

namespace MIPRE.SAT

variable {V : Type*}

/-- A clause from three literals. -/
def cl (a b c : Lit V) : Clause3 V := ⟨a, b, c⟩

/-- The consistency clauses of a gate whose variable is `y`, over the input variables `inp`
and the gate variables `gv`. -/
def gateClauses (inp gv : ℕ → V) (y : V) : Gate → List (Clause3 V)
  | .input i => [cl ⟨inp i, false⟩ ⟨y, true⟩ ⟨y, true⟩, cl ⟨inp i, true⟩ ⟨y, false⟩ ⟨y, false⟩]
  | .const b => [cl ⟨y, b⟩ ⟨y, b⟩ ⟨y, b⟩]
  | .and u v =>
    [cl ⟨gv u, false⟩ ⟨gv v, false⟩ ⟨y, true⟩, cl ⟨gv u, true⟩ ⟨gv v, true⟩ ⟨y, false⟩,
      cl ⟨gv u, true⟩ ⟨gv v, false⟩ ⟨y, false⟩, cl ⟨gv u, false⟩ ⟨gv v, true⟩ ⟨y, false⟩]
  | .or u v =>
    [cl ⟨gv u, true⟩ ⟨gv v, true⟩ ⟨y, false⟩, cl ⟨gv u, false⟩ ⟨gv v, false⟩ ⟨y, true⟩,
      cl ⟨gv u, false⟩ ⟨gv v, true⟩ ⟨y, true⟩, cl ⟨gv u, true⟩ ⟨gv v, false⟩ ⟨y, true⟩]
  | .not u => [cl ⟨gv u, true⟩ ⟨y, true⟩ ⟨y, true⟩, cl ⟨gv u, false⟩ ⟨y, false⟩ ⟨y, false⟩]

namespace Circuit

/-- The circuit-to-3SAT formula of `C`: the consistency clauses of every gate, and the unit
clause on the output gate. -/
def tseitin (C : Circuit) (inp gv : ℕ → V) : Cnf3 V :=
  {c | ∃ g : Fin C.gates.length, c ∈ gateClauses inp gv (gv g) C.gates[g]} ∪
    {cl ⟨gv (C.gates.length - 1), true⟩ ⟨gv (C.gates.length - 1), true⟩
      ⟨gv (C.gates.length - 1), true⟩}

/-- Every gate reads only earlier gates. -/
def RefsLt (C : Circuit) : Prop :=
  ∀ (k : ℕ) (h : k < C.gates.length), ∀ u ∈ C.gates[k].refs, u < k

/-- Every input gate reads an existing input. -/
def InputsLt (C : Circuit) : Prop := ∀ i, Gate.input i ∈ C.gates → i < C.inputs

end Circuit

end MIPRE.SAT


