-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_MachineBound
-- name    : MIPRE_Foundations_Cost_MachineBound
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:22:48.074617+00:00
-- url     : https://prove2.me/theorems/3454bd6e-4636-43d0-92a5-622c4943c5eb
-- title:
--   Size bounds on machine configurations along a run
-- statement:
--   This bundle defines the bounds that every configuration of the evaluation machine satisfies along the simulation of a derivation, and the resulting bound on the size of its encoding.
--
--   `MIPRE.Cost.Machine.FrameBound` $V\ L\ P$ is a predicate on frames: a frame carrying an environment ($\mathtt{cons1}$, $\mathtt{let1}$, $\mathtt{loop1}$) must hold a program of size at most $P$ and an environment of length at most $L$ all of whose values have size at most $V$; a frame $\mathtt{cons2}(a)$ must have $\mathrm{size}(a) \le V$.
--
--   `MIPRE.Cost.Machine.CfgBound` $V\ L\ P\ K\ c$ is the corresponding bound on a configuration $c$, a structure with six clauses:
--
--   1. a returned value has size at most $V$;
--   2. a program under evaluation has size at most $P$;
--   3. the environment has length at most $L$;
--   4. every value in the environment has size at most $V$;
--   5. the stack has length at most $K$;
--   6. every frame of the stack satisfies $\mathrm{FrameBound}\ V\ L\ P$.
--
--   `MIPRE.Cost.Machine.cfgSizeBound` $V\ L\ P\ K$ is the explicit bound
--   $$V + P + L\,V + L + K\,(V + P + L\,V + L + 10) + K + 8$$
--   on the size of the data encoding of any configuration satisfying $\mathrm{CfgBound}\ V\ L\ P\ K$.
--
--   No lemma is proved inside this bundle.
--
--   **Formalization Note**. Along the machine run simulating a derivation $\mathrm{Eval}(\mathit{env}, p, r, t)$ the bounds hold with $V$ any number at least $t$ and at least the sizes of the initial values (every value produced is the result of a sub-derivation of cost at most $t$, hence of size at most $t$), $L$ the initial environment length plus $2t$, $P$ the size of the initial program (every program under evaluation is one of its subterms), and $K$ the initial stack length plus $t$ (the stack gains at most $t$ frames). The uploaded theorems `eval_steps_bound` and `size_toData_le` establish this; the consequence, that every configuration handled by the self-interpreter on a halting run has size polynomial in $\mathrm{esize}(p) + \mathrm{size}(\mathrm{input}) + t$, is what bounds the cost of the universal machine.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineBound.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# Size bounds along machine runs

Along the run of the evaluation machine that simulates a derivation `Eval env p r t`, every
configuration stays bounded (`CfgBound`): values have size at most `V` (where `t ≤ V` and
the initial values are at most `V`, since every value produced is the result of a
sub-derivation of cost at most `t`), environments have length at most `L + 2 t`, programs
are subterms of the initial ones, and the stack gains at most `t` frames
(`eval_steps_bound`). Consequently the data encoding of every configuration along the run
has size polynomial in the sizes of the program, the input and the cost
(`size_toData_le`). This is what bounds the cost of the self-interpreter.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Bounds on configurations -/

/-- Bounds on a frame: values of size at most `V`, an environment of length at most `L`,
a program of size at most `P`. -/
def FrameBound (V L P : ℕ) : Frame → Prop
  | .cons1 t env => esize t ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .cons2 a => a.size ≤ V
  | .let1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V
  | .loop1 b env => esize b ≤ P ∧ env.length ≤ L ∧ ∀ v ∈ env, v.size ≤ V

/-- Bounds on a configuration: values of size at most `V`, environments of length at most
`L`, programs of size at most `P`, a stack of length at most `K`. -/
structure CfgBound (V L P K : ℕ) (c : Cfg) : Prop where
  ctrl_val : ∀ v, c.ctrl = .ret v → v.size ≤ V
  ctrl_prog : ∀ p, c.ctrl = .ev p → esize p ≤ P
  env_len : c.env.length ≤ L
  env_val : ∀ v ∈ c.env, v.size ≤ V
  kont_len : c.kont.length ≤ K
  frames : ∀ f ∈ c.kont, FrameBound V L P f

/-! ## Program subterms -/

/-! ## Chaining bounds along runs -/

/-! ## Size of the encoded configurations -/

/-- Size of the encoding of a configuration satisfying `CfgBound V L P K`. -/
def cfgSizeBound (V L P K : ℕ) : ℕ :=
  V + P + L * V + L + K * (V + P + L * V + L + 10) + K + 8

/-! ## Runs from the empty stack are bounded forever -/

/-! ## The number of steps of a run -/

/-! ## Cost sums -/

end Machine

end MIPRE.Cost


