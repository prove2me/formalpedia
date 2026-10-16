-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
-- name    : MIPRE_Foundations_Cost_MachineBound_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:22:43.289751+00:00
-- url     : https://prove2.me/theorems/2afdc81c-90f3-46bc-ad75-7280393915ec
-- title:
--   Monotonicity of configuration bounds and the final-configuration lemmas (machine-bound addendum)
-- statement:
--   This bundle adds seven theorems, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_MachineBound`, which bounds the configurations met along a run of the evaluation machine. `FrameBound V L P f` says a stack frame holds values of size at most $V$, environments of length at most $L$ and programs of size at most $P$; `CfgBound V L P K c` says the same of a configuration, with a stack of length at most $K$. The added lemmas: both bounds are monotone in all their parameters (`FrameBound.mono`, `CfgBound.mono`); a final configuration $\langle \mathrm{ret}\,r, e, [\,]\rangle$ is a fixed point of `step` (`step_final`), has `stepCost` $0$ and `costSum` $0$ for every number of steps; `costSum c (n+1) = costSum c n + stepCost (step^[n] c)`; and the run of a derivation from the empty stack is bounded forever: if `Eval env p r t` holds, $\mathrm{CfgBound}\,V\,L\,P\,K\,\langle \mathrm{ev}\,p, env, [\,]\rangle$ and $t \le V$, then
--
--   $$\exists\, N\ env',\quad \mathrm{Steps}\,\langle \mathrm{ev}\,p, env, [\,]\rangle\ N\ \langle \mathrm{ret}\,r, env', [\,]\rangle\ t \;\wedge\; \forall n,\ \mathrm{CfgBound}\,V\,(L + 2t)\,P\,(K + t)\,\big(\mathrm{step}^{[n]}\langle \mathrm{ev}\,p, env, [\,]\rangle\big),$$
--
--   that is, every iterate of the step function, before and after the final configuration, stays within the enlarged bounds. This is the form of the size bound that the clocked universal machine needs, since its loop keeps stepping a configuration that may already be final.
--
--   **Formalization Note** `Steps c N c' t` is `step^[N] c = c' ∧ costSum c N = t`. The monotonicity lemmas take the inequalities `V ≤ V'`, `L ≤ L'`, `P ≤ P'` (and `K ≤ K'`) as explicit hypotheses. `eval_steps_bound_forever` is stated for implicit `env p r t` with `h : Eval env p r t` and explicit `V L P K`; `step_final`, `stepCost_final` and `costSum_final` are stated for an arbitrary returned value `r : Data` and environment `e : Env`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineBound.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_MachineBound does not carry);
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound

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

theorem FrameBound.mono {V L P V' L' P' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    {f : Frame} (h : FrameBound V L P f) : FrameBound V' L' P' f := by
  cases f with
  | cons2 a => exact le_trans h hV
  | cons1 t env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | let1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩
  | loop1 b env => exact ⟨le_trans h.1 hP, le_trans h.2.1 hL, fun v hv => le_trans (h.2.2 v hv) hV⟩

theorem CfgBound.mono {V L P K V' L' P' K' : ℕ} (hV : V ≤ V') (hL : L ≤ L') (hP : P ≤ P')
    (hK : K ≤ K') {c : Cfg} (h : CfgBound V L P K c) : CfgBound V' L' P' K' c where
  ctrl_val v hv := le_trans (h.ctrl_val v hv) hV
  ctrl_prog p hp := le_trans (h.ctrl_prog p hp) hP
  env_len := le_trans h.env_len hL
  env_val v hv := le_trans (h.env_val v hv) hV
  kont_len := le_trans h.kont_len hK
  frames f hf := (h.frames f hf).mono hV hL hP

/-! ## Program subterms -/

/-! ## Chaining bounds along runs -/

/-! ## Size of the encoded configurations -/

/-! ## Runs from the empty stack are bounded forever -/

theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n

/-- Along the run of a derivation from the empty stack, every configuration — also after
the final one, which is fixed — is bounded. -/
theorem eval_steps_bound_forever {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (V L P K : ℕ) (hb : CfgBound V L P K ⟨.ev p, env, []⟩) (ht : t ≤ V) :
    ∃ N env', Steps ⟨.ev p, env, []⟩ N ⟨.ret r, env', []⟩ t ∧
      ∀ n, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, []⟩) := by
  obtain ⟨N, env', hs, hb'⟩ := eval_steps_bound h [] V L P K hb ht
  refine ⟨N, env', hs, fun n => ?_⟩
  by_cases hn : n ≤ N
  · exact hb' n hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    have hN := hb' N le_rfl
    rw [show N + m = m + N by omega, Function.iterate_add_apply, hs.1, step_final]
    rwa [hs.1] at hN

/-! ## The number of steps of a run -/

/-! ## Cost sums -/

theorem costSum_succ (c : Cfg) (n : ℕ) :
    costSum c (n + 1) = costSum c n + stepCost (step^[n] c) := by
  rw [costSum_add, costSum, costSum]; omega

theorem stepCost_final (r : Data) (e : Env) : stepCost ⟨.ret r, e, []⟩ = 0 := rfl

theorem costSum_final (r : Data) (e : Env) (n : ℕ) : costSum ⟨.ret r, e, []⟩ n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [costSum_succ, ih, step_final, stepCost_final]

end Machine

end MIPRE.Cost


