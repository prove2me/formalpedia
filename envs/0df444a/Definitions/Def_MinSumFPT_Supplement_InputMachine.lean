-- Prove2me | Definitions.Def_MinSumFPT_Supplement_InputMachine
-- name    : MinSumFPT_Supplement_InputMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:16:06.984627+00:00
-- url     : https://prove2.me/theorems/30c7f518-c3fc-4d69-8c84-fc0547ed7f86
-- title:
--   Runs of the distance-oracle real RAM on an explicit input
-- statement:
--   The conditional lower bounds of §3 speak of algorithms that read an explicit input: two lists of Boolean vectors, a set system, a table of client–facility distances, a 3-CNF formula. This definition runs the published machine `MinSumFPT.Machine` (same instructions, same admissible programs, same step function, one unit of work per instruction) from a start state that holds such an input.
--
--   An input is a list $z_0,\dots,z_{L-1}$ of integers and a list $r_0,\dots,r_{R-1}$ of reals. The integer memory holds $L$ at address $0$, $R$ at address $1$ and $z_i$ at address $2+i$; the real memory holds $r_i$ at address $i$. Every other cell, register and pointer is $0$, and the distance oracle is not used (the instance is empty). A program **answers** $b\in\{\text{true},\text{false}\}$ on an input within $T$ steps if, on every random tape, it halts with real output $1$ (for true) or $0$ (for false) after at most $T$ units of work.
--
--   These runs are the common model in which the Orthogonal Vectors Hypothesis and Theorems 38–40 are stated, so that the reductions of their proofs are programs of the same machine.
--
--   **Formalization Note** Requiring the answer on every tape is the deterministic reading of "algorithm". Reals cannot be cast to integers, so real data (the distances of Theorem 39) is compared only through real arithmetic and comparisons.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §3, pp.43–49 (Hypothesis 2, p.43; Theorems 38–40, pp.45, 47, 48)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-!
# Runs of `MinSumFPT.Machine` on an explicit input

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §3, pp.43–49: Hypothesis 2 (OVH, p.43) and Theorems 38–40 (pp.45, 47, 48) speak of
algorithms that read an explicit input (two lists of vectors, a set system, a client–facility
distance table, a 3-CNF formula).

This module bundles the tightly coupled objects `emptyD`, `inputState`, `runIn` and
`AnswersWithin`.

**Formalization Note.** The instruction set, programs, `Admissible`, states and the step function
are those of the published `MinSumFPT.Machine`, unchanged; only the start state differs. An input is
a list `zs` of integers and a list `rs` of reals: `imem 0 = |zs|`, `imem 1 = |rs|`,
`imem (2 + i) = zs[i]`, real memory `mem i = rs[i]` (`0 ≤ i < |rs|`); every other cell, register
and pointer is `0`. The distance oracle is not used: the run uses the empty instance on `Fin 0`
(every `dist` returns `0`). A decision is the real output after `halt`: `1` for YES, `0` for NO.
The guarantee is required on **every** random tape (a deterministic algorithm); the running time
is the `work` counter (one unit per executed instruction). -/

/-- The empty distance instance on `Fin 0` (no oracle is used by input-reading runs). -/
def emptyD : Fin 0 → Fin 0 → ℝ := fun _ _ => 0

/-- The start state with the integer input `zs` and the real input `rs` loaded into memory. -/
noncomputable def inputState (zs : List ℤ) (rs : List ℝ) : State where
  cfg := ⟨0, fun _ => 0, fun _ => 0, fun i => if 0 ≤ i then rs.getD i.toNat 0 else 0⟩
  imem := fun i =>
    if i = 0 then (zs.length : ℤ) else if i = 1 then (rs.length : ℤ)
    else if 2 ≤ i then zs.getD (i - 2).toNat 0 else 0
  tapePos := 0
  work := 0
  queries := 0
  halted := false
  output := 0

/-- The state after `t` steps of `P` on the explicit input `(zs, rs)` and the tape `ω`. -/
noncomputable def runIn (P : Program) (zs : List ℤ) (rs : List ℝ) (ω : ℕ → ℝ) (t : ℕ) : State :=
  (step P emptyD ω)^[t] (inputState zs rs)

/-- On the input `(zs, rs)`, on every tape, `P` halts with the answer `b` (output `1` for `true`,
`0` for `false`) after at most `T` units of work. -/
def AnswersWithin (P : Program) (zs : List ℤ) (rs : List ℝ) (b : Bool) (T : ℝ) : Prop :=
  ∀ ω : ℕ → ℝ, ∃ t : ℕ, (runIn P zs rs ω t).halted = true ∧
    (runIn P zs rs ω t).output = (if b then 1 else 0) ∧ ((runIn P zs rs ω t).work : ℝ) ≤ T

end MinSumFPT.Supplement


