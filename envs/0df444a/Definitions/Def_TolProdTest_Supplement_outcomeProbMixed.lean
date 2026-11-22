-- Prove2me | Definitions.Def_TolProdTest_Supplement_outcomeProbMixed
-- name    : TolProdTest_Supplement_outcomeProbMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:07:15.139983+00:00
-- url     : https://prove2.me/theorems/df1d9f14-291c-41d3-a01a-e27ea786fda6
-- title:
--   Probability of an outcome event of a circuit on a mixed input
-- statement:
--   Fix $N$ copies of an $n$-qudit system of local dimension $d$, $m$ ancilla qubits, and a circuit $U$ given as a list of gates from $\{H,S,T,X,\mathrm{CNOT}\}$ on $W=N\cdot n\cdot\lceil\log_2 d\rceil+m$ qubit wires. For an operator $\sigma$ on the $N$ copies (typically $\rho^{\otimes N}$) and a set $E$ of outcome strings $y\in\{0,1\}^W$, the **outcome-event probability** is
--
--   $$
--   \Pr[E]=\sum_{y\in E}\operatorname{Re}\big(U V\sigma V^\dagger U^\dagger\big)_{yy},
--   $$
--
--   where $V$ is the published encoding isometry (each qudit stored in $\lceil\log_2 d\rceil$ wires, little-endian, copy-major; ancillas in $|0\rangle$). It is the Born probability that measuring every wire in the computational basis gives a string in $E$.
--
--   This extends the one-wire acceptance probability of the base mission (`TolProdTest.acceptProbMixed`, the case $E=\{y: y_{\mathrm{out}}=1\}$) to algorithms whose output is a whole bit string, as for the learners of Theorems 4.1 and 4.2.
--
--   **Formalization Note** Intermediate measurements and classical post-processing are deferred into the circuit, whose gate count is the length of the list.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 4.1, p.19; Theorem 4.2, p.20 (algorithm model of the mission, from Theorem 1.1, p.3)

import Mathlib
import Definitions.Def_TolProdTest_acceptProbMixed

set_option autoImplicit false

open Matrix

namespace TolProdTest.Supplement

/-- **Probability of an outcome event of a quantum circuit on a mixed input** (the algorithm model of the
mission, extended from one output wire to an event over all wires; used for the learners of Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…),
Theorem 4.1, p.19, and Theorem 4.2, p.20).

An algorithm with `N` copies is a list of gates over the published gate set `{H, S, T, X, CNOT}`
(`ShiShallow.Instr`) on `W = N·n·qd d + m` qubit wires. The input `σ` (an operator on `N` copies of
`(ℂ^d)^{⊗n}`, typically `ρ^{⊗N}`) is loaded on the data wires through the published encoding `inputIso`
(`Nat.clog 2 d` wires per qudit, little-endian, copy-major), the `m` ancillas start in `|0⟩`, the gates `U`
(`circMat`) are applied, and **every** wire is measured in the computational basis. The value is the Born
probability that the outcome string lies in the event `E`:
`Σ_{y ∈ E} Re (U V σ V† U†)_{yy}`.

**Formalization Note** With `E y := (y out = true)` this is the published `TolProdTest.acceptProbMixed`.
Intermediate measurements and classical post-processing are deferred into the circuit; the gate count of the
algorithm is the length of the list. -/
noncomputable def outcomeProbMixed {N n d m : ℕ}
    (σ : Matrix (Fin N → Fin n → Fin d) (Fin N → Fin n → Fin d) ℂ)
    (gates : List (ShiShallow.Instr (N * n * qd d + m)))
    (E : ShiShallow.Bits (N * n * qd d + m) → Prop) [DecidablePred E] : ℝ :=
  ∑ y : ShiShallow.Bits (N * n * qd d + m),
    if E y then
      ((circMat gates * inputIso N n d m * σ * (inputIso N n d m)ᴴ * (circMat gates)ᴴ) y y).re
    else 0

end TolProdTest.Supplement


