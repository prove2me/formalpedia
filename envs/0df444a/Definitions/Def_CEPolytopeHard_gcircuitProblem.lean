-- Prove2me | Definitions.Def_CEPolytopeHard_gcircuitProblem
-- name    : CEPolytopeHard_gcircuitProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:38.109877+00:00
-- url     : https://prove2.me/theorems/a9f9a94f-a73f-4745-802d-2f2dadb554b6
-- title:
--   Search problem: satisfy $(1-\gamma)d$ gates of a fan-out-two generalized circuit
-- statement:
--   For a tolerance $\tau$ and a fraction $\gamma$, an instance of $\mathrm{GCircuit}(\tau, \gamma)$ is the encoding of a well-formed generalized circuit with fan-out two and $d$ nodes, and an answer is the encoding of a rational assignment $v \in ([0, 1] \cap \mathbb Q)^d$ that satisfies at least
--   $$
--   (1 - \gamma)\, d
--   $$
--   gates at tolerance $\tau$. With $\gamma = 0$ every gate must be satisfied.
--
--   This is the problem of Assumption 2.2 ("given a generalized circuit with fan-out two, compute an assignment satisfying at least $(1-\gamma)d$ gates at tolerance $\tau$").
--
--   **Formalization Note** Gates are coded by a type tag followed by their parameter and inputs; the circuit code is the length-prefixed list of gate codes (injective, checked in the verification file). Assignments are rational because answers are finite strings.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.5, pp.12–13 and Assumption 2.2, p.13

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
import Definitions.Def_CEPolytopeHard_lenList
import Definitions.Def_CEPolytopeHard_GCircuit

set_option autoImplicit false

namespace CEPolytopeHard

open CorrelatedAuctionComplexity.Main

/-- code of a gate: a type tag, then its parameter and inputs -/
def encGate : GGate → List ℕ
  | .const β => 0 :: ratCode β
  | .scale β a => 1 :: (ratCode β ++ [a])
  | .copy a => [2, a]
  | .add a b => [3, a, b]
  | .sub a b => [4, a, b]
  | .cmp a b => [5, a, b]

/-- binary encoding of a generalized circuit: the length-prefixed list of its gate codes -/
def GCircuit.encode (C : GCircuit) : Bits := pack (lenList encGate C.gates)

/-- The **search problem of satisfying a `(1 − γ)` fraction of the gates of a fan-out-two
generalized circuit at tolerance τ** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Section 2.5, pp.12–13, Assumption 2.2: "given a
generalized circuit with fan-out two, compute an assignment satisfying at least (1 − γ)d gates at
tolerance τ"). An instance is the encoding of a well-formed generalized circuit with fan-out two;
an answer is the encoding (length-prefixed list of `ratCode`s) of a rational assignment
`v ∈ ([0, 1] ∩ ℚ)^d` under which at least `(1 − γ)d` gates are satisfied at tolerance `τ`.
With `γ = 0` every gate must be satisfied.

**Formalization Note** Assignments are rational because answers are finite strings (p.10: "All
numbers are rational numbers encoded in binary"); a circuit "assigns a value in [0, 1] to each of
d nodes" (p.12). -/
def gcircuitProblem (τ γ : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ C : GCircuit, C.encode = s ∧ C.WellFormed ∧ C.FanOutTwo
  answer s t := ∃ C : GCircuit, C.encode = s ∧ C.WellFormed ∧ C.FanOutTwo ∧
    ∃ v : List ℚ, pack (lenList ratCode v) = t ∧ v.length = C.d ∧ (∀ q ∈ v, 0 ≤ q ∧ q ≤ 1) ∧
      (1 - γ) * (C.d : ℝ) ≤
        ({i : Fin C.d | GateSat τ C (fun j => ((v.getD j.val 0 : ℚ) : ℝ)) i}.ncard : ℝ)

end CEPolytopeHard


