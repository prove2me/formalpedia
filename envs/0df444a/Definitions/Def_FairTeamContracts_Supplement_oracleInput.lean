-- Prove2me | Definitions.Def_FairTeamContracts_Supplement_oracleInput
-- name    : FairTeamContracts_Supplement_oracleInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:09:19.818788+00:00
-- url     : https://prove2.me/theorems/ec193bac-506f-4c8d-9893-870a43d7a1c9
-- title:
--   Input configuration of the value-oracle real RAM for Theorem 5.13
-- statement:
--   Algorithm 2 receives "a value oracle for $f$, costs $(c_i)_{i\in[n]}$" (p.27). On the deterministic value-oracle real RAM, the input configuration for costs $c\in\mathbb R^n$ is:
--
--   1. program counter $0$ and all real registers $0$;
--   2. pointer register $0$ holding $n$, all other pointer registers $0$;
--   3. memory cells $0,\dots,n-1$ holding $c_0,\dots,c_{n-1}$, and every other cell holding $0$.
--
--   The success function $f$ is not part of the input. The program reaches it only through its value instruction, which returns $f(S)$ for a set $S$ the program has written to memory as a bitmap.
--
--   **Formalization Note** The machine is the published deterministic value-oracle dialect `TransparencyTeamContracts.Submodular.Supplement.OracleProgram` of the real pointer RAM (`SmaleNinth.RAMConfig`). Its output conventions `outputTeam` and `outputContract` read the team bitmap and the shares from the negative memory cells. The accuracy $\varepsilon$ is not an input, because the program is chosen after $\varepsilon$.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, p.10 (value oracles) and Algorithm 2, p.27

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine

namespace FairTeamContracts.Supplement

/-- Input configuration of the value-oracle real RAM for Theorem 5.13 (Chen, Castiglioni, Li,
*Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Algorithm 2, p.27:
"Input: Value oracle for f, costs (cᵢ)_{i∈[n]}"): program counter `0`, all real registers `0`,
pointer register `0` holding `n` (the others `0`), and memory cells `0, …, n − 1` holding the
costs `c₀, …, c_{n−1}`; every other cell is `0`.

**Formalization Note.** The machine is the published deterministic value-oracle dialect
`TransparencyTeamContracts.Submodular.Supplement.OracleProgram` of the real pointer RAM
`SmaleNinth.RAMConfig`. The success function `f` is not in the input: the program reaches it only
through its value instruction. The accuracy `ε` is not in the input either: the program is chosen
after `ε` (Theorem 5.13: "for every fixed ε > 0, there exists … algorithm"). -/
noncomputable def oracleInput {n : ℕ} (c : Fin n → ℝ) : SmaleNinth.RAMConfig :=
  ⟨0, fun _ => 0, fun j => if j = 0 then (n : ℤ) else 0,
    fun z => if h : 0 ≤ z ∧ z < n then c ⟨z.toNat, by omega⟩ else 0⟩

end FairTeamContracts.Supplement


