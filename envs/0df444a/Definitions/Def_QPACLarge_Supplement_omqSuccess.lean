-- Prove2me | Definitions.Def_QPACLarge_Supplement_omqSuccess
-- name    : QPACLarge_Supplement_omqSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:24:32.140809+00:00
-- url     : https://prove2.me/theorems/7ef5c4ce-9dfb-434a-a556-bc24192c704d
-- title:
--   Success probability of a time-bounded uniform randomized membership-query learner
-- statement:
--   Let $A$ be an oracle Turing machine (one machine for all input lengths), let $T, m \in \mathbb N$, let $f : \{0,1\}^m \to \{0,1\}$ be a target, and let $P$ be a property of Boolean circuits on $m$ inputs. The success probability $\mathrm{succ}_A(T, m, f, P)$ is the fraction of coin strings $r \in \{0,1\}^{2^m}$ for which $A$, started on input $1^m0\,r$ with membership access to $f$, halts within $T$ steps and outputs the description of a well-formed Boolean circuit $h$ (AND, OR, NOT gates; one output) such that $P(h)$ holds:
--
--   $$
--   \mathrm{succ}_A(T,m,f,P) = 2^{-2^m}\,\Big|\big\{ r \in \{0,1\}^{2^m} : A^{f}(1^m0\,r) \text{ halts within } T \text{ steps with output } \langle h\rangle,\ P(h)\big\}\Big|.
--   $$
--
--   The oracle answers a query $x \in \{0,1\}^m$ by $f(x)$, and a query of any other length by the empty word. A run that has not halted after $T$ steps, or halts with an output that is not a circuit description, fails. The number of coin bits, $2^m$, is fixed by $m$ and does not depend on $T$, so the input does not reveal the time budget; a run of $T = o(2^{m/2})$ steps never reaches the end of the coins for large $m$.
--
--   This is the learner model of Theorem 4.3: a uniform randomized classical algorithm with membership queries, truncated at its running time $T(m)$, exactly as in the proof of Theorem 4.3 ("Truncate it after its promised running time").
--
--   **Formalization Note** The machine is the published `HMBinPacking.OracleMachine` (each step and each oracle call costs one unit), and halting within $T$ steps means that its run `oRun` reaches a halting configuration whose output stack holds the description (the other stacks may be nonempty). Circuit descriptions are the published binary prefix-free code `QPACLarge.encBoolCircuitBin`. The oracle convention is that of the published `QPACLarge.prfAdv`.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15 (membership queries); Theorem 4.3 and its proof, p.32 (uniform randomized learner running in time o(2^{m/2}), truncation)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QPACLarge_encBoolCircuitBin

namespace QPACLarge.Supplement

open QAlgorithms QAlgorithms.Complexity

/-- **Success probability of a time-bounded uniform randomized membership-query learner.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*,
arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15 ("Membership Queries"), and
Theorem 4.3 with its proof, p.32: "no uniform randomized classical algorithm `A` … runs in
`o(2^{m/2})` time with membership queries and outputs a deterministic Boolean circuit `h`";
"Truncate it after its promised running time, and output a fixed constant circuit if it has not
produced a valid circuit by then."

`omqSuccess A T m f P` is the fraction of coin strings `r ∈ {0,1}^{2^m}` such that the oracle
machine `A` (the published `HMBinPacking.OracleMachine`), started on `1^m 0 · r` with membership
access to `f : {0,1}^m → {0,1}`, reaches a halting configuration within `T` steps whose output stack
holds the code (`encBoolCircuitBin`) of a well-formed Boolean circuit `C` on `m` inputs with one
output such that `P C` holds. The oracle answers an `m`-bit query `x` by the bit `f(x)` and any query
of another length by the empty word.

**Formalization Note.** One machine serves every input length (a uniform learner); the input
length reaches it in unary. A run that does not halt within `T` steps, or halts with an output
stack that is not exactly a circuit code, counts as failure (the paper's truncation). The number of
coin bits is `2^m`, a fixed function of `m` that does not depend on the time budget `T`: a machine
whose input length revealed `T` would receive `T` as advice. A run of `T` steps reads `O(T)` input
symbols, and `T(m) = o(2^{m/2})` in Theorem 4.3, so for large `m` no run reaches the end of the
coins. Halting is read from the configuration of the published `oRun` (label `none`, output stack
`k₁`); the other stacks may be nonempty and queries have no length bound, so the machine need not
spend steps clearing its input. -/
noncomputable def omqSuccess (A : HMBinPacking.OracleMachine) (T m : ℕ) (f : Qubits m → Bool)
    (P : BoolCircuit m 1 → Prop) : ℝ :=
  open Classical in
  ((2 : ℝ) ^ (2 ^ m))⁻¹ * ((Finset.univ.filter fun r : Fin (2 ^ m) → Bool =>
    ∃ C : BoolCircuit m 1, C.WellFormed ∧ P C ∧
      ∃ j ≤ T, ∃ c : HMBinPacking.OCfg A,
        HMBinPacking.oRun A (fun q => if q.length = m then [f (fun i => q.getD i false)] else [])
          (encNat m ++ List.ofFn r) j = some c ∧ c.l = none ∧
        c.stk A.M.tm.k₁ = (QPACLarge.encBoolCircuitBin C).map A.M.outputAlphabet.symm).card : ℝ)

end QPACLarge.Supplement


