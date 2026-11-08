-- Prove2me | Definitions.Def_SingleInteraction_sihProblem
-- name    : SingleInteraction_sihProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:01.522212+00:00
-- url     : https://prove2.me/theorems/09bd3654-8e4e-4701-9973-8053675993ac
-- title:
--   The promise problem $\mathrm{SIH}_k$
-- statement:
--   For a fixed $k$-qubit interaction $h$ and a polynomial exponent $c$, $\mathrm{SIH}_k$ is the promise problem on valid inputs $(n,L,a,b)$ with $H=\sum_{e\in L}h_e$:
--
--   1. YES: there exists an $n$-qubit state $|\phi\rangle$ with $\langle\phi|H|\phi\rangle\le a$;
--   2. NO: every $n$-qubit state $|\phi\rangle$ has $\langle\phi|H|\phi\rangle\ge b$.
--
--   The paper's problem for $h$ corresponds to the family over $c$: membership in QMA is stated for every $c$ and hardness for some $c$.
--
--   **Formalization Note** Definition 31's requirements on $h$ (Hermitian, polynomial-time computable entries) are hypotheses of the theorems, not part of the promise problem.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_SIHInstance_Valid
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_hamPromise

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The promise problem `SIH_k` for a fixed `k`-qubit interaction `h`, at the polynomial exponent `c`
(Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30). For a valid input `(n, L, a, b)` with `H = Σ_{e∈L} h_e`:

* YES: "There exists an `n`-qubit state `|ϕ⟩` such that `⟨ϕ| H |ϕ⟩ ≤ a`";
* NO: "For every `n`-qubit state `|ϕ⟩`, `⟨ϕ| H |ϕ⟩ ≥ b`".

**Formalization Note** "`poly(n)`" in the input conditions is the exponent `c` of `SIHInstance.Valid`.
The paper's single problem corresponds to the family `c ↦ sihProblem k h c`: QMA membership is stated
for every `c` and QMA-hardness for some `c` (hardness for `c` implies it for every `c' ≥ c`, as the
valid sets grow with `c`). The definition's requirement that `h` be Hermitian with polynomial-time
computable entries is a hypothesis of the theorems about it (`EntriesPolyTime`), not part of this
promise problem. -/
noncomputable def sihProblem (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (c : ℕ) :
    PromiseProblem SIHInstance :=
  hamPromise (SIHInstance.Valid k c) (fun x => x.n) (fun x => sihHam k h x)
    (fun x => (x.a.value : ℝ)) (fun x => (x.b.value : ℝ)) (fun _ hx => hx.2.2.lt)

end SingleInteraction


