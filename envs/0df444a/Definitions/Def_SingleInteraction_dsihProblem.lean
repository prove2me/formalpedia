-- Prove2me | Definitions.Def_SingleInteraction_dsihProblem
-- name    : SingleInteraction_dsihProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:50.90962+00:00
-- url     : https://prove2.me/theorems/628a15c6-70a4-4252-bfb9-a9398e57b6d7
-- title:
--   The promise problem $\mathrm{DSIH}_k$
-- statement:
--   For a family $\{h^{(n)}\}$ of $k$-qubit interactions and a polynomial exponent $c$, $\mathrm{DSIH}_k$ is defined as $\mathrm{SIH}_k$ except that an input on $n$ physical qubits uses the common interaction $h^{(n)}$: $H^{(n)}=\sum_{e\in L}h^{(n)}_e$. Inputs, validity and promise are those of $\mathrm{SIH}_k$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 32, p.30

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_SIHInstance_Valid
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_hamPromise

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The promise problem `DSIH_k` for a family `{h^(n)}` of `k`-qubit interactions, at the polynomial
exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 32, p.30): as `SIH_k` (Definition 31), except that an input of final
physical size `n` uses the common interaction `h^(n)`, `H^(n) = Σ_{e∈L} h^(n)_e`. "All remaining input
and promise conditions are those of Definition 31."

**Formalization Note** The same instances, codec and validity as `sihProblem`; `n` is the instance's
system size, the final number of physical qubits. The uniformity and norm requirements on the family are
a hypothesis of the theorems about it (`UniformFamily`). -/
noncomputable def dsihProblem (k : ℕ) (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ)
    (c : ℕ) : PromiseProblem SIHInstance :=
  hamPromise (SIHInstance.Valid k c) (fun x => x.n) (fun x => sihHam k (hfam x.n) x)
    (fun x => (x.a.value : ℝ)) (fun x => (x.b.value : ℝ)) (fun _ hx => hx.2.2.lt)

end SingleInteraction


