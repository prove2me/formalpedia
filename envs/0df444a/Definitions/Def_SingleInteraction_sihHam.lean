-- Prove2me | Definitions.Def_SingleInteraction_sihHam
-- name    : SingleInteraction_sihHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:32.382071+00:00
-- url     : https://prove2.me/theorems/a8ccd0af-eb05-4496-ae69-5482be337868
-- title:
--   The Hamiltonian $H=\sum_{e\in L}h_e$
-- statement:
--   The Hamiltonian of a single-interaction input on $n$ qubits,
--
--   $$H=\sum_{e\in L}h_e,$$
--
--   one unweighted copy of the fixed interaction $h$ on each ordered tuple of $L$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, p.30

import Mathlib
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_tupleTerm

namespace SingleInteraction

/-- The Hamiltonian `H = Σ_{e∈L} h_e` of a single-interaction input on `n` qubits (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…),
Definition 31, p.30, "Define `H = Σ_{e∈L} h_e`").

**Formalization Note** The sum runs over the list of tuples; on valid inputs the tuples are pairwise
distinct, so this is the sum over the set `L`. Each tuple contributes one unweighted copy of `h`. -/
noncomputable def sihHam (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (x : SIHInstance) :
    Matrix (Fin x.n → Fin 2) (Fin x.n → Fin 2) ℂ :=
  (x.tuples.map (tupleTerm x.n k h)).sum

end SingleInteraction


