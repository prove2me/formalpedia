-- Prove2me | Definitions.Def_SingleInteraction_tupleTerm
-- name    : SingleInteraction_tupleTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:27.878954+00:00
-- url     : https://prove2.me/theorems/6e66fe3c-cb2d-415b-b78b-813740f99193
-- title:
--   The term $h_e$ of a tuple given as a list of qubit indices
-- statement:
--   For an $n$-qubit register, a $k$-qubit operator $h$ and a tuple $e=(v_1,\dots,v_k)$ given as a list of qubit indices in $\{0,\dots,n-1\}$, the term $h_e$: $h$ applied to the qubits $v_1,\dots,v_k$ in this order, identity elsewhere.
--
--   **Formalization Note** If one of the first $k$ entries is not a qubit index, the term is $0$; valid instances never have such tuples.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, p.30

import Mathlib
import Definitions.Def_SingleInteraction_onTuple

namespace SingleInteraction

/-- The term `h_e` of an instance whose ordered tuple `e = (v₁, …, v_k)` is given as a list of qubit
indices of an `n`-qubit register (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, p.30: "let `h_e` denote the application of
`h` to the ordered tuple `e`, acting as the identity on all remaining qubits").

**Formalization Note** When the first `k` entries of the list are qubit indices `< n`, the term is
`onTuple h e` with `e j` the `j`-th entry (so the `j`-th tensor factor of `h` acts on qubit `v_{j+1}`);
otherwise it is `0`. Instance validity (`SIHInstance.Valid`) requires length `k`, entries `< n` and
pairwise distinct entries, so on valid instances the first case always applies. -/
def tupleTerm (n k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ) (l : List ℕ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  if hl : ∀ j : Fin k, l.getD j 0 < n then onTuple h (fun j => ⟨l.getD j 0, hl j⟩) else 0

end SingleInteraction


