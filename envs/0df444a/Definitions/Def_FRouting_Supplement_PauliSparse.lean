-- Prove2me | Definitions.Def_FRouting_Supplement_PauliSparse
-- name    : FRouting_Supplement_PauliSparse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:21:04.642751+00:00
-- url     : https://prove2.me/theorems/5b8e6533-92cf-4378-bb12-e3a10cd24cc9
-- title:
--   Pauli coefficients and $(q,s)$-Pauli-sparse operators
-- statement:
--   Let $\mathrm{Pauli}_q=\{I,X,Y,Z\}^{\otimes q}$. Every operator $U$ on $q$ qubits expands as
--   $$U=\sum_{P\in\mathrm{Pauli}_q}\widehat U(P)\,P,\qquad \widehat U(P)=2^{-q}\operatorname{tr}(UP).$$
--   $U$ is **$(q,s)$-Pauli-sparse** if its Pauli spectrum has support size at most $s$:
--   $$\bigl|\{P\in\mathrm{Pauli}_q:\widehat U(P)\neq0\}\bigr|\le s.$$
--
--   This is the resource restriction of §7; Theorem 7.10 applies it to the unitaries of quantum circuits.
--
--   **Formalization Note** The Pauli strings and coefficients are the published `UnitalMIP.pauliString` and `UnitalMIP.pauliCoeff`, whose labels $(a,b)\in\mathbb F_2^2$ give $i^{ab}X^aZ^b$ (that is $I, X, Z, Y$) and whose coefficient is $2^{-q}\operatorname{tr}(P^\dagger U)=2^{-q}\operatorname{tr}(UP)$, as Pauli strings are Hermitian. The definition is stated for any operator on $q$ qubits; unitarity comes from where it is applied.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), §7.1 and Definition 7.1, p.31

import Definitions.Def_UnitalMIP_pauliString

set_option autoImplicit false

open Matrix

namespace FRouting.Supplement

open scoped Classical in
/-- **`(q, s)`-Pauli-sparse.** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held
copy, sha256 4a327f29…), Definition 7.1, p.31: "A unitary U is (q, s)-Pauli-sparse if U acts on q qubits
and its Pauli spectrum has support size at most s, namely |Supp(Û)| ≤ s", where (p.31)
`U = ∑_{P ∈ Pauli_q} Û(P) P` with `Û(P) = 2^{-q} tr(UP)`.

**Formalization Note** The Pauli strings and coefficients are the published `UnitalMIP.pauliString` and
`UnitalMIP.pauliCoeff`: labels `(a, b) ∈ 𝔽₂²` give `i^{ab} X^a Z^b`, i.e. `I, X, Z, Y`, and
`pauliCoeff U α = 2^{-q} tr(P_α† U) = 2^{-q} tr(U P_α)` since Pauli strings are Hermitian, so the support
is the paper's. `q` is the index type `Fin q → Fin 2`; unitarity comes from where the notion is applied. -/
def IsPauliSparse {q : ℕ} (U : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ) (s : ℕ) : Prop :=
  (Finset.univ.filter fun α : Fin q → Fin 2 × Fin 2 => UnitalMIP.pauliCoeff U α ≠ 0).card ≤ s

end FRouting.Supplement


