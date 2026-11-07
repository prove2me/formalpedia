-- Prove2me | Definitions.Def_QiOPoQ_fig6Prove
-- name    : QiOPoQ_fig6Prove
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:51.896533+00:00
-- url     : https://prove2.me/theorems/bc885774-22fe-4512-bd2f-553d8773b35b
-- title:
--   Figure 6: Prove
-- statement:
--   $\mathrm{Prove}(1^\lambda,\mathsf{chall})$ parses $\mathsf{chall}=(\hat C_1,\dots,\hat C_t,y)$, evaluates each $\hat C_i$ on $|0\rangle$, measures its logical output qubit in the computational basis, and outputs $\mathsf{resp}=(b'_1,\dots,b'_t)$.
--
--   **Formalization Note** The definition is the classical part: the list $(\hat C_1,\dots,\hat C_t)$ of descriptions handed to the quantum machine of `qptExpect`, which runs each circuit on all zeros and concatenates the measured output in the order $1,\dots,t$. An unparsable challenge gives the empty list.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 6, p.21

import Mathlib
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- **Figure 6, Prove** (p.21): "Parse the challenge chall = (Ĉ_1, . . . , Ĉ_t, y). Evaluate each
Ĉ_i on |0⟩, measure its logical output qubit in the computational basis, and output the
resulting string resp = (b′_1, . . . , b′_t)." The classical part: the list `(Ĉ_1, …, Ĉ_t)` of
circuit descriptions handed to the quantum machine (`qptExpect`), which runs each on `|0…0⟩`
and outputs the measured output qubits in the order `1, …, t`. An unparsable challenge gives the
empty list. -/
noncomputable def fig6Prove (t : ℕ → ℕ) (n : ℕ) (chall : Str) : Str :=
  match untuple chall with
  | some l => tup (l.take (t n))
  | none => tup []

end QiOPoQ


