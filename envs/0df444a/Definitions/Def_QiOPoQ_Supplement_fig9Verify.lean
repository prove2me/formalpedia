-- Prove2me | Definitions.Def_QiOPoQ_Supplement_fig9Verify
-- name    : QiOPoQ_Supplement_fig9Verify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:54:54.400112+00:00
-- url     : https://prove2.me/theorems/53725fc1-7d33-48b6-9a12-1ed52d7fa560
-- title:
--   Figure 9: the public verifier
-- statement:
--   Verify of Figure 9 rejects if $b'$ is not a $\lambda$-bit string; otherwise it outputs the unique $b\in\{0,1\}$ with $g_\lambda(b')=y_b$, and rejects if there is no unique such bit. It uses neither $C$ nor a secret state.
--
--   **Formalization Note** A challenge that does not parse as $\lambda+2$ components is rejected.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 9, p.28

import Mathlib
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

open Classical in
/-- **Figure 9, Verify.** Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256 fe2f9210…),
Figure 9, p.28: "Verify(1^λ, chall, b′): Reject if b′ is not a λ-bit vector. Otherwise output the
unique b ∈ {0, 1} for which g_λ(b′) = y_b, and reject if there is no unique such bit."

The challenge is parsed as `tup [Ĉ_0, …, Ĉ_{λ−1}, y_0, y_1]` (a challenge with another number of
components is rejected); `⊥` is `none`. -/
noncomputable def fig9Verify (g : Str → Str) (n : ℕ) (chall resp : Str) : Option Bool :=
  match untuple chall with
  | some l =>
    if l.length = n + 2 ∧ resp.length = n then
      if g resp = l.getD n [] ∧ g resp ≠ l.getD (n + 1) [] then some false
      else if g resp = l.getD (n + 1) [] ∧ g resp ≠ l.getD n [] then some true
      else none
    else none
  | none => none

end QiOPoQ.Supplement


