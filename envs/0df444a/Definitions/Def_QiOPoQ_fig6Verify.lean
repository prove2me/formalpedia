-- Prove2me | Definitions.Def_QiOPoQ_fig6Verify
-- name    : QiOPoQ_fig6Verify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:47.517314+00:00
-- url     : https://prove2.me/theorems/683c0eca-4d9f-4b91-b9d0-d9b749e70fe7
-- title:
--   Figure 6: Verify
-- statement:
--   $\mathrm{Verify}(1^\lambda,\mathsf{chall},\mathsf{resp})$ parses the challenge as $(\hat C_1,\dots,\hat C_t,y)$ and the response as $\mathsf{resp}\in\{0,1\}^t$, and accepts if and only if $f(\mathsf{resp})=y$.
--
--   **Formalization Note** To match the syntax of Definition 3.3, it also receives the coins $r$, which it does not use. A challenge with the wrong number of components, or a response of length other than $t$, is rejected.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Figure 6, p.21

import Mathlib
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- **Figure 6, Verify** (p.21): "Parse the challenge as chall = (Ĉ_1, . . . , Ĉ_t, y) and the
response as resp ∈ {0, 1}^t. Accept if f(resp) = y and reject otherwise." The coins `r` are not
used. A challenge that does not parse as `t + 1` components, or a response of length `≠ t`, is
rejected. -/
noncomputable def fig6Verify (f : Str → Str) (t : ℕ → ℕ) (n : ℕ) (_r chall resp : Str) : Bool :=
  match untuple chall with
  | some l => decide (l.length = t n + 1 ∧ resp.length = t n ∧ l.getLast? = some (f resp))
  | none => false

end QiOPoQ


