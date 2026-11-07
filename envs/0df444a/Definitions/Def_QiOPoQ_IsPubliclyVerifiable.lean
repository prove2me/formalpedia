-- Prove2me | Definitions.Def_QiOPoQ_IsPubliclyVerifiable
-- name    : QiOPoQ_IsPubliclyVerifiable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:53.436011+00:00
-- url     : https://prove2.me/theorems/61867c04-b807-4766-8d4b-01083f961ce8
-- title:
--   Definition 3.4: publicly verifiable proof of quantumness
-- statement:
--   A two-message proof of quantumness is **publicly verifiable** if there is a deterministic classical polynomial-time algorithm PublicVerify such that, for every $r$ of length $\ell(\lambda)$, the honestly generated $\mathsf{chall}=\mathrm{Challenge}(1^\lambda;r)$ and every response $\mathsf{resp}$,
--
--   $$
--   \mathrm{Verify}(1^\lambda,r,\mathsf{chall},\mathsf{resp})=\mathrm{PublicVerify}(1^\lambda,\mathsf{chall},\mathsf{resp}).
--   $$
--
--   After generating the challenge, the verifier retains no secret state needed to check a transcript.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.4, p.15

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- **Definition 3.4 (Publicly verifiable Proof of Quantumness).** arXiv:2609.40289,
Definition 3.4, p.15: "Π = (Challenge, Prove, Verify), is publicly verifiable if there is a
deterministic classical polynomial-time algorithm PublicVerify such that, for every r, every
honestly generated chall = Challenge(1^λ; r), and every response resp,
Verify(1^λ, r, chall, resp) = PublicVerify(1^λ, chall, resp)." -/
def IsPubliclyVerifiable (ℓ : Polynomial ℕ) (chal : ℕ → Str → Str)
    (verify : ℕ → Str → Str → Str → Bool) : Prop :=
  ∃ pv : ℕ → Str → Str → Bool,
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ n (c s : Str), g (tup [unary n, c, s]) = bitStr (pv n c s)) ∧
    ∀ n (r s : Str), r.length = ℓ.eval n → verify n r (chal n r) s = pv n (chal n r) s

end QiOPoQ


