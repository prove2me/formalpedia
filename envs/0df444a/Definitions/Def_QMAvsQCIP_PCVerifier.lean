-- Prove2me | Definitions.Def_QMAvsQCIP_PCVerifier
-- name    : QMAvsQCIP_PCVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:09.892169+00:00
-- url     : https://prove2.me/theorems/a84fe7c2-4a6f-4573-8e80-e022bd82c044
-- title:
--   Public-coin verifier with queries after the last reply
-- statement:
--   A **public-coin classical query verifier** with $R$ rounds and $\ell$-bit messages sends, in each round $j$, a fresh uniformly random string $a_j\in\{0,1\}^\ell$ and receives a reply $b_j$; it uses no other randomness. After the last reply it runs a query-only decision tree on the transcript $(a,b)$: all of its oracle queries come after the last prover reply.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 5, p.23; Lemma 3, p.23

import Definitions.Def_QMAvsQCIP_CTree_RoundsLE

set_option autoImplicit false

namespace QMAvsQCIP

/-- A **public-coin classical query verifier with all queries after the last prover reply**,
oracle domain `Z`, `R` rounds of `ℓ`-bit messages: in round `j` it sends a fresh uniformly random
`a_j ∈ {0,1}^ℓ` and receives the reply `b_j`; it uses no other randomness, and after the last
reply it runs the query-only decision tree `dec a b` (no further messages) on the transcript
`(a, b)`. Its acceptance probability is `pcAccept`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 5, p.23 (PDF p.26): "A classical verifier is public-coin if each
of its messages before the final decision is a fresh uniform random string and it uses no other
randomness, so its final computation is deterministic given the transcript and oracle. As in the
query complexity model, we fix round counts and message lengths by padding"; Lemma 3: "a
public-coin protocol (P′, V′) … with deterministic P′ and all verifier queries after the last
prover reply". -/
structure PCVerifier (Z : Type) (ℓ : ℕ) where
  /-- number of rounds -/
  R : ℕ
  /-- the decision tree on the verifier messages `a` and the prover replies `b` -/
  dec : (Fin R → Fin ℓ → Bool) → (Fin R → Fin ℓ → Bool) → CTree Z ℓ
  dec_noSends : ∀ a b, CTree.RoundsLE 0 (dec a b)

end QMAvsQCIP


