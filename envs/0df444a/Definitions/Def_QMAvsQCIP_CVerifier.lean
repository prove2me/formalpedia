-- Prove2me | Definitions.Def_QMAvsQCIP_CVerifier
-- name    : QMAvsQCIP_CVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:40.152812+00:00
-- url     : https://prove2.me/theorems/5ce578bf-d981-415f-85bc-bba589100b60
-- title:
--   Randomized classical query verifier
-- statement:
--   A **randomized classical query verifier** with oracle domain $Z$ and $\ell$-bit messages tosses $k$ private fair coins $c\in\{0,1\}^k$ and then runs a classical interactive query algorithm depending on $c$. Its local computation is unrestricted; its rounds, queries and random bits are the counted resources.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 5, p.17; Lemma 3, p.23; Theorem 7, p.31

import Definitions.Def_QMAvsQCIP_CTree

set_option autoImplicit false

namespace QMAvsQCIP

/-- A **randomized classical query verifier** with oracle domain `Z` and `ℓ`-bit messages: it
tosses `k` fair coins `c ∈ {0,1}^k` and then runs the classical interactive query algorithm
`tree c`. Its acceptance probability is `cAccept`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 5, p.17 (PDF p.20): "Restricting the verifier to classical
queries and classical computation with polynomially many random bits gives IP^bb"; Lemma 3, p.23
(PDF p.26): "its bounds on rounds, communication, random bits, and the number and length of
queries"; Theorem 7, p.31 (PDF p.34): "a randomized classical verifier V′".

**Formalization Note.** Private coins: the prover sees only the messages. Local computation is
unrestricted. -/
structure CVerifier (Z : Type) (ℓ : ℕ) where
  /-- number of random bits -/
  k : ℕ
  /-- the algorithm run on coins `c` -/
  tree : (Fin k → Bool) → CTree Z ℓ

end QMAvsQCIP


