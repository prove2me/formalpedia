-- Prove2me | Definitions.Def_CompNonlocal_Certificate_prepProb
-- name    : CompNonlocal_Certificate_prepProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:15.512274+00:00
-- url     : https://prove2.me/theorems/a715a135-eb11-4160-bf3c-906269b93c02
-- title:
--   Transcript probabilities of the §8.1 preparation
-- statement:
--   $\Pr[T=(x,z)]=\Pr[X=x]\cdot\operatorname{Tr}\tilde\zeta_{x,z}$: the sender sends $x$, the receiver's complete record is $z$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35 and Lemma 11, p.37

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_questionProb
import Definitions.Def_CompNonlocal_Certificate_prepared

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The probability of the transcript `t = (x, z)` of the §8.1 preparation: the sender sends `x`
(probability `Pr[X = x]`), the receiver's complete record is `z` (probability the trace of the
unnormalized prepared state). Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35 and
Lemma 11, p.37 ("For every transcript t = (x, a) of positive probability"). -/
noncomputable def Certificate.prepProb (c : Certificate) (κ : ℕ) (x : Str)
    (z : Bits (c.A κ).width) : ℝ :=
  c.questionProb κ x * (c.prepared κ x z).trace.re

end CompNonlocal


