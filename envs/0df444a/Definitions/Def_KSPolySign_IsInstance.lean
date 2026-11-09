-- Prove2me | Definitions.Def_KSPolySign_IsInstance
-- name    : KSPolySign_IsInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:30:30.843144+00:00
-- url     : https://prove2.me/theorems/90fc3896-8305-4ec9-9375-92d727f0bcc6
-- title:
--   Maintained instance: PSD rank-one matrices with $\sum_i C_i^2\preceq I$
-- statement:
--   A family $C_1,\dots,C_k\in\mathbb C^{n\times n}$ is a **maintained instance** when every $C_i$ is positive semidefinite of rank exactly one and
--   $$\sum_{i=1}^k C_i^2 \preceq I.$$
--   The normalized inputs of Lemma 3.1 are such a family, and so are the retained matrices on every face of the algorithm. The fixed Hermitian matrix $F$ of Definition 3.5 is a separate argument.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Maintained instance.** A family `(C_i)` of nonzero positive semidefinite rank-one matrices with
`∑_i C_i² ⪯ I`. Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19): "Let I index nonzero positive semidefinite
rank-one matrices (C_i)_{i∈I} with ∑_{i∈I} C_i² ⪯ I".

**Formalization Note** "Nonzero of rank one" is `rank = 1`. The fixed Hermitian matrix `F` of
Definition 3.5 is a separate argument of every statement. -/
def IsInstance {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, (C i).PosSemidef ∧ (C i).rank = 1) ∧ (1 - ∑ i, C i * C i).PosSemidef

end KSPolySign


