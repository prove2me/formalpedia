-- Prove2me | Definitions.Def_QSDMixing_GU_IsPOVM
-- name    : QSDMixing_GU_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:30.156082+00:00
-- url     : https://prove2.me/theorems/1f0acde3-38e0-4454-8a6d-421a90f70054
-- title:
--   POVM on $\ell^2(K)$ with finitely many outcomes
-- statement:
--   A family $(M_i)_{i\in I}$ of bounded operators on $\ell^2(K)$, with $I$ finite, is a POVM when every $M_i$ is positive and
--
--   $$
--   \sum_{i\in I}M_i=\mathbb I.
--   $$
--
--   These are the measurements over which the optimal success probabilities are taken.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eqs. (2), (4), pp.3–4

import Mathlib
import Definitions.Def_GaussTesting_Ell2

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- A POVM on `ℓ²(K)` with finitely many outcomes `I`: positive operators summing to the identity.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (2), p.3, and eq. (4), p.4: the measurements `{Π_i}`. -/
def IsPOVM {K I : Type} [Fintype I] (M : I → Ell2 K →L[ℂ] Ell2 K) : Prop :=
  (∀ i, (M i).IsPositive) ∧ ∑ i, M i = 1

end QSDMixing.GU


