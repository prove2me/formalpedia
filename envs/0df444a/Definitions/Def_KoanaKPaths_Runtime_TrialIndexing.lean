-- Prove2me | Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
-- name    : KoanaKPaths_Runtime_TrialIndexing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T07:51:47.527149+00:00
-- url     : https://prove2.me/theorems/f9e7532f-b9c4-43bb-bb02-fe5da9416b4a
-- title:
--   Structural address identities for trial signs
-- statement:
--   This bundle contains the essential address identities for the first and later sketch-sign parts of the finite trial index. It exposes their natural-number offsets after the nk vertex-label signs. The indices a,b range over k sketch states, v over n vertices, and i over the k−1 later layers.
--
--   $$
--   j_1=nk+an+v,\qquad j_2=nk+kn+ik^2n+akn+bn+v.
--   $$
--
--   These structural lemmas align the canonical finite-product indexing with the arithmetic expressions compiled by the sign readers.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/TrialIndexing.lean; source snapshot SHA-256 72e568714e8e218d700c752db46d065fae1105d11f936be9f4852061622f675e.

import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main









lemma trialIndex_first {n k : ℕ} (a : Fin k) (v : Fin n) :
    (trialIndexEquiv n k (.inr (.inl (a,v)))).val=n*k+a.val*n+v.val := by
  change n*k+(v.val+n*a.val)=n*k+a.val*n+v.val
  ring

lemma trialIndex_later {n k : ℕ} (i : Fin (k-1)) (a b : Fin k) (v : Fin n) :
    (trialIndexEquiv n k (.inr (.inr (i,a,(b,v))))).val=
      n*k+k*n+i.val*(k*(k*n))+a.val*(k*n)+b.val*n+v.val := by
  change n*k+(k*n+((v.val+n*b.val)+(k*n)*a.val+(k*(k*n))*i.val))=_
  ring





end KoanaKPaths.Main

end


