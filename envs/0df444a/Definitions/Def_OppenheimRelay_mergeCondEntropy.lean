-- Prove2me | Definitions.Def_OppenheimRelay_mergeCondEntropy
-- name    : OppenheimRelay_mergeCondEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:53.212693+00:00
-- url     : https://prove2.me/theorems/cbf95c7e-9e88-4b06-9c27-318aab338c3c
-- title:
--   Conditional entropy $S(A\mid B)$ of a merging source
-- statement:
--   For a vector $\phi$ on the merging source $R\times(A\times B)$, the conditional entropy is
--   $$
--   S(A\mid B) = S(AB)-S(B),
--   $$
--   with $S$ the von Neumann entropy in bits of the reduced states of $|\phi\rangle\langle\phi|$.
--
--   $nS(A\mid B)$ is the number of ebits state merging consumes (produces, when negative).
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "If all that is available…" ("S(A|B) the conditional entropy defined as S(AB) − S(B)") and paragraph "We will show that redistribution uses…"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_MergeSource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **S(A|B)** of a merging source, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…":
"S(A|B) the conditional entropy defined as S(AB) − S(B)". -/
noncomputable def mergeCondEntropy {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (phi : EuclideanSpace ℂ (MergeSource A B R)) : ℝ :=
  subsystemEntropy (pureDensity phi) (fun p => p.2) (fun p => p.1) -
    subsystemEntropy (pureDensity phi) (fun p => p.2.2) (fun p => (p.1, p.2.1))

end OppenheimRelay


