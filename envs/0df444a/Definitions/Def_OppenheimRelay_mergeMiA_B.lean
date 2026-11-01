-- Prove2me | Definitions.Def_OppenheimRelay_mergeMiA_B
-- name    : OppenheimRelay_mergeMiA_B
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:29.997581+00:00
-- url     : https://prove2.me/theorems/4545aed5-4a18-41f2-a6c3-9544c66ac83c
-- title:
--   Mutual information $I(A:B)$ of a merging source
-- statement:
--   For a vector $\phi$ on the merging source $R\times(A\times B)$,
--   $$
--   I(A:B) = S(A)+S(B)-S(AB),
--   $$
--   with $S$ the von Neumann entropy in bits of the reduced states of $|\phi\rangle\langle\phi|$. $nI(A:B)/2$ is the number of ebits the two parties share at the end of coherent merging.
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraphs "If all that is available…" (definition of mutual information) and "Now, to perform merging…"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_MergeSource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:B)** of a merging source, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…"
(`I(C : R) = S(C) + S(R) − S(CR)`, here on the registers A and B). Expansion:
`I(A:B) = S(A) + S(B) − S(AB)`. -/
noncomputable def mergeMiA_B {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (phi : EuclideanSpace ℂ (MergeSource A B R)) : ℝ :=
  subsystemEntropy (pureDensity phi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
    subsystemEntropy (pureDensity phi) (fun p => p.2.2) (fun p => (p.1, p.2.1)) -
    subsystemEntropy (pureDensity phi) (fun p => p.2) (fun p => p.1)

end OppenheimRelay


