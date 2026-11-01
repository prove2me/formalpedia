-- Prove2me | Definitions.Def_OppenheimRelay_mergeMiA_R
-- name    : OppenheimRelay_mergeMiA_R
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:37.199889+00:00
-- url     : https://prove2.me/theorems/7a6a0ea9-a66a-4dd5-b6a0-aa45c9d56462
-- title:
--   Mutual information $I(A:R)$ of a merging source
-- statement:
--   For a vector $\phi$ on the merging source $R\times(A\times B)$,
--   $$
--   I(A:R) = S(A)+S(R)-S(AR),
--   $$
--   with $S$ the von Neumann entropy in bits of the reduced states of $|\phi\rangle\langle\phi|$. $nI(A:R)$ is the number of classical bits state merging uses, and $nI(A:R)/2$ the number of qubits coherent merging sends.
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraphs "If all that is available…" (definition of mutual information) and "Now, to perform merging…"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_MergeSource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:R)** of a merging source, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…"
(`I(C : R) = S(C) + S(R) − S(CR)`, here on the registers A and R). Expansion:
`I(A:R) = S(A) + S(R) − S(AR)`. -/
noncomputable def mergeMiA_R {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (phi : EuclideanSpace ℂ (MergeSource A B R)) : ℝ :=
  subsystemEntropy (pureDensity phi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
    subsystemEntropy (pureDensity phi) (fun p => p.1) (fun p => p.2) -
    subsystemEntropy (pureDensity phi) (fun p => (p.1, p.2.1)) (fun p => p.2.2)

end OppenheimRelay


