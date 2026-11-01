-- Prove2me | Definitions.Def_OppenheimRelay_miA_C
-- name    : OppenheimRelay_miA_C
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:20.768194+00:00
-- url     : https://prove2.me/theorems/409992ad-0475-49da-bae6-b12653b77f38
-- title:
--   Mutual information $I(A:C)$ of the relay source
-- statement:
--   For a vector $\psi$ on the relay source $R\times(A\times(C\times B))$, the quantum mutual information between $A$ and $C$ is
--   $$
--   I(A:C) = S(A)+S(C)-S(AC),
--   $$
--   where $S(X)$ is the von Neumann entropy, in bits, of the reduced state of $|\psi\rangle\langle\psi|$ on the registers $X$. This is the paper's definition $I(C:R)=S(C)+S(R)-S(CR)$, applied to the registers $A$ and $C$.
--
--   Half of it is the rate at which the relay protocol extracts ebits between Alice and Charlie (p.2, step 1).
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "If all that is available…" (definition of I(C : R))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:C)**, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…"
(`I(C : R) = S(C) + S(R) − S(CR)`, here on the registers A and C); used at p.2, the protocol and
the rate display. Expansion: `I(A:C) = S(A) + S(C) − S(AC)`. -/
noncomputable def miA_C {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.1) (fun p => (p.1, p.2.1, p.2.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.2.1, p.2.2.1)) (fun p => (p.1, p.2.2.2))

end OppenheimRelay


