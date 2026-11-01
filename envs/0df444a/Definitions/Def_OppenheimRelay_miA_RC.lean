-- Prove2me | Definitions.Def_OppenheimRelay_miA_RC
-- name    : OppenheimRelay_miA_RC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:36.361987+00:00
-- url     : https://prove2.me/theorems/16475311-c671-4592-bca9-2f9f10792b08
-- title:
--   Mutual information $I(A:RC)$ of the relay source
-- statement:
--   For a vector $\psi$ on the relay source $R\times(A\times(C\times B))$, the quantum mutual information between $A$ and $RC$ is
--   $$
--   I(A:RC) = S(A)+S(RC)-S(ARC),
--   $$
--   where $S(X)$ is the von Neumann entropy, in bits, of the reduced state of $|\psi\rangle\langle\psi|$ on the registers $X$. This is the paper's definition $I(C:R)=S(C)+S(R)-S(CR)$, applied to the registers $A$ and $RC$.
--
--   The paper also writes it $I(A:CR)$. Half of it is the qubit cost of a naive coherent merging of $A$ to Bob that treats $C$ as part of the reference (p.1, "A naive application of coherent-merging…").
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "If all that is available…" (definition of I(C : R))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:RC)**, in bits (the paper also writes I(A:CR)). Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph
"If all that is available…" (`I(C : R) = S(C) + S(R) − S(CR)`, here on the registers A and RC);
used at p.1 ("A naive application of coherent-merging…") and p.2, step 3. Expansion:
`I(A:RC) = S(A) + S(RC) − S(ARC)`. -/
noncomputable def miA_RC {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.1)) (fun p => (p.2.1, p.2.2.2)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1, p.2.2.1)) (fun p => p.2.2.2)

end OppenheimRelay


