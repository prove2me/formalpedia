-- Prove2me | Definitions.Def_OppenheimRelay_miA_RB
-- name    : OppenheimRelay_miA_RB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:29.619242+00:00
-- url     : https://prove2.me/theorems/4bfb0c93-9893-4728-8923-fd69b3e924b8
-- title:
--   Mutual information $I(A:RB)$ of the relay source
-- statement:
--   For a vector $\psi$ on the relay source $R\times(A\times(C\times B))$, the quantum mutual information between $A$ and $RB$ is
--   $$
--   I(A:RB) = S(A)+S(RB)-S(ARB),
--   $$
--   where $S(X)$ is the von Neumann entropy, in bits, of the reduced state of $|\psi\rangle\langle\psi|$ on the registers $X$. This is the paper's definition $I(C:R)=S(C)+S(R)-S(CR)$, applied to the registers $A$ and $RB$.
--
--   Half of it is the rate $Q^{A\to C}$ of qubits Alice sends to Charlie in the relay protocol (p.2, step 1 and the rate display).
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "If all that is available…" (definition of I(C : R))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:RB)**, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…"
(mutual information `I(C : R) = S(C) + S(R) − S(CR)`, here on the registers A and RB); used at p.2,
step 1 and the rate display. Expansion: `I(A:RB) = S(A) + S(RB) − S(ARB)`, each entropy computed
from the marginal of `|ψ⟩⟨ψ|` on the named registers. -/
noncomputable def miA_RB {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => p.2.1) (fun p => (p.1, p.2.2)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.2)) (fun p => (p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1, p.2.2.2)) (fun p => p.2.2.1)

end OppenheimRelay


