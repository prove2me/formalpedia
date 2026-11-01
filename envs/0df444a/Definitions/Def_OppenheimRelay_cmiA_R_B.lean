-- Prove2me | Definitions.Def_OppenheimRelay_cmiA_R_B
-- name    : OppenheimRelay_cmiA_R_B
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:27:36.503505+00:00
-- url     : https://prove2.me/theorems/7babaeca-347f-4536-ac20-88aa93deb356
-- title:
--   Conditional mutual information $I(A:R\mid B)$ of the relay source
-- statement:
--   For a vector $\psi$ on the relay source $R\times(A\times(C\times B))$, the paper defines
--   $$
--   I(A:R\mid B) = S(A\mid B)+S(R\mid B)-S(AR\mid B), \qquad S(X\mid B) = S(XB)-S(B).
--   $$
--   Expanding the three conditional entropies, the terms in $S(B)$ cancel down to one, and
--   $$
--   I(A:R\mid B) = S(AB)+S(RB)-S(ARB)-S(B).
--   $$
--   This is the expression the definition computes, with $S$ the von Neumann entropy in bits of the corresponding reduced state of $|\psi\rangle\langle\psi|$.
--
--   Half of it is the optimal rate $Q^{C\to B}$ of qubits sent from the relay to Bob.
--
--   **Formalization Note** Each entropy is the published `vnEntropy` (base-2 logarithm, $0\log 0 = 0$) of the marginal of $|\psi\rangle\langle\psi|$ computed by the published `subsystemEntropy`, which traces out the complementary registers.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraph "If all that is available…" (I(A : R|B) = S(A|B) + S(R|B) − S(AR|B), S(A|B) = S(AB) − S(B))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelaySource

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

/-- **I(A:R|B)**, in bits. Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "If all that is available…":
`I(A : R|B) = S(A|B) + S(R|B) − S(AR|B)` with `S(A|B) = S(AB) − S(B)`. Expanding the three
conditional entropies, the terms in S(B) leave `I(A:R|B) = S(AB) + S(RB) − S(ARB) − S(B)`. -/
noncomputable def cmiA_R_B {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    (psi : EuclideanSpace ℂ (RelaySource A C B R)) : ℝ :=
  subsystemEntropy (pureDensity psi) (fun p => (p.2.1, p.2.2.2)) (fun p => (p.1, p.2.2.1)) +
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.2.2)) (fun p => (p.2.1, p.2.2.1)) -
    subsystemEntropy (pureDensity psi) (fun p => (p.1, p.2.1, p.2.2.2)) (fun p => p.2.2.1) -
    subsystemEntropy (pureDensity psi) (fun p => p.2.2.2) (fun p => (p.1, p.2.1, p.2.2.1))

end OppenheimRelay


