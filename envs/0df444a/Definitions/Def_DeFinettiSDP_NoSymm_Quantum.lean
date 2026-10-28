-- Prove2me | Definitions.Def_DeFinettiSDP_NoSymm_Quantum
-- name    : DeFinettiSDP_NoSymm_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:20.116927+00:00
-- url     : https://prove2.me/theorems/c1e11184-9af3-4c22-b696-26fea5cdfdaa
-- title:
--   §2.1, §2.4 and Lemma D.1 — measurements, two-designs and distortion
-- statement:
--   A finite **measurement** on a $d_B$-dimensional system is a family $(M_z)_{z=1}^t$ of positive semidefinite matrices satisfying $\sum_z M_z=I$. Measuring the $B$ part of an operator $\xi_{AB}$ leaves $A$ untouched and records $z$ in a diagonal classical register:
--
--   $$
--   (I_A\otimes M_B)(\xi_{AB})=\sum_z \operatorname{Tr}_B[(I_A\otimes M_z)\xi_{AB}]\otimes |z\rangle\langle z|.
--   $$
--
--   A state **two-design** consists of normalized rank-one projectors $P_z$ with $t^{-1}\sum_z P_z\otimes P_z=2P^{\mathrm{sym}}/[d_B(d_B+1)]$. Its measurement has effects $(d_B/t)P_z$. For any fixed measurement, its side-information distortion is the supremum of $\|\xi\|_1/\|(I_A\otimes M_B)(\xi)\|_1$ over Hermitian $\xi$ with both partial traces zero and over all finite dimensions of $A$. Equation (10) defines $f(B\mid\cdot)$ as the infimum of these distortions over measurements.
--
--   These definitions distinguish the optimal distortion from the distortion of a particular measurement and supply the objects in Theorem 2.5 and Lemma D.1.
--
--   **Formalization Note** Distortions are extended nonnegative real numbers; a zero measured norm for nonzero input gives $+\infty$. The symmetric projector is $(I+F)/2$, where $F$ swaps the two $B$ factors. A nonempty design outcome set is required by statements using the design.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §2.1 p. 4; equation (10) p. 6; Lemma D.1 p. 29

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems

namespace DeFinettiSDP.NoSymm

open Matrix
open scoped Kronecker ComplexOrder

/-- Apply a measurement to the second part of a bipartite operator, retaining the first
part and writing the outcome in a classical diagonal register (§2.1, p. 4). -/
def measB {dA dB t : ℕ} (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA × Fin t) (Fin dA × Fin t) ℂ :=
  fun (a, z) (a', z') =>
    if z = z' then ∑ b, ∑ b', M z b' b * ξ (a, b) (a', b') else 0

/-- Swap operator on B ⊗ B (§2.1, p. 3). -/
def swapMat (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun (i, j) (k, l) => if i = l ∧ j = k then 1 else 0

end DeFinettiSDP.NoSymm


