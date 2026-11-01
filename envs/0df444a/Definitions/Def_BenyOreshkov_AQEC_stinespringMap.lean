-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_stinespringMap
-- name    : BenyOreshkov_AQEC_stinespringMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:05.712659+00:00
-- url     : https://prove2.me/theorems/65a38a99-3f5a-44a0-b1ac-9c1f0cdde1b2
-- title:
--   The channel $\rho\mapsto\mathrm{Tr}_K(W\rho W^\dagger)$ of an operator $W$ and its complement $\rho\mapsto\mathrm{Tr}_Y(W\rho W^\dagger)$
-- statement:
--   Let $X$, $Y$, $K$ be finite-dimensional Hilbert spaces and let $W : X \to Y \otimes K$ be a linear operator. It defines two maps on operators on $X$:
--   $$
--   \rho \mapsto \mathrm{Tr}_K\big(W\rho W^\dagger\big) \quad\text{(an operator on } Y\text{)},\qquad \rho \mapsto \mathrm{Tr}_Y\big(W\rho W^\dagger\big) \quad\text{(an operator on } K\text{)}.
--   $$
--   When $W$ is an isometry ($W^\dagger W = 1$), the first map is a quantum channel from $X$ to $Y$ in Stinespring form, with environment $K$, and the second is its complementary channel into the environment. This is how Bény and Oreshkov write every channel: $\mathcal N(\rho)=\mathrm{Tr}_E(V\rho V^\dagger)$ and $\widehat{\mathcal N}(\rho)=\mathrm{Tr}_B(V\rho V^\dagger)$, and a recovery channel as $\mathcal R(\rho)=\mathrm{Tr}_{\widetilde E}(U(\rho\otimes|0\rangle\langle 0|)U^\dagger)$, i.e. $W = U(\cdot\otimes|0\rangle)$.
--
--   **Formalization Note** $W$ is a matrix indexed by $(Y\times K)\times X$, output system first and environment second. $\mathrm{Tr}_K$ and $\mathrm{Tr}_Y$ are the partial traces `WildeQIT.partialTraceRight` and `WildeQIT.partialTraceLeft`. The maps are defined for every $W$; isometry or contraction conditions are imposed in the statements.
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Background and proof of Theorem 1, p. 2

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_partialTrace

open Matrix QAlgorithms WildeQIT

namespace BenyOreshkov.AQEC

/-- **The channel of an isometry and its complement.** Bény, Oreshkov, *General conditions for
approximate quantum error correction and near-optimal recovery channels*, arXiv:0907.5391v4,
§Background and proof of Theorem 1, p. 2: an operator `W : X → Y ⊗ K` defines the map
`ρ ↦ Tr_K(W ρ W†)` (the paper's `N(ρ) = Tr_E(VρV†)` and
`R(ρ) = Tr_Ẽ(U(ρ ⊗ |0⟩⟨0|)U†)` with `W = U(· ⊗ |0⟩)`).

**Formalization Note** `W` is a matrix `Matrix (Y × K) X ℂ`, the output system first and the
environment second; `Tr_K` is `WildeQIT.partialTraceRight`. The map is defined for every `W`;
it is a channel when `W` is an isometry (`Wᴴ * W = 1`). -/
def stinespringMap {X Y K : Type} [Fintype X] [Fintype K] (W : Matrix (Y × K) X ℂ) :
    Superop X Y :=
  fun ρ => partialTraceRight (W * ρ * Wᴴ)

/-- **The complementary map** `ρ ↦ Tr_Y(W ρ W†)` of the same operator `W : X → Y ⊗ K`,
arXiv:0907.5391v4, §Background, p. 2: "if instead of tracing out the environment after the
unitary interaction, we trace out the target system B, we obtain a channel N̂ which is said to be
complementary to N: N̂(ρ) = Tr_B(VρV†)".

**Formalization Note** `Tr_Y` (the first factor) is `WildeQIT.partialTraceLeft`. -/
def stinespringComp {X Y K : Type} [Fintype X] [Fintype Y] (W : Matrix (Y × K) X ℂ) :
    Superop X K :=
  fun ρ => partialTraceLeft (W * ρ * Wᴴ)

end BenyOreshkov.AQEC


