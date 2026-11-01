-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_IsComplementaryPair
-- name    : BenyOreshkov_AQEC_IsComplementaryPair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:12.310116+00:00
-- url     : https://prove2.me/theorems/63268fff-8618-468a-bf88-626f06374687
-- title:
--   Complementary channels $\mathcal N$, $\widehat{\mathcal N}$ given by one isometry
-- statement:
--   Let $A$, $B$, $E$ be finite-dimensional Hilbert spaces, $\mathcal N$ a map from operators on $A$ to operators on $B$ and $\widehat{\mathcal N}$ a map from operators on $A$ to operators on $E$. The pair is **complementary** if there is an isometry $V : A \to B\otimes E$ ($V^\dagger V = 1$) such that for every operator $\rho$ on $A$
--   $$
--   \mathcal N(\rho) = \mathrm{Tr}_E\big(V\rho V^\dagger\big),\qquad \widehat{\mathcal N}(\rho) = \mathrm{Tr}_B\big(V\rho V^\dagger\big).
--   $$
--   Then $\mathcal N$ is a channel and $\widehat{\mathcal N}$ is a channel *complementary* to it: tracing out the target system $B$ instead of the environment $E$ after the same isometric interaction. This is the hypothesis of Theorem 1 on both pairs $(\mathcal N,\widehat{\mathcal N})$ and $(\mathcal M,\widehat{\mathcal M})$.
--
--   **Formalization Note** One isometry gives both channels, so $\widehat{\mathcal N}$ is tied to $\mathcal N$. The environment $E$ is any finite type; it need not be of minimal dimension (the paper: "all complementary channels correspond to some choice of the orthonormal family of states $|i\rangle$ in the environment").
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Background, p. 2 (definition of the complementary channel, before Eq. (1))

import Definitions.Def_BenyOreshkov_AQEC_stinespringMap

open Matrix QAlgorithms WildeQIT

namespace BenyOreshkov.AQEC

/-- **Complementary channels.** Bény, Oreshkov, arXiv:0907.5391v4, §Background, p. 2: a channel
`N : A → B` is `N(ρ) = Tr_E(VρV†)` for an isometry `V : A → B ⊗ E`, and the channel
`N̂(ρ) = Tr_B(VρV†)` obtained from the same isometry is *complementary* to `N`.
`IsComplementaryPair N Nc` says that there is one isometry `V` giving both: `N = Tr_E(V · V†)`
and `Nc = Tr_B(V · V†)`.

**Formalization Note** The isometry is `V : Matrix (B × E) A ℂ` with `Vᴴ * V = 1`; the
environment `E` is any finite type (not required minimal). `N` traces out the second factor
(`partialTraceRight`), `Nc` the first (`partialTraceLeft`). Both channels are required to agree
with the isometry on every operator, so both are linear. -/
def IsComplementaryPair {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype E]
    (N : Superop A B) (Nc : Superop A E) : Prop :=
  ∃ V : Matrix (B × E) A ℂ, Vᴴ * V = 1 ∧ ∀ ρ, N ρ = stinespringMap V ρ ∧ Nc ρ = stinespringComp V ρ

end BenyOreshkov.AQEC


