-- Prove2me | Definitions.Def_NumberField_Completion_Finite
-- name    : NumberField_Completion_Finite
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/fca85224-7a25-5cd5-a173-5088b61fb534
-- title:
--   Local fields at finite places: finiteness, compactness, local compactness
-- statement:
--   Throughout, $K$ is a number field, $v$ a height-one prime of the ring of integers $\mathcal{O}_K$, $K_v =$ `v.adicCompletion K` the $v$-adic completion (a valued field with values in $\mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$) and $\mathcal{O}_v =$ `v.adicCompletionIntegers K` its valuation subring. The module registers the basic topological and finiteness facts about this situation as instances and lemmas.
--
--   [`NumberField.instFiniteResidueFieldAdicCompletionIntegers`](../def/NumberField_Completion_Finite.html#L23) asserts that the residue field of $\mathcal{O}_v$ is finite; it is obtained by transporting the finiteness of $\mathcal{O}_K/v$ (a nonzero ideal in a ring free of finite rank over $\mathbb{Z}$) along the ring isomorphism $\mathcal{O}_K/v \cong \mathcal{O}_v/\mathfrak{m}_v$ induced by $\mathcal{O}_K \to \mathcal{O}_v$. The same statement is then recorded for the residue field $\mathfrak{k}[K_v]$ of the valuation ring attached to the `Valued` structure on $K_v$. [`NumberField.instCompactSpaceAdicCompletionIntegers`](../def/NumberField_Completion_Finite.html#L32) asserts that $\mathcal{O}_v$ is a compact space; it cites [`Valued.WithZeroMulInt.integer_compactSpace`](../def/Mathlib_Topology_Algebra_Valued_WithZeroMulInt.html#L73), whose hypotheses here are completeness of $K_v$, the discrete-valuation-ring property and rank-one discreteness of its valuation, the finiteness of the residue field just established, and the surjectivity of the valuation of $K_v$ onto $\mathbb{Z}^{m0}$. [`NumberField.isCompactAdicCompletionIntegers`](../def/NumberField_Completion_Finite.html#L37) and [`NumberField.isOpenAdicCompletionIntegers`](../def/NumberField_Completion_Finite.html#L42) restate this compactness, and the openness of a valuation subring in a valued field, for $\mathcal{O}_v$ viewed as a subset of $K_v$.
--
--   From these, $K_v$ is shown to be weakly locally compact — each $x$ has the compact open neighbourhood $x + \mathcal{O}_v$ — and hence locally compact; second countability of $K_v$ is also available. Finally, [`Rat.adicCompletion.locallyCompactSpace`](../def/NumberField_Completion_Finite.html#L46) records local compactness of the $v$-adic completion of $\mathbb{Q}$ for a height-one prime $v$ of $\mathcal{O}_\mathbb{Q}$, deduced from its identification, as a homeomorphism and hence a closed embedding, with the corresponding field $\mathbb{Q}_p$.
--
--   **Relation to Mathlib.** Mathlib supplies the $v$-adic completion of a Dedekind domain's fraction field, its valuation subring and the residue-field machinery for valued fields; the finiteness, compactness and (weak) local compactness instances for number fields assembled here are the project's additions, built on the project's comparison of $\mathcal{O}_K/v$ with the residue field of $\mathcal{O}_v$ and on its compactness criterion for $\mathbb{Z}^{m0}$-valued fields.
--
--   **Where it is used.** These instances make $K_v$ a local field in the topological sense, so that the completions at finite places may be used as topological rings throughout the argument; they are prerequisites for the local analysis of Galois representations at finite places and are relied upon by a large part of the development.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/NumberField/Completion/Finite.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_Completion_Finite.lean

import Mathlib
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt
import Definitions.Def_Mathlib_LinearAlgebra_Countable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

example (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

open IsDedekindDomain

variable (v : HeightOneSpectrum (𝓞 K))

open IsLocalRing

instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued in
instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))

instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance
    (v.valuedAdicCompletion_surjective K)

lemma NumberField.isCompactAdicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_compactSpace]
  exact instCompactSpaceAdicCompletionIntegers K v

lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

instance Rat.adicCompletion.locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding
  |>.locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 K)) :
    WeaklyLocallyCompactSpace (v.adicCompletion K) where
  exists_compact_mem_nhds x :=
    open Pointwise in
    ⟨x +ᵥ ((v.adicCompletionIntegers K) : Set (v.adicCompletion K)),
      (isCompact_iff_compactSpace.mpr <| instCompactSpaceAdicCompletionIntegers K v).vadd x,
      ((isOpenAdicCompletionIntegers K v).vadd x).mem_nhds (Set.mem_vadd_set.mpr ⟨0, by simp⟩)⟩

instance (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := inferInstance

example (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance

end


