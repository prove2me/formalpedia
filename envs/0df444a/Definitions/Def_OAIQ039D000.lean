-- Prove2me | Definitions.Def_OAIQ039D000
-- name    : OAIQ039D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:40:42.280897+00:00
-- url     : https://prove2.me/theorems/0bf983d8-eb53-43bc-a0bf-bfa9577aa1c5
-- title:
--   Definitions bundle OAIQ039D000 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle added to the split of OpenAI's proof of `OAI.Kadison.uniform_commutator` (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** Three abbreviations, each the verbatim term of one side of an equation in OpenAI's Lean:
--
--   - `OAI.Kadison.TracialSequence.doubleEmbeddingLeft τ ω M hconst hτ hM hone x` is the left side of OpenAI's `double_embedding`: the vector `VectorGNS.embedding … (originalEmbedding … x)` of `boundedSubspace τ ω`.
--   - `OAI.Kadison.TracialSequence.doubleCompressionLeft τ ω M hconst hτ hM hone T x` and `doubleCompressionRight τ ω M hconst hτ hM hone T x` are the two sides of OpenAI's `double_compression_preserves`: `VectorGNS.compression … (compressed τ ω T) (originalEmbedding … x)` and `originalEmbedding … (T x)`.
--
--   **Why.** Written out, the statements of `double_embedding` and `double_compression_preserves` have types of about $1.3 \cdot 10^9$ and $2.6 \cdot 10^9$ nodes when counted without sharing (nested instance arguments of the GNS completions). Lean 4.33 takes 100–180 s to write a module whose declaration has such a type, so their statement modules cannot be built within the platform's 300 s. With these names the restated lemmas `OAI.Kadison.TracialSequence.double_embedding_small` and `OAI.Kadison.TracialSequence.double_compression_preserves_small` have small types. Each abbreviation unfolds to OpenAI's term by definition.
--
--   **Imports.** The bundle `OAIQ039C072` of this split, with the same `attribute [-instance]` lines as the statements it restates.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); terms from the statements of OAI.Kadison.TracialSequence.double_embedding and double_compression_preserves in lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C072

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor FreeBlocks

abbrev doubleEmbeddingLeft {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1) (x : τ.GNS) :=
  VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
    (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))
    (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
      (constantHom τ ω M hconst) (constant_trace τ ω M hconst) x)

abbrev doubleCompressionLeft {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :=
  VectorGNS.compression (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω) (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω)) (compressed τ ω T)
    (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
      (constantHom τ ω M hconst) (constant_trace τ ω M hconst) x)

abbrev doubleCompressionRight {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :=
  originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
    (constantHom τ ω M hconst) (constant_trace τ ω M hconst) (T x)

end Kadison.TracialSequence

end

end OAI

end


