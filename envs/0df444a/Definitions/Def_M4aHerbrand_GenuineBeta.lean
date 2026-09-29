-- Prove2me | Definitions.Def_M4aHerbrand_GenuineBeta
-- name    : M4aHerbrand_GenuineBeta
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/9f899a4c-71c1-5d44-83d3-fff766dde166
-- title:
--   The adelic conorm map between adele rings of number fields
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra. Since `AdeleRing (𝓞 K) K` is the product of the infinite and the finite adele ring, a ring homomorphism $\mathbb{A}_K \to \mathbb{A}_L$ may be given by a pair of maps, and `genuineβ K L` is exactly such a pair: on the archimedean factor it is the conorm attached to the infinite-place datum `genuineInfinitePlaceData`, and on the non-archimedean factor it is `finiteConorm (𝓞 K) K L (𝓞 L)`. The archimedean datum is the `InfinitePlaceData` whose place isomorphism, for an infinite place $v$ of $K$, is the algebra isomorphism $K_v \otimes_K L \;\cong\; \prod_{w \mid v} L_w$ (product over the places of $L$ whose restriction to $K$ is $v$) sending $c \otimes l$ to the family $(\iota_{K_v \to L_w}(c)\cdot \iota_{L \to L_w}(l))_w$; its conorm therefore has $w$-component the image of $x_{w|_K}$ under $K_{w|_K} \to L_w$. The finite conorm is the map of restricted products along the contraction map $w \mapsto w \cap \mathcal{O}_K$ on height-one primes, with local components the semialgebra homomorphisms $K_{v} \to L_{w}$ on adic completions for $v = w \cap \mathcal{O}_K$; these carry $\mathcal{O}_{K_v}$ into $\mathcal{O}_{L_w}$ and the contraction map is cofinite-to-cofinite, so the restricted-product condition is preserved.
--
--   Two componentwise identities record the two halves of `genuineβ`, `continuous_genuineβ` asserts that it is continuous, being continuous in each factor, and `genuineβ_compat` asserts compatibility with the principal embeddings: for $e \in K$, the image of $e$ under $K \to \mathbb{A}_K$ followed by `genuineβ K L` equals the image of $e$ under $K \to L \to \mathbb{A}_L$.
--
--   **Relation to Mathlib.** Mathlib provides the adele ring of a number field as the product of its infinite and finite adele rings, together with the adic completions and the restricted-product formalism used here; the assembled conorm `genuineβ` and the infinite-place datum it rests on are the project's own.
--
--   **Where it is used.** The map `genuineβ` is the base-change homomorphism of adele rings along a finite extension of number fields, with the compatibility with the principal embeddings that allows it to be compared with the induced map $\mathbb{A}_K \otimes_K L \to \mathbb{A}_L$. It is used throughout the project's adelic base-change material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_GenuineBeta.lean

import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_FiniteConorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain M4aHerbrand.ArchSemilocal

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineβ : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (genuineInfinitePlaceData (K := K) (L := L)).conorm (finiteConorm (𝓞 K) K L (𝓞 L))

@[simp] theorem genuineβ_fst (x : AdeleRing (𝓞 K) K) :
    (genuineβ K L x).1 = (genuineInfinitePlaceData (K := K) (L := L)).conorm x.1 := rfl

@[simp] theorem genuineβ_snd (x : AdeleRing (𝓞 K) K) :
    (genuineβ K L x).2 = finiteConorm (𝓞 K) K L (𝓞 L) x.2 := rfl

theorem continuous_genuineβ : Continuous (genuineβ K L) :=
  Continuous.prodMap continuous_conorm (continuous_finiteConorm (𝓞 K) K L (𝓞 L))

theorem genuineβ_compat (e : K) :
    genuineβ K L (algebraMap K (AdeleRing (𝓞 K) K) e) = algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L e) :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).conorm_algebraMap e)
    (finiteConorm_algebraMap (𝓞 K) K L (𝓞 L) e)

end Genuine

end M4aHerbrand.Bridge

end


