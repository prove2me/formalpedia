-- Prove2me | Definitions.Def_M4aHerbrand_FiniteConorm
-- name    : M4aHerbrand_FiniteConorm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d3c74267-d414-50db-b5e7-0c494bc3268f
-- title:
--   Conorm map on finite adele rings of an AKLB extension
-- statement:
--   The standing context is an AKLB situation: $A$ is a Dedekind domain with fraction field $K$, $B$ is an $A$-algebra which is integral over $A$ and is itself a Dedekind domain with fraction field $L$, and $L$ is a $K$-algebra compatibly with the $A$- and $B$-structures (the scalar-tower and fraction-field typeclasses are the standing assumptions).
--
--   The first declaration, `tendsto_under_cofinite`, records that the restriction map $w \mapsto w \cap A$ on height-one primes, written `HeightOneSpectrum.under A`, is cofinite-to-cofinite: the preimage of a cofinite set of primes of $A$ is cofinite in the primes of $B$, equivalently each finite set of primes of $A$ has only finitely many primes of $B$ above it.
--
--   For a height-one prime $w$ of $B$, `finiteLocalHom` is the local map $K_{w \cap A} \to L_w$ between adic completions, namely the underlying ring homomorphism of the project's semialgebra map `Extension.adicCompletionSemialgHom` attached to $w$ viewed as an extension of $w \cap A$. Two accompanying lemmas state that this map is continuous and that it carries the valuation ring $\mathcal{O}_{w \cap A} \subseteq K_{w\cap A}$ into $\mathcal{O}_w \subseteq L_w$.
--
--   The main definition, `finiteConorm`, is the resulting ring homomorphism $\mathbb{A}_{A,K}^{f} \to \mathbb{A}_{B,L}^{f}$ between the finite adele rings, obtained as the restricted-product map along the index map `under A` (legitimate by the cofiniteness statement) whose $w$-component is `finiteLocalHom` at $w$, the integrality condition holding at every $w$. Its value at $w$ is the image of the $(w \cap A)$-component of the input. Finally `continuous_finiteConorm` asserts continuity for the restricted-product topologies, and `finiteConorm_algebraMap` asserts compatibility with principal adeles: the conorm of the diagonal image of $k \in K$ is the diagonal image of $k$ regarded in $L$.
--
--   **Relation to Mathlib.** Mathlib supplies the finite adele ring, adic completions of height-one primes and the generic restricted-product map `RestrictedProduct.mapAlongRingHom`; the base-change (conorm) homomorphism of finite adele rings along an AKLB extension, and its local constituents, are assembled here from the project's completion base-change material.
--
--   **Where it is used.** These maps provide the comparison between the finite adeles of a base field and those of a finite extension, so that adelic objects over $K$ can be transported to $L$; they are part of the adelic infrastructure underlying the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_FiniteConorm.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace M4aHerbrand.Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

include K L in
omit [IsFractionRing B L] in

theorem tendsto_under_cofinite :
    Filter.Tendsto (HeightOneSpectrum.under A : HeightOneSpectrum B → HeightOneSpectrum A)
      Filter.cofinite Filter.cofinite := by
  intro S hS
  exact preimage_comap_finite A K L B Sᶜ hS

def finiteLocalHom (w : HeightOneSpectrum B) : (w.under A).adicCompletion K →+* w.adicCompletion L :=
  (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).toRingHom

theorem finiteLocalHom_apply (w : HeightOneSpectrum B) (x : (w.under A).adicCompletion K) :
    finiteLocalHom A K L B w x =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) x := rfl

theorem continuous_finiteLocalHom (w : HeightOneSpectrum B) : Continuous (finiteLocalHom A K L B w) :=
  Extension.adicCompletionSemialgHom_continuous K L (⟨w, rfl⟩ : (w.under A).Extension B)

theorem finiteLocalHom_mapsTo (w : HeightOneSpectrum B) :
    Set.MapsTo (finiteLocalHom A K L B w)
      ((w.under A).adicCompletionIntegers K : Set ((w.under A).adicCompletion K))
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
  Set.mapsTo_iff_image_subset.2
    (Extension.adicCompletionSemialgHom_image_adicCompletionIntegers K L
      (⟨w, rfl⟩ : (w.under A).Extension B))

def finiteConorm : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w => finiteLocalHom A K L B w)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)

@[simp] theorem finiteConorm_apply (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    finiteConorm A K L B x w =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) (x (w.under A)) :=
  rfl

theorem continuous_finiteConorm : Continuous (finiteConorm A K L B) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w x => finiteLocalHom A K L B w x)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)
    (fun w => continuous_finiteLocalHom A K L B w)

theorem finiteConorm_algebraMap (k : K) :
    finiteConorm A K L B (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L k) := by
  refine FiniteAdeleRing.ext L fun w => ?_
  rw [FiniteAdeleRing.algebraMap_apply]
  exact (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).commutes k

end AKLB

end M4aHerbrand.Bridge

end


