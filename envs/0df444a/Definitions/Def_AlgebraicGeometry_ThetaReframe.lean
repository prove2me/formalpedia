-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaReframe
-- name    : AlgebraicGeometry_ThetaReframe
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/22576991-4291-566d-beab-07e7bc1753fb
-- title:
--   Reframing a framed polarised abelian scheme by a matrix
-- statement:
--   Fix natural numbers $g, N, n$ and a commutative ring $S$. A `FramedPolarisedAbelianScheme g N n S` is a polarised abelian scheme $X$ of relative dimension $g$, polarisation degree $N+1$ and level $n$ over $S$ — an abelian scheme $f : A \to \operatorname{Spec} S$ with relative group law $L$, torsion points $P_\bullet$ and invertible sheaf $\mathcal{L} = X.\mathrm{pol}$ — together with a frame: a `Scheme.Modules.ProjPresentation` of $\mathcal{L}$ relative to $f$ with $N+1$ global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal{L}, \top)$, the requirement that the associated morphism `frame.toProj` to projective $N$-space over $S$ be a closed immersion, and the requirement `IsSectionBasis` that the map $S^{N+1} \to \Gamma(\mathcal{L},\top)$, $c \mapsto \sum_i f^{\sharp}(c_i)\,\sigma_i$, be bijective.
--
--   This module defines a single predicate, `IsReframe X U X'`, for a square matrix $U \in M_{N+1}(S)$ and a second framed object $X'$ over the same $S$. It asserts the existence of a projective presentation $P'$ of the same sheaf $X.\mathrm{pol}$ for the same structure morphism $X.f$, whose morphism to projective space is a closed immersion and whose sections form a section basis in the above sense, such that firstly $X'$ is *equal* to the framed object assembled from the unchanged underlying polarised abelian scheme $X.\mathrm{toPolarisedAbelianScheme}$ together with $P'$ and these two properties, and secondly the new sections are the $U$-combinations of the old ones:
--   $$\sigma'_i = \sum_{j=0}^{N} f^{\sharp}(U_{ij}) \cdot \sigma_j, \qquad 0 \le i \le N,$$
--   where $U_{ij} \in S$ acts on $\Gamma(X.\mathrm{pol}, \top)$ through the identification of $S$ with $\Gamma(\operatorname{Spec} S, \top)$ followed by $X.f$, exactly as in `IsSectionBasis`. Thus reframing is formulated as a relation between framed objects rather than as an operation producing one, the equality being a literal equality of structures, so that no transport along an isomorphism of the underlying data is involved; the morphism $P'.\mathrm{toProj}$ is constrained only by being a closed immersion, the sections determining it.
--
--   **Relation to Mathlib.** Mathlib has no notion of polarised abelian scheme, of a projective presentation of an invertible sheaf by global sections, or of frames on such; these are the project's own notions, built on Mathlib's schemes and `SheafOfModules`.
--
--   **Where it is used.** The reframing relation records the action of $\mathrm{GL}_{N+1}(S)$ on the projective frames of a polarised abelian scheme, and is used alongside the theta-adaptedness conditions of the imported modules in the project's treatment of moduli of polarised abelian schemes with level and theta structure, which underlies the realisation of modular curves and their Jacobians needed for the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaReframe.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def IsReframe {S : Type u} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (X' : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ (P' : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P'.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P'.σ),
    X' = ⟨X.toPolarisedAbelianScheme, P', h₁, h₂⟩ ∧
    ∀ i : Fin (N + 1), P'.σ i =
      ∑ j : Fin (N + 1), ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (U i j))) • X.frame.σ j

end AlgebraicGeometry.FramedPolarisedAbelianScheme

end


