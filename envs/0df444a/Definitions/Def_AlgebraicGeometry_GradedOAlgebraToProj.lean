-- Prove2me | Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
-- name    : AlgebraicGeometry_GradedOAlgebraToProj
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/901caef5-bfac-5f79-97db-a67f4aaedec9
-- title:
--   Recognising the canonical morphism to Proj of a section ring
-- statement:
--   Fix a commutative ring $S$, a scheme $X$ with a structure morphism $f : X \to \operatorname{Spec} S$, an object $L$ of $X$'s category of sheaves of modules, a commutative $S$-algebra $R$ with an $\mathbb{N}$-grading by $S$-submodules $\mathcal{R}_n \subseteq R$ making $R$ a graded algebra, and a family of maps $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ into the global sections of the tensor powers $L^{\otimes 0} = \mathcal{O}_X$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$. The module defines a Prop-valued structure `IsCanonicalToProj` which is a predicate on a morphism $\theta : X \to \operatorname{Proj} \mathcal{R}$, with three fields.
--
--   First, `comp_toSpecZero`: $\theta$ followed by the canonical $\operatorname{Proj} \mathcal{R} \to \operatorname{Spec} \mathcal{R}_0$ and then by $\operatorname{Spec}$ of the ring map $S \to \mathcal{R}_0$ obtained from $S \to R$ composed with projection onto the degree-zero part equals $f$; thus $\theta$ is a morphism over $\operatorname{Spec} S$. Second, `isFrameOn`: for every $n > 0$ and every $\sigma \in \mathcal{R}_n$, the section $\iota_n(\sigma)$ satisfies the project predicate `IsFrameOn` on the open set $\theta^{-1}(D_+(\sigma))$, the assertion that $\iota_n(\sigma)$ frames $L^{\otimes n}$ there. Third, `appLE_awayToSection_smul`: for $n > 0$, $\sigma \in \mathcal{R}_n$, $k \in \mathbb{N}$ and $s \in \mathcal{R}_{kn}$, write $U = \theta^{-1}(D_+(\sigma))$ and let $\theta^{\#}(s/\sigma^k) \in \Gamma(U, \mathcal{O}_X)$ be the pullback along $\theta$ of the section of $\mathcal{O}_{\operatorname{Proj}\mathcal{R}}$ on $D_+(\sigma)$ given by the homogeneous localisation $s/\sigma^k$; then $\theta^{\#}(s/\sigma^k) \cdot \iota_{kn}(\sigma^k)|_U = \iota_{kn}(s)|_U$ in $\Gamma(U, L^{\otimes kn})$, where $\sigma^k$ is taken in $\mathcal{R}_{kn}$.
--
--   No linearity or multiplicativity of $\iota$ is part of this structure; that is the content of the companion predicate `IsSectionRing`, which requires each $\iota_n$ to be bijective and additive, $S$-semilinear through $f$, unital, and multiplicative for the tensor-power isomorphisms $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$.
--
--   **Relation to Mathlib.** Built on Mathlib's $\operatorname{Proj}$ of a graded algebra (`Proj.toSpecZero`, `Proj.basicOpen`, `Proj.awayToSection`, `HomogeneousLocalization.Away.mk`, `GradedRing.projZeroRingHom'`); Mathlib has no predicate characterising a morphism to $\operatorname{Proj}$ in terms of a section ring of a line bundle, so `IsCanonicalToProj` is the project's own notion.
--
--   **Where it is used.** These predicates belong to the project's scheme-theoretic infrastructure for presenting a scheme as the $\operatorname{Proj}$ of a graded ring of sections of a line bundle: `IsSectionRing` records that a graded algebra is such a section ring, and `IsCanonicalToProj` pins down the morphism to $\operatorname{Proj}$ that the sections induce.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_GradedOAlgebraToProj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}

structure IsCanonicalToProj (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (θ : X ⟶ Proj 𝓡) : Prop where

  comp_toSpecZero : θ ≫ Proj.toSpecZero 𝓡 ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))) = f

  isFrameOn : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n, IsFrameOn (ι n σ) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))

  appLE_awayToSection_smul : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ) (s : 𝓡 (k • n)),
      (θ.appLE (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
          (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))) •
        (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩)
      = (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) s)

end AlgebraicGeometry.GradedOAlgebra

end


