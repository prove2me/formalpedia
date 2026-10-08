-- Prove2me | Definitions.Def_HarmonicGames_Projection_Pinv
-- name    : HarmonicGames_Projection_Pinv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:35.471137+00:00
-- url     : https://prove2.me/theorems/b5df8aca-6309-44bc-9ca1-d8d079cea109
-- title:
--   The restriction of a linear map to the orthogonal complement of its kernel is injective (the step that defines the pseudoinverse $L^\dagger$)
-- statement:
--   Let $V$ and $W$ be real inner product spaces and $L : V \to W$ a linear map. Then the restriction of $L$ to the orthogonal complement of its kernel,
--
--   $$
--   L|_{(\ker L)^\perp} : (\ker L)^\perp \to W ,
--   $$
--
--   is injective: if $x \in (\ker L)^\perp$ and $Lx = 0$, then $x \in \ker L \cap (\ker L)^\perp = \{0\}$.
--
--   This is the fact behind the Moore–Penrose pseudoinverse $L^\dagger$ that the paper uses for the operators $D_m$ and $\delta_0$ ("with respect to the inner products introduced in Section 3"): $L$ maps $(\ker L)^\perp$ isomorphically onto its image, and $L^\dagger$ is the inverse of that isomorphism composed with the orthogonal projection onto $\operatorname{im} L$.
--
--   **Formalization Note** The pseudoinverse itself is defined in the shared module `HarmonicGames.Decomposition.Pinv`, which this file imports; this file only restates the injectivity lemma in the namespace `HarmonicGames.Projection`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 13–14, Section 4.1 (the pseudoinverses D_m†)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

namespace HarmonicGames.Projection

open scoped InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The restriction of `L` to the orthogonal complement `(ker L)ᗮ` of its kernel is injective. -/
theorem pinv_restrict_injective (L : V →ₗ[ℝ] W) :
    Function.Injective (L ∘ₗ (LinearMap.ker L)ᗮ.subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h : (x : V) ∈ LinearMap.ker L ⊓ (LinearMap.ker L)ᗮ := ⟨hx, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
  exact Subtype.ext h

end HarmonicGames.Projection


