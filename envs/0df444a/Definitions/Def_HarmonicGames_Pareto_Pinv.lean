-- Prove2me | Definitions.Def_HarmonicGames_Pareto_Pinv
-- name    : HarmonicGames_Pareto_Pinv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:47.595131+00:00
-- url     : https://prove2.me/theorems/dfa63e24-3596-4bee-a1dc-3caf4f1bf930
-- title:
--   Injectivity of a linear map restricted to the orthogonal complement of its kernel
-- statement:
--   Let $V$ and $W$ be real inner product spaces and $L : V \to W$ a linear map. The restriction of $L$ to the orthogonal complement $(\ker L)^\perp$ of its kernel is injective: if $x \in (\ker L)^\perp$ and $Lx = 0$, then $x \in \ker L \cap (\ker L)^\perp = \{0\}$.
--
--   This is the structural fact behind the Moore–Penrose pseudoinverse $L^\dagger$, which inverts $L|_{(\ker L)^\perp} : (\ker L)^\perp \to \operatorname{im} L$ and which the paper uses ("with respect to the inner products introduced in Section 3") for $D^\dagger$ and $\delta_0^\dagger$ in the potential and harmonic components of Theorem 4.1.
--
--   **Formalization Note** The pseudoinverse operator itself is the shared definition `HarmonicGames.Decomposition.pinv`; this file contains only the injectivity lemma.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 13–14 and 17, Section 4.1 (pseudoinverses) and Theorem 4.1

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

namespace HarmonicGames.Pareto

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

end HarmonicGames.Pareto


