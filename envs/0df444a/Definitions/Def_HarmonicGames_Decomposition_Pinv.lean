-- Prove2me | Definitions.Def_HarmonicGames_Decomposition_Pinv
-- name    : HarmonicGames_Decomposition_Pinv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:50:57.809147+00:00
-- url     : https://prove2.me/theorems/bd257d98-001e-4764-bba1-bb56ca622260
-- title:
--   The Moore–Penrose pseudoinverse $L^\dagger$ of a linear map between finite-dimensional inner product spaces
-- statement:
--   Let $V$ and $W$ be finite-dimensional real inner product spaces and $L : V \to W$ a linear map. The **Moore–Penrose pseudoinverse** $L^\dagger : W \to V$ is the linear map that sends $y \in W$ to the unique vector $x \in (\ker L)^\perp$ with
--
--   $$
--   L x = P_{\operatorname{im} L}\, y ,
--   $$
--
--   where $P_{\operatorname{im} L}$ is the orthogonal projection of $W$ onto the image of $L$. It is built in three steps: project $y$ orthogonally onto $\operatorname{im} L$, invert the linear isomorphism $L|_{(\ker L)^\perp} : (\ker L)^\perp \to \operatorname{im} L$, and include $(\ker L)^\perp$ into $V$.
--
--   The pseudoinverse depends on the inner products of $V$ and $W$. Candogan, Menache, Ozdaglar and Parrilo use it (p. 13, "the (Moore–Penrose) pseudoinverse … with respect to the inner products introduced in Section 3") for the operators $D_m^\dagger$, $D^\dagger$ and $\delta_0^\dagger$ that define the projections $\Pi_m = D_m^\dagger D_m$ and the components of the decomposition theorem. The map so defined satisfies the four Penrose identities $LL^\dagger L = L$, $L^\dagger L L^\dagger = L^\dagger$, $(LL^\dagger)^* = LL^\dagger$, $(L^\dagger L)^* = L^\dagger L$.
--
--   **Formalization Note** Mathlib has no operator pseudoinverse, so it is defined here. The projection is taken onto the image of $L$ restricted to $(\ker L)^\perp$, which equals $\operatorname{im} L$. The file contains one structural lemma: the restriction of $L$ to $(\ker L)^\perp$ is injective. The Penrose identities are not proved here.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 13, §4.1 (pseudoinverse with respect to the inner products of Section 3)

import Mathlib

namespace HarmonicGames.Decomposition

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

/-- The **Moore–Penrose pseudoinverse** `L†` of a linear map `L : V → W` between
finite-dimensional real inner product spaces, taken with respect to the inner products of
`V` and `W`.  For `y : W`, `L† y` is the unique `x ∈ (ker L)ᗮ` with `L x = P y`, where `P`
is the orthogonal projection of `W` onto `range L`.  Concretely: project `y` orthogonally
onto `range (L|_{(ker L)ᗮ})` (which equals `range L`), invert the linear isomorphism
`L|_{(ker L)ᗮ} : (ker L)ᗮ ≃ range L`, and include `(ker L)ᗮ` into `V`.

This operator satisfies the four Penrose identities `L L† L = L`, `L† L L† = L†`,
`(L L†)* = L L†`, `(L† L)* = L† L` (not proved here). -/
noncomputable def pinv [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (L : V →ₗ[ℝ] W) : W →ₗ[ℝ] V :=
  (LinearMap.ker L)ᗮ.subtype ∘ₗ
    (LinearEquiv.ofInjective _ (pinv_restrict_injective L)).symm.toLinearMap ∘ₗ
    (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto.toLinearMap

end HarmonicGames.Decomposition


