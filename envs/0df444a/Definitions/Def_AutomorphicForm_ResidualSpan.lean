-- Prove2me | Definitions.Def_AutomorphicForm_ResidualSpan
-- name    : AutomorphicForm_ResidualSpan
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/1423c369-53bf-54ea-a938-61826b9380ff
-- title:
--   Residual span of determinant characters for adelic GL2​
-- statement:
--   The setting is a Dedekind domain $R$ with fraction field $K$, its adele ring $\mathbb{A} =$ `AdeleRing R K`, and the group $\mathrm{GL}_2(\mathbb{A})$, written `AdelicGL2 R K`. Fixed are a subgroup $Z \le \mathbb{A}^\times$ and a group homomorphism $\xi : Z \to \mathbb{C}^\times$. For a homomorphism $\chi : \mathbb{A}^\times \to \mathbb{C}^\times$, `chiDet R K χ` is the function $g \mapsto \chi(\det g)$ on $\mathrm{GL}_2(\mathbb{A})$, and `SquaresToXi R K Z ξ χ` is the condition $\chi(z)^2 = \xi(z)$ for all $z \in Z$.
--
--   `residualSpan R K Z ξ` is then defined as the $\mathbb{C}$-submodule of the space of all functions $\mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ spanned by the set of those functions that are of the form $\chi \circ \det$ for some homomorphism $\chi : \mathbb{A}^\times \to \mathbb{C}^\times$ satisfying $\chi^2 = \xi$ on $Z$. No continuity, unitarity, invariance under $K^\times$ inside $\mathbb{A}^\times$, automorphy or square-integrability condition is imposed on $\chi$ or on the resulting functions: membership is purely the span condition, and $\chi$ is an abstract homomorphism of unit groups.
--
--   Two consequences are recorded. First, if $\chi$ satisfies $\chi^2 = \xi$ on $Z$ then $\chi \circ \det$ lies in `residualSpan R K Z ξ`, being one of the spanning functions. Second, if no homomorphism $\chi : \mathbb{A}^\times \to \mathbb{C}^\times$ satisfies $\chi^2 = \xi$ on $Z$, the spanning set is empty and the submodule is $\bot$, the zero submodule.
--
--   **Relation to Mathlib.** The adele ring and `Matrix.GeneralLinearGroup`, as well as `Submodule.span`, are Mathlib's; the notion of a space of functions on $\mathrm{GL}_2$ of the adeles spanned by determinant twists with prescribed square on a central subgroup is the project's own.
--
--   **Where it is used.** The module sits in the project's adelic framework for automorphic forms on $\mathrm{GL}_2$ with central character $\xi$, where the functions $\chi \circ \det$ form the one-dimensional, non-cuspidal part of such a space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ResidualSpan.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AutomorphicForm

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def residualSpan (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) :=
  Submodule.span ℂ
    {φ | ∃ χ : (AdeleRing R K)ˣ →* ℂˣ, SquaresToXi R K Z ξ χ ∧ φ = chiDet R K χ}

variable {R K}

theorem chiDet_mem_residualSpan {Z : Subgroup (AdeleRing R K)ˣ} {ξ : Z →* ℂˣ}
    {χ : (AdeleRing R K)ˣ →* ℂˣ} (h : SquaresToXi R K Z ξ χ) :
    chiDet R K χ ∈ residualSpan R K Z ξ :=
  Submodule.subset_span ⟨χ, h, rfl⟩

theorem residualSpan_eq_bot_of_forall_not {Z : Subgroup (AdeleRing R K)ˣ} {ξ : Z →* ℂˣ}
    (h : ∀ χ : (AdeleRing R K)ˣ →* ℂˣ, ¬ SquaresToXi R K Z ξ χ) :
    residualSpan R K Z ξ = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro φ ⟨χ, hχ, -⟩
  exact absurd hχ (h χ)

end AutomorphicForm


