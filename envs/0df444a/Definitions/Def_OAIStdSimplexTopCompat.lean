-- Prove2me | Definitions.Def_OAIStdSimplexTopCompat
-- name    : OAIStdSimplexTopCompat
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T09:47:19.152854+00:00
-- url     : https://prove2.me/theorems/42fe481c-64d8-4eae-977b-c9fbf53d8d5b
-- title:
--   Topological simplex compatibility layer for ports of openai/math (`toTopHomeo` and `TopCat.toSSetObjEquiv` with the structure `Convexity.StdSimplex`)
-- statement:
--   A compatibility layer, not new mathematics. It builds on [`Def_OAIStdSimplexCompat`](https://prove2.me/theorems/c7014b9a-e570-4ee1-a054-618b8beeb719), which it imports.
--
--   OpenAI's [openai/math](https://github.com/openai/math) is built on Mathlib `d13f23b`; prove2.me's environment is Mathlib `0df444a`. In `d13f23b` the topological $n$-simplex in `SimplexCategory.toTopHomeo` and `TopCat.toSSetObjEquiv` is the structure `Convexity.StdSimplex ℝ (Fin (n+1))`; in `0df444a` it is the subtype `stdSimplex ℝ (Fin (n+1))` of `Fin (n+1) → ℝ`. The two are homeomorphic, but not definitionally equal, so ported code that feeds a singular simplex to a lemma about `Convexity.StdSimplex` does not typecheck. This bundle gives each of the two declarations a version with the suffix `D` and the `d13f23b` type, obtained by composing with that homeomorphism, so that ported code compiles after a mechanical renaming.
--
--   This is not OpenAI's code, and nothing in it is copied from openai/math.
--
--   **Contents.**
--
--   - `OAI.SStd.homeoStdSimplex X`: the homeomorphism between the subtype `OAI.SStd ℝ X` (that is, `stdSimplex ℝ X`) and the structure `Convexity.StdSimplex ℝ X`, for a finite type $X$, preserving the weights; `homeoStdSimplex_map` and `homeoStdSimplex_symm_map` say that it and its inverse commute with pushing a point forward along a map of index types.
--   - `SimplexCategory.toTopHomeoD n`: the homeomorphism from the geometric realization of the standard simplicial simplex $\Delta[n]$ to `Convexity.StdSimplex ℝ (Fin (n+1))`, which is `d13f23b`'s `toTopHomeo` (Mathlib's `toTopHomeo` followed by `homeoStdSimplex`), with its naturality in $n$, `toTopHomeoD_naturality_apply`.
--   - `TopCat.toSSetObjEquivD X n`: the bijection between the $n$-simplices of the singular simplicial set of a topological space $X$ and the continuous maps `Convexity.StdSimplex ℝ (Fin (n+1)) → X`, which is `d13f23b`'s `toSSetObjEquiv` (Mathlib's `toSSetObjEquiv` followed by precomposition with the inverse of `homeoStdSimplex`). With it: `toSSetObjEquivD_apply` and `toSSetObjEquivD_symm_apply`, which unfold it to Mathlib's version, and the four lemmas `d13f23b` states for `toSSetObjEquiv`, with the same statements: `toSSetObjEquivD_symm_naturality`, `toSSetObjEquivD_naturality_apply` (a simplicial operator on the singular simplicial set is precomposition with the corresponding affine map of simplices), and its cases `toSSetObjEquivD_δ_apply` (faces) and `toSSetObjEquivD_σ_apply` (degeneracies).
--
--   In `d13f23b` those four lemmas hold by `rfl`. Here they are proved, through `homeoStdSimplex_map`.
--
--   **How ports use it.** The porting tools of the prove2me skill (`p2mlib.oaiport`, option `--stdsimplex`, structure mode) rename `toTopHomeo`, `toSSetObjEquiv` and these lemmas to their `D` versions, and import this bundle where they are used. Before this bundle, three ports wrote the same bridge by hand: Thomason's theorem (`OAI.CategoryTheory.Thomason`), the FiniteType singular-homology modules, and the Artin-group realizations.
-- source:
--   Original, written for porting openai/math (https://github.com/openai/math), not OpenAI code. It restates, for Convexity.StdSimplex, the types of SimplexCategory.toTopHomeo (Mathlib/AlgebraicTopology/SimplicialSet/TopAdj.lean) and TopCat.toSSetObjEquiv with its lemmas (Mathlib/AlgebraicTopology/SingularSet.lean, SimplicialSet/TopAdj.lean) as in Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612, https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612; proved from Mathlib 0df444a and Definitions.Def_OAIStdSimplexCompat.

import Mathlib
import Definitions.Def_OAIStdSimplexCompat

/-!
# Topological simplex compatibility for ports of openai/math

This file is not OpenAI's code. Mathlib `d13f23b` (OpenAI's) takes the topological `n`-simplex
of `SimplexCategory.toTop` to be the structure `Convexity.StdSimplex ℝ (Fin (n+1))`; Mathlib
`0df444a` (prove2.me's) takes the subtype `stdSimplex ℝ (Fin (n+1))`. Part 3 gives the two
declarations whose types mention that simplex, `SimplexCategory.toTopHomeo` and
`TopCat.toSSetObjEquiv`, versions with the suffix `D` and the `d13f23b` types, through the
homeomorphism `OAI.SStd.homeoStdSimplex` between subtype and structure. A port in structure mode
renames each use to the `D` version.
-/

noncomputable section OAIStdSimplexTopCompat

open CategoryTheory Simplicial

/-! ## Part 3: `toTopHomeoD` and `toSSetObjEquivD`, with the structure `Convexity.StdSimplex` -/

namespace OAI.SStd

/-- The subtype `stdSimplex ℝ X` and the structure `Convexity.StdSimplex ℝ X` are homeomorphic. -/
noncomputable def homeoStdSimplex (X : Type*) [Fintype X] :
    SStd ℝ X ≃ₜ Convexity.StdSimplex ℝ X where
  toEquiv := equivStdSimplex
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ X).continuous_iff.mpr
    exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun k => ?_
    exact Convexity.StdSimplex.continuous_weights_apply ℝ k

/-- `homeoStdSimplex` commutes with pushing forward along a map of index types. -/
theorem homeoStdSimplex_map {X Y : Type*} [Fintype X] [Fintype Y] (g : X → Y) (x : SStd ℝ X) :
    homeoStdSimplex Y (map g x) = Convexity.StdSimplex.map g (homeoStdSimplex X x) := by
  apply Convexity.StdSimplex.ext
  ext k
  simp [homeoStdSimplex, equivStdSimplex, toStdSimplex, weights_map,
    Convexity.StdSimplex.weights_map]

/-- The inverse of `homeoStdSimplex` commutes with pushing forward along a map of index types. -/
theorem homeoStdSimplex_symm_map {X Y : Type*} [Fintype X] [Fintype Y] (g : X → Y)
    (z : Convexity.StdSimplex ℝ X) :
    (homeoStdSimplex Y).symm (Convexity.StdSimplex.map g z) =
      map g ((homeoStdSimplex X).symm z) := by
  rw [Homeomorph.symm_apply_eq, homeoStdSimplex_map, Homeomorph.apply_symm_apply]

end OAI.SStd

/-- `d13f23b`'s `SimplexCategory.toTopHomeo`: the realization of `Δ[n]` is homeomorphic to
`Convexity.StdSimplex ℝ (Fin (n.len + 1))`. -/
noncomputable def SimplexCategory.toTopHomeoD (n : SimplexCategory) :
    ↑(SSet.toTop.obj (SSet.stdSimplex.obj n)) ≃ₜ Convexity.StdSimplex ℝ (Fin (n.len + 1)) :=
  n.toTopHomeo.trans (OAI.SStd.homeoStdSimplex _)

theorem SimplexCategory.toTopHomeoD_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : ↑(SSet.toTop.obj (SSet.stdSimplex.obj n))) :
    m.toTopHomeoD ((ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.map f))) x) =
      Convexity.StdSimplex.map (⇑(ConcreteCategory.hom f)) (n.toTopHomeoD x) := by
  apply Convexity.StdSimplex.ext
  ext k
  simp only [SimplexCategory.toTopHomeoD, Homeomorph.trans_apply,
    SimplexCategory.toTopHomeo_naturality_apply]
  simp [OAI.SStd.homeoStdSimplex, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights, Convexity.StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Finsupp.single_apply]
  change (FunOnFinite.linearMap ℝ ℝ _ (n.toTopHomeo x).1) k = _
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]

namespace TopCat

/-- `d13f23b`'s `TopCat.toSSetObjEquiv`: the `n`-simplices of the singular simplicial set of `X`
are the continuous maps from `Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))` to `X`. -/
noncomputable def toSSetObjEquivD (X : TopCat) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  (X.toSSetObjEquiv n).trans
    ((OAI.SStd.homeoStdSimplex _).continuousMapCongr (Homeomorph.refl X))

theorem toSSetObjEquivD_apply (X : TopCat) (n : SimplexCategoryᵒᵖ) (s : (toSSet.obj X).obj n)
    (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    X.toSSetObjEquivD n s z = X.toSSetObjEquiv n s ((OAI.SStd.homeoStdSimplex _).symm z) :=
  rfl

theorem toSSetObjEquivD_symm_apply (X : TopCat) (n : SimplexCategoryᵒᵖ)
    (g : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X)) :
    (X.toSSetObjEquivD n).symm g =
      (X.toSSetObjEquiv n).symm
        (g.comp ⟨OAI.SStd.homeoStdSimplex _, (OAI.SStd.homeoStdSimplex _).continuous⟩) :=
  rfl

theorem toSSetObjEquivD_symm_naturality {X : TopCat} {n m : SimplexCategory} (f : n ⟶ m)
    (g : C((Convexity.StdSimplex ℝ (Fin (m.len + 1))), X)) :
    (toSSet.obj X).map f.op ((X.toSSetObjEquivD _).symm g) =
      (X.toSSetObjEquivD _).symm (g.comp ⟨Convexity.StdSimplex.map f, by fun_prop⟩) := by
  apply (X.toSSetObjEquivD _).injective
  ext z
  rw [Equiv.apply_symm_apply, toSSetObjEquivD_apply, toSSetObjEquiv_naturality_apply,
    toSSetObjEquivD_symm_apply]
  change g (OAI.SStd.homeoStdSimplex _ (stdSimplex.map f ((OAI.SStd.homeoStdSimplex _).symm z))) =
    g (Convexity.StdSimplex.map f z)
  congr 1
  rw [← OAI.SStd.map, OAI.SStd.homeoStdSimplex_map, Homeomorph.apply_symm_apply]

@[simp]
theorem toSSetObjEquivD_naturality_apply {X : TopCat} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (toSSet.obj X).obj (Opposite.op m)) (z : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    dsimp% X.toSSetObjEquivD _ ((toSSet.obj X).map f.op x) z =
      X.toSSetObjEquivD _ x (Convexity.StdSimplex.map f z) := by
  rw [toSSetObjEquivD_apply, toSSetObjEquivD_apply, OAI.SStd.homeoStdSimplex_symm_map]
  exact toSSetObjEquiv_naturality_apply f x _

@[simp]
theorem toSSetObjEquivD_δ_apply {X : TopCat} {n : ℕ}
    (x : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dsimp% X.toSSetObjEquivD _ ((toSSet.obj X).δ i x) z =
      X.toSSetObjEquivD _ x (Convexity.StdSimplex.map i.succAbove z) :=
  toSSetObjEquivD_naturality_apply (SimplexCategory.δ i) x z

@[simp]
theorem toSSetObjEquivD_σ_apply {X : TopCat} {n : ℕ}
    (x : toSSet.obj X _⦋n⦌) (i : Fin (n + 1)) (z : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    dsimp% X.toSSetObjEquivD _ ((toSSet.obj X).σ i x) z =
      X.toSSetObjEquivD _ x (Convexity.StdSimplex.map i.predAbove z) :=
  toSSetObjEquivD_naturality_apply (SimplexCategory.σ i) x z

end TopCat

end OAIStdSimplexTopCompat


