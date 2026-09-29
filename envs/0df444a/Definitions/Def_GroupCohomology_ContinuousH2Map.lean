-- Prove2me | Definitions.Def_GroupCohomology_ContinuousH2Map
-- name    : GroupCohomology_ContinuousH2Map
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/3ecb2649-09e8-57fc-b104-324294168e12
-- title:
--   Pullback maps on level-constant cochains and continuous H2
-- statement:
--   The context is a commutative ring $k$, groups $G$ and $H$ equipped with level maps $r_G \colon G \to (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ and $r_H$ into the same automorphism group of `AlgebraicClosure ℚ`, a group homomorphism $f \colon G \to H$ with $r_H(f(g)) = r_G(g)$ for all $g$, representations $A$ of $H$ and $B$ of $G$ over $k$, and a $k$-linear map $\varphi \colon A \to B$ satisfying $\varphi(A.\rho(f(g))\,a) = B.\rho(g)\,\varphi(a)$.
--
--   Recall that a function on $H$ (resp. on $H \times H$) is level-constant for $r_H$ when there is a finite-dimensional intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that the function is unchanged by right translation of its argument(s) by elements whose $r_H$-image lies in the fixing subgroup of $F$. The two `precomp` lemmas record that precomposition with $f$ preserves this, with the same field $F$. The linear maps `cochainsPullPush₁` and `cochainsPullPush₂` send $x$ to $\varphi \circ x \circ f$ and to $\varphi \circ x \circ (f \times f)$ respectively; they commute with the differential $d_{12}$ from $1$- to $2$-cochains, and the degree-$2$ map carries $2$-cocycles to $2$-cocycles, level-constant cochains to level-constant cochains, hence level $2$-cocycles to level $2$-cocycles, and coboundaries of level-constant $1$-cochains to coboundaries of level-constant $1$-cochains. Restricting gives `levelCocycles₂Map`, a $k$-linear map between the submodules of level $2$-cocycles, and passing to quotients gives `continuousH2Map`, a $k$-linear map from the continuous $H^2$ of $(r_H, A)$ to that of $(r_G, B)$, determined by $[x] \mapsto [\varphi \circ x \circ (f \times f)]$ on classes of level $2$-cocycles.
--
--   **Relation to Mathlib.** The cochain-level differential `d₁₂` and the submodule `cocycles₂` are Mathlib's; the level-constancy conditions, the level cocycles and coboundaries and the quotient `continuousH2` are the project's own. The functorial data $(f, \varphi)$ is kept unbundled — a group homomorphism with a pointwise compatibility of level maps, plus a plain linear map with an equivariance hypothesis — rather than packaged as a morphism of representations as in Mathlib's `groupCohomology` functoriality.
--
--   **Where it is used.** The maps constructed here are the pullback maps on the project's continuous second cohomology: taking $f$ the identity gives change of coefficients, and taking $\varphi$ the identity gives restriction along a subgroup inclusion or a decomposition-group embedding, as needed in the Galois-cohomological parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousH2Map.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
variable {rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (f : G →* H) (hf : ∀ g, rH (f g) = rG g)

section precomp

include hf

lemma IsLevelConstant₁.precomp {X : Type*} {x : H → X} (hx : IsLevelConstant₁ rH x) :
    IsLevelConstant₁ rG (x ∘ f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  exact h (f g) (f s) (by rwa [hf])

lemma IsLevelConstant₂.precomp {X : Type*} {x : H × H → X} (hx : IsLevelConstant₂ rH x) :
    IsLevelConstant₂ rG (x ∘ Prod.map f f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  exact h (f g) (f g') (f s) (f s') (by rwa [hf]) (by rwa [hf])

end precomp

variable {A : Rep k H} {B : Rep k G} (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a))

def cochainsPullPush₁ : (H → A) →ₗ[k] (G → B) where
  toFun x := φ ∘ x ∘ f
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def cochainsPullPush₂ : (H × H → A) →ₗ[k] (G × G → B) where
  toFun x := φ ∘ x ∘ Prod.map f f
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp] lemma cochainsPullPush₁_apply (x : H → A) (g : G) : cochainsPullPush₁ f φ x g = φ (x (f g)) := rfl

@[simp] lemma cochainsPullPush₂_apply (x : H × H → A) (g : G × G) :
    cochainsPullPush₂ f φ x g = φ (x (f g.1, f g.2)) := rfl

include hφ in
lemma cochainsPullPush₂_d₁₂ (x : H → A) :
    cochainsPullPush₂ f φ ((d₁₂ A).hom x) = (d₁₂ B).hom (cochainsPullPush₁ f φ x) := by
  ext ⟨g, g'⟩
  simp [d₁₂_hom_apply, map_add, map_sub, hφ, map_mul]

include hφ in
lemma cochainsPullPush₂_mem_cocycles₂ {x : H × H → A} (hx : x ∈ cocycles₂ A) :
    cochainsPullPush₂ f φ x ∈ cocycles₂ B := by
  rw [mem_cocycles₂_iff] at hx ⊢
  intro g h j
  simp only [cochainsPullPush₂_apply, map_mul, ← map_add, hx, ← hφ]

include hf in
lemma cochainsPullPush₁_mem_levelCochains₁ {x : H → A} (hx : x ∈ levelCochains₁ rH A) :
    cochainsPullPush₁ f φ x ∈ levelCochains₁ rG B :=
  ((IsLevelConstant₁.precomp f hf hx).comp φ :)

include hf in
lemma cochainsPullPush₂_mem_levelCochains₂ {x : H × H → A} (hx : x ∈ levelCochains₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCochains₂ rG B :=
  ((IsLevelConstant₂.precomp f hf hx).comp φ :)

include hf hφ in
lemma cochainsPullPush₂_mem_levelCocycles₂ {x : H × H → A} (hx : x ∈ levelCocycles₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCocycles₂ rG B :=
  ⟨cochainsPullPush₂_mem_cocycles₂ f φ hφ hx.1, cochainsPullPush₂_mem_levelCochains₂ f hf φ hx.2⟩

include hf hφ in
lemma cochainsPullPush₂_mem_levelCoboundaries₂ {x : H × H → A} (hx : x ∈ levelCoboundaries₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCoboundaries₂ rG B := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundaries₂_iff rH A x).1 hx
  exact (mem_levelCoboundaries₂_iff rG B _).2
    ⟨cochainsPullPush₁ f φ y, IsLevelConstant₁.precomp f hf hy |>.comp φ, (cochainsPullPush₂_d₁₂ f φ hφ y).symm⟩

def levelCocycles₂Map : ↥(levelCocycles₂ rH A) →ₗ[k] ↥(levelCocycles₂ rG B) :=
  (cochainsPullPush₂ f φ).restrict fun _ hx => cochainsPullPush₂_mem_levelCocycles₂ f hf φ hφ hx

@[simp] lemma coe_levelCocycles₂Map (x : ↥(levelCocycles₂ rH A)) :
    (levelCocycles₂Map f hf φ hφ x : G × G → B) = cochainsPullPush₂ f φ x := rfl

def continuousH2Map : continuousH2 rH A →ₗ[k] continuousH2 rG B :=
  Submodule.mapQ _ _ (levelCocycles₂Map f hf φ hφ) fun _ hx =>
    cochainsPullPush₂_mem_levelCoboundaries₂ f hf φ hφ hx

@[simp] lemma continuousH2Map_continuousH2π (x : ↥(levelCocycles₂ rH A)) :
    continuousH2Map f hf φ hφ (continuousH2π rH A x) = continuousH2π rG B (levelCocycles₂Map f hf φ hφ x) :=
  rfl

end groupCohomology


