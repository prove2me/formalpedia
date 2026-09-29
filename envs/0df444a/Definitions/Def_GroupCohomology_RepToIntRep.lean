-- Prove2me | Definitions.Def_GroupCohomology_RepToIntRep
-- name    : GroupCohomology_RepToIntRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/12bac1dc-0b6e-544c-a710-b4da4f1c7412
-- title:
--   Restriction of scalars from k-linear to Z-linear representations
-- statement:
--   Fix a commutative ring $k$ and a group $G$. For an object $M$ of $\mathrm{Rep}_k(G)$, i.e. a $k$-module $M.V$ together with a homomorphism $\rho_M \colon G \to \mathrm{GL}_k(M.V)$, [`Rep.toIntRepρ`](../def/GroupCohomology_RepToIntRep.html#L13) is the representation of $G$ on the same abelian group regarded as a $\mathbb{Z}$-module (the canonical $\mathbb{Z}$-module structure on an additive commutative group), sending $g$ to the additive endomorphism underlying $\rho_M(g)$, viewed as a $\mathbb{Z}$-linear map; multiplicativity and unitality are inherited from $\rho_M$. The object [`Rep.toIntRep M`](../def/GroupCohomology_RepToIntRep.html#L20) of $\mathrm{Rep}_{\mathbb{Z}}(G)$ is the resulting $\mathbb{Z}[G]$-module: the same carrier, the same action. Accompanying identities record that the underlying type of `M.toIntRep` is $M.V$, that its action map is `M.toIntRepρ`, and that $g$ acts on $x$ by $\rho_M(g)x$.
--
--   On morphisms, [`Rep.toIntRepMap`](../def/GroupCohomology_RepToIntRep.html#L28) sends a morphism $\varphi \colon M \to N$ of $k$-linear representations — a $k$-linear map commuting with the actions — to the morphism $M_{\mathbb{Z}} \to N_{\mathbb{Z}}$ given by the same underlying additive map, now read as $\mathbb{Z}$-linear, its equivariance being the equivariance of $\varphi$; the underlying function is unchanged, as recorded by [`Rep.toIntRepMap_hom_apply`](../def/GroupCohomology_RepToIntRep.html#L31). The lemmas [`Rep.toIntRepMap_id`](../def/GroupCohomology_RepToIntRep.html#L33) and [`Rep.toIntRepMap_comp`](../def/GroupCohomology_RepToIntRep.html#L35) state that this assignment preserves identities and composition, and [`Rep.toIntRepFunctor`](../def/GroupCohomology_RepToIntRep.html#L40) packages the construction as a functor $\mathrm{Rep}_k(G) \to \mathrm{Rep}_{\mathbb{Z}}(G)$. Mathematically this is restriction of scalars along the unique ring homomorphism $\mathbb{Z} \to k$, equivalently the forgetful functor from $k[G]$-modules to $G$-modules; everything in the module is data together with the identities expressing that the carrier, the action and the maps are literally unchanged.
--
--   **Relation to Mathlib.** Mathlib supplies the categories `Rep k G`, the notion `Representation`, and the constructors `Rep.of` and `Rep.ofHom`, as well as the passage from an additive map to a $\mathbb{Z}$-linear map; the functor `Rep k G ⥤ Rep ℤ G` assembled from them here is the project's own.
--
--   **Where it is used.** Galois representations in the argument are $\mathbb{F}_p$-linear, whereas duality statements for class formations are naturally phrased for $G$-modules, i.e. abelian groups with $G$-action. This functor is the bridge, so that submodules, invariants and group cohomology of such a representation may be formed against the canonical $\mathbb{Z}$-module structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RepToIntRep.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type} [CommRing k] [Group G]

def toIntRepρ (M : Rep k G) : Representation ℤ G M.V where
  toFun g := (M.ρ g).toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp

@[simp] lemma toIntRepρ_apply_apply (M : Rep k G) (g : G) (x : M.V) : M.toIntRepρ g x = M.ρ g x := rfl

def toIntRep (M : Rep k G) : Rep ℤ G := Rep.of M.toIntRepρ

lemma coe_toIntRep (M : Rep k G) : (M.toIntRep : Type) = M.V := rfl

@[simp] lemma toIntRep_ρ (M : Rep k G) : M.toIntRep.ρ = M.toIntRepρ := rfl

lemma toIntRep_ρ_apply_apply (M : Rep k G) (g : G) (x : M.V) : M.toIntRep.ρ g x = M.ρ g x := rfl

def toIntRepMap {M N : Rep k G} (φ : M ⟶ N) : M.toIntRep ⟶ N.toIntRep :=
  Rep.ofHom ⟨φ.hom.toAddMonoidHom.toIntLinearMap, fun g => LinearMap.ext fun x => Rep.hom_comm_apply φ g x⟩

@[simp] lemma toIntRepMap_hom_apply {M N : Rep k G} (φ : M ⟶ N) (x : M.V) : (toIntRepMap φ).hom x = φ.hom x := rfl

lemma toIntRepMap_id (M : Rep k G) : toIntRepMap (𝟙 M) = 𝟙 M.toIntRep := by ext x; rfl

lemma toIntRepMap_comp {M N P : Rep k G} (φ : M ⟶ N) (ψ : N ⟶ P) :
    toIntRepMap (φ ≫ ψ) = toIntRepMap φ ≫ toIntRepMap ψ := by ext x; rfl

variable (k G) in

def toIntRepFunctor : Rep k G ⥤ Rep ℤ G where
  obj M := M.toIntRep
  map φ := toIntRepMap φ
  map_id M := toIntRepMap_id M
  map_comp φ ψ := toIntRepMap_comp φ ψ

end Rep

end


