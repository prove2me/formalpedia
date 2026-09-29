-- Prove2me | Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
-- name    : GroupCohomology_ContinuousUnramifiedLevelMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/983c75e5-e4ce-5ad5-ae43-e71a931b682b
-- title:
--   Functoriality of S-level continuous H1 and H2
-- statement:
--   Throughout, $k$ is a commutative ring, $G,H,I$ are groups equipped with level maps $r_G,r_H,r_I$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\mathrm{AlgebraicClosure}\ \mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\ \mathbb{Q})$, $S$ is a finite set of rational primes, and $f : G \to H$ is a homomorphism with $r_H(f(g)) = r_G(g)$ for all $g$. Recall that `IsLevelConstantSr₁ r S x` asserts the existence of an intermediate field $F/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ which is finite over $\mathbb{Q}$ and whose fixing subgroup contains the inertia subgroup of every valuation subring lying over a prime outside $S$, such that $x(gs) = x(g)$ whenever $r(s)$ fixes $F$; `IsLevelConstantSr₂` is the two-variable analogue. The two `precomp` lemmas say that the same field $F$ witnesses level constancy for $x \circ f$ and $x \circ (f \times f)$.
--
--   In degree two, for representations $A$ of $H$ and $B$ of $G$ and a $k$-linear $\varphi : A \to B$ with $\varphi(\rho_A(f(g))a) = \rho_B(g)\varphi(a)$, the cochain operation $x \mapsto \varphi \circ x \circ (f\times f)$ carries $S$-level cochains, $S$-level $2$-cocycles and $S$-level $2$-coboundaries for $(r_H,A)$ into those for $(r_G,B)$; `levelCocyclesSr₂Map` is the resulting map on $S$-level cocycles and `continuousH2SrMap` the induced $k$-linear map $H^2_{S}(r_H,A) \to H^2_{S}(r_G,B)$ on the quotients. Further lemmas record that it commutes with the comparison maps to the all-levels continuous $H^2$ and with the maps enlarging $S$ to $S' \supseteq S$, and give the identity and composition laws (for $f' : H \to I$, $\psi : C \to B$, $\varphi : B \to A$, the map attached to $(f' \circ f, \varphi \circ \psi)$ is the map for $(f',\psi)$ followed by the map for $(f,\varphi)$). For a single group $G$ and a morphism $\varphi : A \to B$ of representations, `continuousH2SrMapHom` is the resulting map, identity-preserving and satisfying $\varphi \mathbin{;} \psi \mapsto (\text{map of }\varphi)$ followed by $(\text{map of }\psi)$.
--
--   In degree one, for $\varphi : \mathrm{res}_f A \to B$ the value of `mapCocycles₁ f φ c` at $g$ is $\varphi(c(f(g)))$; the image of the submodule $H^1_{S}(r_H,A) \subseteq H^1(A)$ under the degree-one functoriality map of Mathlib lies in $H^1_{S}(r_G,B)$, and `continuousH1SrMap` is the corresponding restricted linear map.
--
--   **Relation to Mathlib.** Mathlib provides the functoriality of group cohomology (`groupCohomology.map`, `mapCocycles₁`, `H1π`), which the degree-one maps here restrict to the $S$-level submodules; the $S$-level cochain, cocycle and coboundary submodules and the quotient `continuousH2Sr` are project notions, and the degree-two maps are constructed at the level of cochains.
--
--   **Where it is used.** The $S$-level continuous cohomology groups model Galois cohomology with ramification restricted outside $S$, as used in the Selmer-group estimates of the Fermat deduction; the maps defined here are those occurring in the associated long exact sequences, in restriction and conjugation comparisons between level maps, and in the passage from $S$ to a larger set of primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousUnramifiedLevelMap.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {k : Type u} [CommRing k] {G H I : Type u} [Group G] [Group H] [Group I]
variable {rI : I →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (f : G →* H) (hf : ∀ g, rH (f g) = rG g) (S : Finset Nat.Primes)

section precomp

include hf

lemma IsLevelConstantSr₁.precomp {X : Type*} {x : H → X} (hx : IsLevelConstantSr₁ rH S x) : IsLevelConstantSr₁ rG S (x ∘ f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  exact h (f g) (f s) (by rwa [hf])

lemma IsLevelConstantSr₂.precomp {X : Type*} {x : H × H → X} (hx : IsLevelConstantSr₂ rH S x) :
    IsLevelConstantSr₂ rG S (x ∘ Prod.map f f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  exact h (f g) (f g') (f s) (f s') (by rwa [hf]) (by rwa [hf])

end precomp

section degreeTwo

variable {A : Rep k H} {B : Rep k G} (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a))

include hf in
lemma cochainsPullPush₁_mem_levelCochainsSr₁ {x : H → A} (hx : x ∈ levelCochainsSr₁ rH S A) :
    cochainsPullPush₁ f φ x ∈ levelCochainsSr₁ rG S B :=
  ((IsLevelConstantSr₁.precomp f hf S hx).comp φ :)

include hf in
lemma cochainsPullPush₂_mem_levelCochainsSr₂ {x : H × H → A} (hx : x ∈ levelCochainsSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCochainsSr₂ rG S B :=
  ((IsLevelConstantSr₂.precomp f hf S hx).comp φ :)

include hf hφ in
lemma cochainsPullPush₂_mem_levelCocyclesSr₂ {x : H × H → A} (hx : x ∈ levelCocyclesSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCocyclesSr₂ rG S B :=
  ⟨cochainsPullPush₂_mem_cocycles₂ f φ hφ hx.1, cochainsPullPush₂_mem_levelCochainsSr₂ f hf S φ hx.2⟩

include hf hφ in
lemma cochainsPullPush₂_mem_levelCoboundariesSr₂ {x : H × H → A} (hx : x ∈ levelCoboundariesSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCoboundariesSr₂ rG S B := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundariesSr₂_iff rH S A x).1 hx
  exact (mem_levelCoboundariesSr₂_iff rG S B _).2
    ⟨cochainsPullPush₁ f φ y, (IsLevelConstantSr₁.precomp f hf S hy).comp φ, (cochainsPullPush₂_d₁₂ f φ hφ y).symm⟩

def levelCocyclesSr₂Map : ↥(levelCocyclesSr₂ rH S A) →ₗ[k] ↥(levelCocyclesSr₂ rG S B) :=
  (cochainsPullPush₂ f φ).restrict fun _ hx => cochainsPullPush₂_mem_levelCocyclesSr₂ f hf S φ hφ hx

@[simp] lemma coe_levelCocyclesSr₂Map (x : ↥(levelCocyclesSr₂ rH S A)) :
    (levelCocyclesSr₂Map f hf S φ hφ x : G × G → B) = cochainsPullPush₂ f φ x := rfl

def continuousH2SrMap : continuousH2Sr rH S A →ₗ[k] continuousH2Sr rG S B :=
  Submodule.mapQ _ _ (levelCocyclesSr₂Map f hf S φ hφ) fun _ hx => cochainsPullPush₂_mem_levelCoboundariesSr₂ f hf S φ hφ hx

@[simp] lemma continuousH2SrMap_continuousH2Srπ (x : ↥(levelCocyclesSr₂ rH S A)) :
    continuousH2SrMap f hf S φ hφ (continuousH2Srπ rH S A x) = continuousH2Srπ rG S B (levelCocyclesSr₂Map f hf S φ hφ x) := rfl

lemma continuousH2SrToContinuousH2_comp_continuousH2SrMap :
    continuousH2SrToContinuousH2 rG S B ∘ₗ continuousH2SrMap f hf S φ hφ =
      continuousH2Map f hf φ hφ ∘ₗ continuousH2SrToContinuousH2 rH S A :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

variable {S} in

lemma continuousH2SrOfLE_comp_continuousH2SrMap {S' : Finset Nat.Primes} (h : S ⊆ S') :
    continuousH2SrOfLE rG B h ∘ₗ continuousH2SrMap f hf S φ hφ = continuousH2SrMap f hf S' φ hφ ∘ₗ continuousH2SrOfLE rH A h :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end degreeTwo

section laws

variable {A : Rep k G}

lemma continuousH2SrMap_id :
    continuousH2SrMap (rH := rG) (MonoidHom.id G) (fun _ => rfl) S (LinearMap.id : A →ₗ[k] A) (fun _ _ => rfl) = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

variable {B : Rep k H} {C : Rep k I} (f' : H →* I) (hf' : ∀ h, rI (f' h) = rH h)
  (ψ : C →ₗ[k] B) (hψ : ∀ (h : H) (c : C), ψ (C.ρ (f' h) c) = B.ρ h (ψ c))
  (φ : B →ₗ[k] A) (hφ : ∀ (g : G) (b : B), φ (B.ρ (f g) b) = A.ρ g (φ b))

lemma continuousH2SrMap_comp :
    continuousH2SrMap (f'.comp f) (fun g => by rw [MonoidHom.comp_apply, hf', hf]) S (φ ∘ₗ ψ)
        (fun g c => by rw [LinearMap.comp_apply, LinearMap.comp_apply, MonoidHom.comp_apply, hψ, hφ]) =
      continuousH2SrMap f hf S φ hφ ∘ₗ continuousH2SrMap f' hf' S ψ hψ :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end laws

section sameGroup

variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep k G}

abbrev continuousH2SrMapHom (φ : A ⟶ B) : continuousH2Sr r S A →ₗ[k] continuousH2Sr r S B :=
  continuousH2SrMap (MonoidHom.id G) (fun _ => rfl) S φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a)

lemma continuousH2SrMapHom_continuousH2Srπ (φ : A ⟶ B) (x : ↥(levelCocyclesSr₂ r S A)) :
    continuousH2SrMapHom S r φ (continuousH2Srπ r S A x) =
      continuousH2Srπ r S B (levelCocyclesSr₂Map (MonoidHom.id G) (fun _ => rfl) S φ.hom.toLinearMap
        (fun g a => Rep.hom_comm_apply φ g a) x) := rfl

lemma continuousH2SrMapHom_id : continuousH2SrMapHom S r (𝟙 A) = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

lemma continuousH2SrMapHom_comp (φ : A ⟶ B) (ψ : B ⟶ C) :
    continuousH2SrMapHom S r (φ ≫ ψ) = continuousH2SrMapHom S r ψ ∘ₗ continuousH2SrMapHom S r φ :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end sameGroup

section degreeOne

variable {A : Rep k H} {B : Rep k G} (φ : Rep.res f A ⟶ B)

lemma coe_mapCocycles₁_apply (c : cocycles₁ A) (g : G) : (mapCocycles₁ f φ c : G → B) g = φ.hom (c (f g)) := rfl

lemma map_hom_H1π (c : cocycles₁ A) :
    (groupCohomology.map f φ 1).hom ((H1π A).hom c) = (H1π B).hom (mapCocycles₁ f φ c) := by
  change (H1π A ≫ groupCohomology.map f φ 1).hom c = (mapCocycles₁ f φ ≫ H1π B).hom c
  rw [H1π_comp_map]

include hf in

lemma map_continuousH1Sr_le :
    (continuousH1Sr rH S A).map (groupCohomology.map f φ 1).hom ≤ continuousH1Sr rG S B := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff rH S A x).1 hx
  rw [map_hom_H1π]
  refine H1π_mem_continuousH1Sr rG S B ?_
  have hfun : ((mapCocycles₁ f φ c : cocycles₁ B) : G → B) = φ.hom ∘ (c : H → A) ∘ f :=
    funext fun g => coe_mapCocycles₁_apply f φ c g
  rw [hfun]
  exact (IsLevelConstantSr₁.precomp f hf S hc).comp φ.hom

def continuousH1SrMap : ↥(continuousH1Sr rH S A) →ₗ[k] ↥(continuousH1Sr rG S B) :=
  (groupCohomology.map f φ 1).hom.restrict fun x hx => map_continuousH1Sr_le f hf S φ ⟨x, hx, rfl⟩

@[simp] lemma coe_continuousH1SrMap_apply (x : ↥(continuousH1Sr rH S A)) :
    (continuousH1SrMap f hf S φ x : H1 B) = (groupCohomology.map f φ 1).hom x := rfl

end degreeOne

end groupCohomology

end


