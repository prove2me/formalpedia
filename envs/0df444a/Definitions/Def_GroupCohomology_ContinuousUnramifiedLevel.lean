-- Prove2me | Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
-- name    : GroupCohomology_ContinuousUnramifiedLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/61f8ec26-a72d-5056-a183-4e15da346a22
-- title:
--   Level-constant cochains with ramification restricted outside S
-- statement:
--   Throughout, $G$ is a group, $r\colon G\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ a homomorphism into the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, and $S$ a finite set of rational primes. The two basic predicates are `IsLevelConstantSr₁` and `IsLevelConstantSr₂`: a function $f$ on $G$ (resp. on $G\times G$) has the property when there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ with `F.IsUnramifiedOutside S` — that is, $F/\mathbb Q$ is finite and for every prime $q\notin S$ and every valuation subring of $\overline{\mathbb Q}$ lying over $q$ the associated inertia subgroup over $\mathbb Q$ lies in the pointwise fixing subgroup of $F$ — such that $f(gs)=f(g)$ for all $g,s$ with $r(s)$ fixing $F$ pointwise (resp. $f(gs,g's')=f(g,g')$ whenever $r(s)$ and $r(s')$ both fix $F$). Taking $r=\mathrm{id}$ recovers `IsLevelConstantS₁`/`IsLevelConstantS₂` exactly; dropping the unramifiedness clause and keeping only finiteness of $F$ gives `IsLevelConstant₁`/`IsLevelConstant₂`, so each $S$-version implies the corresponding unrestricted one. Further lemmas record stability under addition (using $F\sqcup F'$), constancy, post-composition with any map of target types, enlargement of $S$, and pullback along a homomorphism $\iota\colon G'\to G$ with $r$ replaced by $r\circ\iota$.
--
--   For `M : Rep k G` over a commutative ring $k$ these predicates cut out submodules `levelCochainsSr₁` and `levelCochainsSr₂` of the degree-one and degree-two inhomogeneous cochains, contained in `levelCochains₁`/`levelCochains₂`. From them: `levelCocyclesSr₁`, the level-constant $1$-cocycles; `continuousH1Sr`, their image in $H^1(G,M)$ under `H1π`; `levelCocyclesSr₂`, the intersection of `cocycles₂ M` with `levelCochainsSr₂`; `levelCoboundariesSr₂`, the image of `levelCochainsSr₁` under $d_{12}$; and `continuousH2Sr`, the quotient of `levelCocyclesSr₂` by the part of `levelCoboundariesSr₂` lying inside it, with projection `continuousH2Srπ` (surjective, with the expected vanishing criterion). The comparison maps `continuousH2SrToContinuousH2` and, for $S\subseteq S'$, `continuousH1Sr_mono`, `levelCocyclesSr₂_mono` and `continuousH2SrOfLE` relate these to the unrestricted continuous cohomology and to larger ramification sets.
--
--   **Relation to Mathlib.** The underlying low-degree cochain objects (`cocycles₁`, `cocycles₂`, `d₁₂`, `H1`, `H1π`, `H2`, `Rep`) and `IntermediateField.fixingSubgroup` are Mathlib's; the level-constancy predicates, the restricted-ramification cochain submodules and the resulting $H^1$ and $H^2$ carriers are the project's own, Mathlib having no continuous cohomology of profinite Galois groups.
--
--   **Where it is used.** These carriers are the ambient cohomology groups in which the project's Selmer groups with prescribed local conditions and restricted ramification live, both globally and, after composing $r$ with the inclusion of a decomposition group, locally; the maps in $S$ and to the unrestricted groups supply the comparisons needed when the ramification set is enlarged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousUnramifiedLevel.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

def IsLevelConstantSr₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantSr₂ {X : Type*} (f : G × G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

lemma isLevelConstantSr₁_id_iff {X : Type*} (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) :
    IsLevelConstantSr₁ (MonoidHom.id _) S f ↔ IsLevelConstantS₁ S f := Iff.rfl

lemma isLevelConstantSr₂_id_iff {X : Type*}
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) :
    IsLevelConstantSr₂ (MonoidHom.id _) S f ↔ IsLevelConstantS₂ S f := Iff.rfl

variable {r S}

lemma IsLevelConstantSr₁.isLevelConstant₁ {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : IsLevelConstant₁ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩

lemma IsLevelConstantSr₂.isLevelConstant₂ {X : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) : IsLevelConstant₂ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩

lemma IsLevelConstantSr₁.add {X : Type*} [Add X] {f f' : G → X} (hf : IsLevelConstantSr₁ r S f) (hf' : IsLevelConstantSr₁ r S f') :
    IsLevelConstantSr₁ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

lemma IsLevelConstantSr₂.add {X : Type*} [Add X] {f f' : G × G → X} (hf : IsLevelConstantSr₂ r S f)
    (hf' : IsLevelConstantSr₂ r S f') : IsLevelConstantSr₂ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

variable (r S) in
lemma isLevelConstantSr₁_const {X : Type*} (x : X) : IsLevelConstantSr₁ r S (fun _ : G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

variable (r S) in
lemma isLevelConstantSr₂_const {X : Type*} (x : X) : IsLevelConstantSr₂ r S (fun _ : G × G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩

lemma IsLevelConstantSr₁.comp {X Y : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) (φ : X → Y) :
    IsLevelConstantSr₁ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

lemma IsLevelConstantSr₂.comp {X Y : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) (φ : X → Y) :
    IsLevelConstantSr₂ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

lemma IsLevelConstantSr₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    IsLevelConstantSr₁ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

lemma IsLevelConstantSr₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G × G → X}
    (hf : IsLevelConstantSr₂ r S f) : IsLevelConstantSr₂ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

lemma IsLevelConstantSr₁.of_comp {G' : Type*} [Group G'] (ι : G' →* G) {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    IsLevelConstantSr₁ (r.comp ι) S (f ∘ ι) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, map_mul, h (ι g) (ι s) hs]⟩

lemma IsLevelConstantSr₂.of_comp {G' : Type*} [Group G'] (ι : G' →* G) {X : Type*} {f : G × G → X}
    (hf : IsLevelConstantSr₂ r S f) : IsLevelConstantSr₂ (r.comp ι) S (f ∘ Prod.map ι ι) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, Prod.map_apply, map_mul, h _ _ _ _ hs hs']⟩

section carriers

variable (r S) {k : Type u} [CommRing k] (M : Rep k G)

def levelCochainsSr₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstantSr₁ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₁_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochainsSr₂ : Submodule k (G × G → M) where
  carrier := {f | IsLevelConstantSr₂ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₂_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

lemma mem_levelCochainsSr₁_iff (f : G → M) : f ∈ levelCochainsSr₁ r S M ↔ IsLevelConstantSr₁ r S f := Iff.rfl

lemma mem_levelCochainsSr₂_iff (f : G × G → M) : f ∈ levelCochainsSr₂ r S M ↔ IsLevelConstantSr₂ r S f := Iff.rfl

lemma levelCochainsSr₁_le_levelCochains₁ : levelCochainsSr₁ r S M ≤ levelCochains₁ r M :=
  fun _ hf => hf.isLevelConstant₁

lemma levelCochainsSr₂_le_levelCochains₂ : levelCochainsSr₂ r S M ≤ levelCochains₂ r M :=
  fun _ hf => hf.isLevelConstant₂

def levelCocyclesSr₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsSr₁ r S M).comap (cocycles₁ M).subtype

lemma mem_levelCocyclesSr₁_iff (c : cocycles₁ M) : c ∈ levelCocyclesSr₁ r S M ↔ IsLevelConstantSr₁ r S c := Iff.rfl

def continuousH1Sr : Submodule k (H1 M) :=
  (levelCocyclesSr₁ r S M).map (H1π M).hom

lemma mem_continuousH1Sr_iff (x : H1 M) :
    x ∈ continuousH1Sr r S M ↔ ∃ c : cocycles₁ M, IsLevelConstantSr₁ r S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1Sr, Submodule.mem_map, mem_levelCocyclesSr₁_iff]

lemma H1π_mem_continuousH1Sr {c : cocycles₁ M} (hc : IsLevelConstantSr₁ r S c) : (H1π M).hom c ∈ continuousH1Sr r S M :=
  (mem_continuousH1Sr_iff r S M _).2 ⟨c, hc, rfl⟩

lemma continuousH1Sr_le_continuousH1 : continuousH1Sr r S M ≤ continuousH1 r M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact H1π_mem_continuousH1 r M hc.isLevelConstant₁

variable {S} in

lemma continuousH1Sr_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1Sr r S M ≤ continuousH1Sr r S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact (mem_continuousH1Sr_iff r S' M _).2 ⟨c, hc.mono h, rfl⟩

def levelCocyclesSr₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochainsSr₂ r S M

def levelCoboundariesSr₂ : Submodule k (G × G → M) :=
  (levelCochainsSr₁ r S M).map (d₁₂ M).hom

lemma mem_levelCocyclesSr₂_iff (f : G × G → M) : f ∈ levelCocyclesSr₂ r S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantSr₂ r S f :=
  Iff.rfl

lemma mem_levelCoboundariesSr₂_iff (f : G × G → M) :
    f ∈ levelCoboundariesSr₂ r S M ↔ ∃ x : G → M, IsLevelConstantSr₁ r S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesSr₂, Submodule.mem_map, mem_levelCochainsSr₁_iff]

lemma levelCocyclesSr₂_le_levelCocycles₂ : levelCocyclesSr₂ r S M ≤ levelCocycles₂ r M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩

lemma levelCocyclesSr₂_le_cocycles₂ : levelCocyclesSr₂ r S M ≤ cocycles₂ M := fun _ h => h.1

lemma levelCoboundariesSr₂_le_levelCoboundaries₂ : levelCoboundariesSr₂ r S M ≤ levelCoboundaries₂ r M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesSr₂_iff r S M f).1 hf
  exact (mem_levelCoboundaries₂_iff r M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩

lemma levelCoboundariesSr₂_le_coboundaries₂ : levelCoboundariesSr₂ r S M ≤ coboundaries₂ M :=
  (levelCoboundariesSr₂_le_levelCoboundaries₂ r S M).trans (levelCoboundaries₂_le_coboundaries₂ r M)

variable {S} in
lemma levelCocyclesSr₂_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : levelCocyclesSr₂ r S M ≤ levelCocyclesSr₂ r S' M :=
  fun _ hf => ⟨hf.1, hf.2.mono h⟩

abbrev continuousH2Sr : Type u :=
  ↥(levelCocyclesSr₂ r S M) ⧸ (levelCoboundariesSr₂ r S M).comap (levelCocyclesSr₂ r S M).subtype

abbrev continuousH2Srπ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] continuousH2Sr r S M :=
  Submodule.mkQ _

lemma continuousH2Srπ_eq_zero_iff (f : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2Srπ r S M f = 0 ↔ (f : G × G → M) ∈ levelCoboundariesSr₂ r S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

lemma continuousH2Srπ_surjective : Function.Surjective (continuousH2Srπ r S M) :=
  Submodule.mkQ_surjective _

def levelCocyclesSr₂ToLevelCocycles₂ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] ↥(levelCocycles₂ r M) :=
  Submodule.inclusion (levelCocyclesSr₂_le_levelCocycles₂ r S M)

def continuousH2SrToContinuousH2 : continuousH2Sr r S M →ₗ[k] continuousH2 r M :=
  Submodule.mapQ _ _ (levelCocyclesSr₂ToLevelCocycles₂ r S M) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    exact levelCoboundariesSr₂_le_levelCoboundaries₂ r S M hc)

lemma continuousH2SrToContinuousH2_mk (c : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2SrToContinuousH2 r S M (continuousH2Srπ r S M c) = continuousH2π r M (levelCocyclesSr₂ToLevelCocycles₂ r S M c) := rfl

variable {S} in

def continuousH2SrOfLE {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH2Sr r S M →ₗ[k] continuousH2Sr r S' M :=
  Submodule.mapQ _ _ (Submodule.inclusion (levelCocyclesSr₂_mono r M h)) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    obtain ⟨x, hx, hxc⟩ := (mem_levelCoboundariesSr₂_iff r S M _).1 hc
    exact (mem_levelCoboundariesSr₂_iff r S' M _).2 ⟨x, hx.mono h, hxc⟩)

end carriers

end groupCohomology

end


