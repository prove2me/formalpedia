-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic
-- name    : Mathlib_Topology_Algebra_RestrictedProduct_Basic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/61cdca5a-f30f-55c0-90b8-9203017678be
-- title:
--   Restricted products: linear maps, supports, structure subrings
-- statement:
--   Standing context: a family of objects indexed by $\iota$, a filter on the index set, and for each $i$ a distinguished subobject $B_i$ (or $A_i$, $C_i$) of $R_i$ given via a `SetLike` class, the restricted product $\Pi^{\mathrm{r}}_i [R_i, B_i]_{[\mathcal F]}$ consisting of those $x \in \prod_i R_i$ with $x_i \in B_i$ for $\mathcal F$-almost all $i$.
--
--   Four groups of declarations. (i) Functoriality for modules: given a semiring $A$, families of $A$-modules $R_1$ on $\iota_1$ and $R_2$ on $\iota_2$ with subobjects closed under addition and under the $A$-action, a map $f : \iota_2 \to \iota_1$ with $\mathrm{Tendsto}\ f\ \mathcal F_2\ \mathcal F_1$, and $A$-linear maps $\varphi_j : R_1(f(j)) \to R_2(j)$ such that $\varphi_j$ maps $B_1(f(j))$ into $B_2(j)$ for $\mathcal F_2$-almost all $j$, `mapAlongLinearMap` is the $A$-linear map of restricted products with $j$-component $x \mapsto \varphi_j(x_{f(j)})$; `inclusionLinearMap` is the special case $f = \mathrm{id}$, $\varphi = \mathrm{id}$ for submodules $C_i$ and filters $\mathcal F \le \mathcal G$, the identity on underlying functions. (ii) Supports: `mulSupport u` $= \{i : u_i \ne 1\}$ (additively `addSupport`), with the facts that elements with disjoint supports commute, that $\mathrm{mulSupport}(uv)$ lies in any set containing both supports, and that inversion preserves support; `indexSupport u` is the finite set of $i$ with $u_i \notin A_i$. The predicate `SubmonoidClass.isProductAt U i`, for a submonoid-like subobject $U$, asserts that every $u \in U$ factors as $u = u_i u_i'$ with both factors in $U$, $\mathrm{mulSupport}\,u_i \subseteq \{i\}$ and $i \notin \mathrm{mulSupport}\,u_i'$; the accompanying lemma shows that under this hypothesis each $\gamma \in U \cdot gU$, with $\mathrm{mulSupport}\,g \subseteq \{i\}$, has a representative of its coset $\gamma U$ supported in $\{i\}$. (iii) Componentwise maps: if $\varphi$ acts by $\varphi(x)_j = g_j(x_{f(j)})$ and $\{j\}^c$ lies in the filter, surjectivity of $\varphi$ gives surjectivity of each $g_j$, and when $\mathcal G = f^*\mathcal F$, almost all $g_j$ map $C_{f(j)}$ onto $C_{2,j}$; these rest on the ability to alter one coordinate arbitrarily. (iv) Structure maps: the monoid and ring homomorphisms $\prod_i A_i \to \Pi^{\mathrm{r}}_i[M_i, A_i]$, the subring `structureSubring` defined as the range of the latter, characterised by $x_i \in A_i$ for all $i$, and `singleAddMonoidHom`, sending $x \in A_j$ to `Pi.single j x`.
--
--   **Relation to Mathlib.** Mathlib supplies `RestrictedProduct` together with `structureMap` and `mapAlongAddMonoidHom`; this module adds the $A$-linear and ring-homomorphism versions, the support notions for restricted-product elements (analogous to Mathlib's `Function.mulSupport`), the subring of everywhere-integral elements, and the single-coordinate embedding.
--
--   **Where it is used.** Restricted products in this form are the ambient framework for the project's adelic and idelic constructions, where the subobjects are the local integral structures and the filter is the cofinite one; the support and one-coordinate-alteration lemmas are of the kind used to analyse open subgroups of idele groups and their cosets.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde; `FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone; `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {ℱ : Filter ι}
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

variable
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

end RestrictedProduct

open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)
variable {A : Type*} [Semiring A]
variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
    [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
    [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
    (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

def RestrictedProduct.mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a f := by
    ext i
    apply map_smul (φ i)

@[simp]
lemma RestrictedProduct.mapAlongLinearMap_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongLinearMap R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

def RestrictedProduct.inclusionLinearMap
     {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

lemma inclusionLinearMap_apply {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, C i]_[𝓖]) :
  inclusionLinearMap A R C h x = ⟨x.1, x.2.filter_mono h⟩ := rfl

end modules

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

namespace RestrictedProduct

section supports

variable {S T : ι → Type*}
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [(i : ι) → One (G i)] in

@[to_additive

                                                                  ]
def mulSupport (u : Πʳ i, [G i, A i]) : Set ι :=
  {i : ι | u i ≠ 1}

variable [(i : ι) → One (G i)] in
@[to_additive (attr := simp)]
lemma not_mem_mulSupport {u : Πʳ i, [G i, A i]} (i : ι) :
  i ∉ mulSupport u ↔ u i = 1 := by simp [mulSupport]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mul_comm_of_disjoint_mulSupport {u v : Πʳ i, [G i, A i]}
    (h : mulSupport u ∩ mulSupport v = ∅) : u * v = v * u := by
  ext i
  obtain hi | hi : i ∉ u.mulSupport ∨ i ∉ v.mulSupport := by
    rw [Set.ext_iff] at h
    specialize h i
    tauto
  · rw [not_mem_mulSupport] at hi
    simp [hi]
  · rw [not_mem_mulSupport] at hi
    simp [hi]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mulSupport_mul_subset {u v : Πʳ i, [G i, A i]} {J : Set ι} (hu : mulSupport u ⊆ J)
    (hv : mulSupport v ⊆ J) : mulSupport (u * v) ⊆ J := by
  intro i hi
  contrapose! hi
  simp [not_mem_mulSupport, (not_mem_mulSupport i).1 (fun a ↦ hi (hu a)),
    (not_mem_mulSupport i).1 (fun a ↦ hi (hv a))]

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)] in
@[to_additive (attr := simp)]
lemma mulSupport_inv {u : Πʳ i, [G i, A i]} : mulSupport u⁻¹ = mulSupport u := by
  ext i
  simp only [mulSupport]
  exact inv_ne_one

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubmonoidClass T (Πʳ i, [G i, A i])] in

def SubmonoidClass.isProductAt (U : T) (i : ι) : Prop :=
  ∀ u ∈ U, ∃ uᵢ, uᵢ ∈ U ∧ ∃ uᵢ', uᵢ' ∈ U ∧ u = uᵢ * uᵢ' ∧ mulSupport uᵢ ⊆ {i} ∧ i ∉ mulSupport uᵢ'

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubgroupClass T (Πʳ i, [G i, A i])] in
open scoped Pointwise in

lemma mem_coset_and_mulSupport_subset_of_isProductAt
    {U : T} (i : ι) (g : Πʳ i, [G i, A i])
    (hU : SubmonoidClass.isProductAt U i) (hg : mulSupport g ⊆ {i}) (γ : Πʳ i, [G i, A i])
    (hγ : γ ∈ U * g • (U : Set (Πʳ i, [G i, A i]))) :
    ∃ δ, δ ∈ γ • (U : Set (Πʳ i, [G i, A i])) ∧ mulSupport δ ⊆ {i} := by
  obtain ⟨u, hu, _, ⟨v, hv, rfl⟩, rfl⟩ := hγ
  obtain ⟨uᵢ, huᵢU, uᵢ', huᵢ'U, rfl, huᵢ, huᵢ'⟩ := hU u hu
  refine ⟨uᵢ * g, ⟨v⁻¹ * uᵢ'⁻¹, mul_mem (inv_mem hv) (inv_mem huᵢ'U), by
    have hcomm : g * uᵢ'⁻¹ = uᵢ'⁻¹ * g := mul_comm_of_disjoint_mulSupport <| by
      rw [mulSupport_inv]

      rw [Set.eq_empty_iff_forall_notMem]
      intro j ⟨hj1, hj2⟩
      apply huᵢ'
      apply hg at hj1
      simp_all
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left, hcomm]⟩,
    mulSupport_mul_subset huᵢ hg⟩

noncomputable
def indexSupport (u : Πʳ i, [G i, A i]) : Finset ι :=
  Set.Finite.toFinset (s := {x | u x ∉ A x}) (by have h := u.2; simp at h; exact h)

@[simp]
theorem mem_indexSupport_iff {u : Πʳ i, [G i, A i]} {i : ι} :
    i ∈ indexSupport u ↔ u i ∉ A i := by
  simp [indexSupport]

end supports

section components

variable {ι₂ : Type*} {f : ι₂ → ι} {𝒢 : Filter ι₂}
variable {G₂ : ι₂ → Type*} {C₂ : (i : ι₂) → Set (G₂ i)}
variable (hf : 𝒢 = Filter.comap f ℱ)
variable (φ : Πʳ i, [G i, C i]_[ℱ] → Πʳ i, [G₂ i, C₂ i]_[𝒢])
variable (g : (j : ι₂) → G (f j) → G₂ j) (hcomponent : ∀ x j, φ x j = g j (x (f j)))

include hcomponent in
variable {φ} {g} in
lemma components_comp_coe_eq_coe_apply : (fun a j ↦ g j (a (f j))) ∘ (⇑) = (⇑) ∘ φ := by
  ext x i
  simp [hcomponent]

lemma exists_update (x : Πʳ i, [G i, C i]_[ℱ]) (i : ι) (a : G i)
    (h : {i}ᶜ ∈ ℱ) : ∃ y : Πʳ i, [G i, C i]_[ℱ], y i = a ∧ ∀ j ≠ i, y j = x j := by
  classical
  exact ⟨⟨fun j ↦ if hj : j = i then hj ▸ a else x j, by
    filter_upwards [h, x.2] with j (hj : j ≠ i)
    aesop⟩, by
    aesop⟩

variable (C) in
lemma exists_apply_eq [∀ i, Nonempty (C i)] (i : ι) (a : G i) (h : {i}ᶜ ∈ ℱ) :
    ∃ x : Πʳ i, [G i, C i]_[ℱ], x i = a := by
  let y : Πʳ i, [G i, C i]_[ℱ] := ⟨fun i ↦ (Classical.ofNonempty : C i),
    Filter.Eventually.of_forall (fun x ↦ Subtype.coe_prop _)⟩
  obtain ⟨x, hx, -⟩ := exists_update y i a h
  exact ⟨x, hx⟩

variable [∀ j, Nonempty (C₂ j)]

include hcomponent in
lemma surjective_components_of_surjective (hφ : Function.Surjective φ) (j : ι₂) (hj : {j}ᶜ ∈ 𝒢) :
    Function.Surjective (g j) := by
  intro y
  obtain ⟨y', hy'⟩ := exists_apply_eq C₂ j y hj
  obtain ⟨x, hx⟩ := hφ y'
  use (x (f j))
  rw [← hcomponent, hx, hy']

include hf hcomponent in
lemma eventually_surjOn_of_surjective (hφ : Function.Surjective φ) :
    ∀ᶠ (j : ι₂) in 𝒢, Set.SurjOn (g j) (C (f j)) (C₂ j) := by
  classical
  have p (j : ι₂) : ∃ (y : C₂ j), (∃ (x : C (f j)), g j x = y)
       → Set.SurjOn (g j) (C (f j)) (C₂ j) := by
    by_cases hsurj : Set.SurjOn (g j) (C (f j)) (C₂ j)
    · exact ⟨Classical.choice inferInstance, fun _ ↦ hsurj⟩
    · rw [Set.SurjOn, Set.not_subset_iff_exists_mem_notMem] at hsurj
      obtain ⟨y, hy, hne⟩ := hsurj
      exact ⟨⟨y, hy⟩, fun ⟨⟨x, hx⟩, hxy⟩ ↦ absurd ⟨x, hx, hxy⟩ hne⟩
  choose y' hy' using p
  set y : Πʳ i, [G₂ i, C₂ i]_[𝒢] :=
    ⟨fun i ↦ y' i, Filter.Eventually.of_forall (fun i ↦ (y' i).prop)⟩ with hy
  obtain ⟨x, hx⟩ := hφ y
  rw [hf, Filter.eventually_comap]
  filter_upwards [x.eventually]
  rintro - hx' j rfl
  apply hy'
  use ⟨x (f j), hx'⟩
  rw [← hcomponent, hx, hy, mk_apply]

end components

section structure_map

@[to_additive
                                                                                     ]
def structureMapMonoidHom {ι : Type*} (M : ι → Type*) [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →* Πʳ (i : ι), [M i, Submonoid.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_one' := rfl
  map_mul' := by intros; rfl

def structureMapRingHom {ι : Type*} (M : ι → Type*) [(i : ι) → Ring (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubringClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →+* Πʳ (i : ι), [M i, Subring.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by intros; rfl
  map_add' := by intros; rfl

def structureSubring {ι : Type*} (R : ι → Type*) {S : ι → Type*}
    (A : (i : ι) → (S i)) (𝓕 : Filter ι) [(i : ι) → SetLike (S i) (R i)] [(i : ι) → Ring (R i)]
    [(i : ι) → SubringClass (S i) (R i)] :
    Subring (Πʳ i, [R i, A i]_[𝓕]) :=
  (RestrictedProduct.structureMapRingHom R A 𝓕).range

@[simp]
theorem mem_structureSubring_iff {ι : Type*} {R : ι → Type*} {S : ι → Type*}
    {A : (i : ι) → (S i)} {𝓕 : Filter ι} [(i : ι) → SetLike (S i) (R i)] [(i : ι) → Ring (R i)]
    [(i : ι) → SubringClass (S i) (R i)] {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ RestrictedProduct.structureSubring R A 𝓕 ↔
      ∀ i, x i ∈ A i := by
  rw [RestrictedProduct.structureSubring]
  change x ∈ Set.range (RestrictedProduct.structureMap _ _ _) ↔ _
  rw [RestrictedProduct.range_structureMap]
  aesop

end structure_map

section single

variable {ι : Type*} [DecidableEq ι] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddMonoid (A i)]
    [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

noncomputable def singleAddMonoidHom (j : ι) : A j →+ Πʳ i, [A i, B i] where
  toFun x := ⟨Pi.single j x, by
    simpa using (Set.finite_singleton j).subset fun i _ ↦ by by_cases h : i = j <;> simp_all⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Pi.single_add]

end single

end RestrictedProduct


