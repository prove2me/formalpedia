-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv
-- name    : Mathlib_Topology_Algebra_RestrictedProduct_Equiv
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/76787011-8897-52f2-bcbc-0d81d06e01f8
-- title:
--   Equivalences of restricted products: factorwise, reindexing, flattening, decompositions
-- statement:
--   Throughout, $\Pi^{r}_{i}\,[R_i, A_i]_{\mathcal F}$ denotes the restricted product of a family $R_i$ with respect to subsets (or sub-structures) $A_i$ along a filter $\mathcal F$ on the index type: families $x$ with $x_i \in A_i$ for $\mathcal F$-almost all $i$.
--
--   The first group of definitions varies the factors. Given bijections $\varphi_i : R_{1,i} \simeq R_{2,i}$ such that $\varphi_i$ restricts to a bijection of $A_{1,i}$ onto $A_{2,i}$ for $\mathcal F$-almost all $i$, [`Equiv.restrictedProductCongrRight`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L17) is the induced bijection of restricted products, acting componentwise; `MulEquiv`, `AddEquiv`, `RingEquiv` and `LinearEquiv` versions upgrade this when the $A_i$ are submonoids, subsemirings, or additive submonoids stable under the scalars. [`MulEquiv.restrictedProductUnits`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L40) identifies the unit group of a restricted product of monoids with the restricted product of the unit groups $(M_i)^\times$ taken with respect to the units of the submonoids $A_i$.
--
--   The second group varies the index. For $e : \iota_1 \simeq \iota_2$ with $\mathcal F_2 = e_*\mathcal F_1$ (respectively $\mathcal F_1 = e^*\mathcal F_2$), [`Equiv.restrictedProductCongrLeft'`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L104) and [`Equiv.restrictedProductCongrLeft`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L127) are the reindexing bijections, again with monoid, additive, ring and linear versions, together with the expected formulae for their values. [`Equiv.restrictedProductCongr`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L240) and its algebraic analogues combine both, from data $e$, $\varphi_i : R_{1,i} \simeq R_{2,e(i)}$ and an eventual bijectivity hypothesis, and send $x$ to the family $e(i) \mapsto \varphi_i(x_i)$. [`RingEquiv.restrictedProductCongr_bijOn_structureSubring`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L364) records that if bijectivity holds at every index, the resulting ring equivalence carries the subring of elements lying in $A_{1,i}$ for all $i$ bijectively onto its counterpart.
--
--   The remaining definitions are structural decompositions: restricted products commute with binary products, with finite products and with matrix formation; [`RestrictedProduct.flatten`](../def/Mathlib_Topology_Algebra_RestrictedProduct_Equiv.html#L441), `flatten_equiv` and `flatten_equiv'` group the factors along a map $f$ of index types with appropriate filter compatibility; and `principalEquivProd`, with its monoid, additive and module versions, identifies a restricted product along a principal filter $\mathcal P(S)$ with $\left(\prod_{i \in S} A_i\right) \times \prod_{i \notin S} R_i$.
--
--   **Relation to Mathlib.** These are additions to Mathlib's `RestrictedProduct` theory, in the style of its basic API (`map`, `mapAlong`, `inclusion`, `structureMap`), supplying congruence, flattening and principal-filter decomposition equivalences.
--
--   **Where it is used.** Restricted products along the cofinite filter are the ambient model for rings of finite adeles and their matrix and unit groups; these equivalences are what permits reindexing, change of coefficient family, and the splitting of an adelic object into its finitely many distinguished components and the rest.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri; `FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone; `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv.lean

import Mathlib
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

open RestrictedProduct

section pi_congr_right

variable {ι : Type*}
variable {R₁ : ι → Type*} {R₂ : ι → Type*} {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}
variable {𝓕 : Filter ι}

@[simps]
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  left_inv x := by ext; simp
  right_inv x := by ext; simp

section add_mul_equiv

variable [(i : ι) → Monoid (R₁ i)] [(i : ι) → Monoid (R₂ i)]
  [(i : ι) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → SubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

@[to_additive (attr := simps! apply)
                                ]
def MulEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := Equiv.restrictedProductCongrRight _ hφ
  map_mul' _ _ := by ext; simp

def MulEquiv.restrictedProductUnits {ι : Type*} {ℱ : Filter ι}
    {M : ι → Type*} [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    {A : Π i, S i} :
    (Πʳ i, [M i, A i]_[ℱ])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]_[ℱ] where
        toFun u := ⟨fun i ↦ ⟨u.1 i, u⁻¹.1 i, congr($u.mul_inv i), congr($u.inv_mul i)⟩,
          by filter_upwards [u.val.2, u⁻¹.val.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
        invFun ui := ⟨⟨fun i ↦ ui i, by filter_upwards [ui.2] using fun i hi ↦ hi.1⟩,
          ⟨fun i ↦ ui⁻¹ i, by filter_upwards [ui⁻¹.2] using fun i hi ↦ hi.1⟩,
          by ext i; exact (ui i).mul_inv,
          by ext i; exact (ui i).inv_mul⟩
        left_inv u := by ext; rfl
        right_inv ui := by ext; rfl
        map_mul' u v := by ext; rfl

end add_mul_equiv

section ring_equiv

variable [(i : ι) → Semiring (R₁ i)] [(i : ι) → Semiring (R₂ i)]
  [(i : ι) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

@[simps! apply]
def RingEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃+* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃+* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext; simp [AddEquiv.restrictedProductCongrRight]

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]
variable [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]
variable [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
variable [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]

def LinearEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv)
    (by filter_upwards [hφ]; exact fun i ↦ id)
  map_smul' m x := by
    ext i
    apply map_smul

end linear_equiv

end pi_congr_right

section pi_congr_left

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

@[simps! apply, simps -isSimp symm_apply]
def Equiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂] where
  toFun x := ⟨fun i ↦ e.piCongrLeft' _ x i, by
    have := x.eventually
    simp only [piCongrLeft'_apply, h, Filter.eventually_map]; grind⟩
  invFun y := ⟨fun j ↦ (e.piCongrLeft' _).symm y j, by
    have := y.eventually
    simp_rw [h] at this
    have := Filter.eventually_map.1 this
    simp only [piCongrLeft'_symm_apply]; grind⟩
  left_inv x := by
    ext i
    exact funext_iff.1 ((e.piCongrLeft' _).left_inv x) i
  right_inv y := by
    ext j
    exact funext_iff.1 ((e.piCongrLeft' _).right_inv y) j

@[simp]
theorem Equiv.restrictedProductCongrLeft'_symm_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e)
    (x : Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) (j : ι₂) :
    (restrictedProductCongrLeft' e h).symm x (e.symm j) = x j := by
  simp [restrictedProductCongrLeft'_symm_apply]

def Equiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ((e.symm).restrictedProductCongrLeft' (𝓕₂.map_equiv_symm _ ▸ h)).symm

@[simp]
theorem Equiv.restrictedProductCongrLeft_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (x : Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁]) (i : ι₁) :
    (restrictedProductCongrLeft e h) x (e i) = x i :=
  restrictedProductCongrLeft'_symm_apply_apply e.symm (𝓕₂.map_equiv_symm _ ▸ h) x _

#adaptation_note /-- to_additive started failing in 4.28.0 . This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes -/
section add_equiv

variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

@[simps! apply]
def AddEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_add' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']

def AddEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_add' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end add_equiv

section mul_equiv

variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

def MulEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']

def MulEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end mul_equiv

section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

@[simps! apply]
def RingEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := rfl

def RingEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]
  [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]

@[simps! apply]
def LinearEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_smul' _ _ := rfl

def LinearEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ₗ[T] Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]

end linear_equiv

end pi_congr_left

section pi_congr

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

def Equiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  (Equiv.restrictedProductCongrRight φ hφ).trans
    (e.restrictedProductCongrLeft h)

@[simp]
theorem Equiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    e.restrictedProductCongr h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem Equiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (e.restrictedProductCongr h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

#adaptation_note /-- to_additive started failing in 4.28.0.
This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes  -/
section add_equiv

variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

@[simps! apply]
def AddEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_add' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

end add_equiv

section mul_equiv

variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

def MulEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

end mul_equiv

section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

def RingEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

@[simp]
theorem RingEquiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    RingEquiv.restrictedProductCongr e h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem RingEquiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (RingEquiv.restrictedProductCongr e h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}
variable [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]

def LinearEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ₗ[T] R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end linear_equiv

end pi_congr

section structure_map

variable {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
  {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂} {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable [(i : ι₁) → Ring (R₁ i)] [(i : ι₂) → Ring (R₂ i)]
  [(i : ι₁) → SubringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubringClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

theorem RingEquiv.restrictedProductCongr_bijOn_structureSubring (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ i, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Set.BijOn (restrictedProductCongr e h φ (.of_forall hφ))
      (structureSubring R₁ A₁ 𝓕₁) (structureSubring R₂ A₂ 𝓕₂) := by
  have hm (i : _) := (hφ i).mapsTo
  have hs (i : _) := (hφ i).symm (φ i).toEquiv.invOn |>.mapsTo
  refine ⟨fun x hx ↦ ?_, (RingEquiv.injective _).injOn, fun y hy ↦ ?_⟩
  · refine mem_structureSubring_iff.2 fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    aesop
  · exact ⟨(restrictedProductCongr e h φ (.of_forall hφ)).symm y, by aesop⟩

end structure_map

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}

@[simps]
def Equiv.restrictedProductProd :
    Πʳ i, [A i × B i, C i ×ˢ D i]_[ℱ] ≃ (Πʳ i, [A i, C i]_[ℱ]) × (Πʳ i, [B i, D i]_[ℱ]) where
  toFun x := (map (fun i (t : A i × B i) ↦ t.1) (by simp +contextual [Set.MapsTo]) x,
              map (fun i (t : A i × B i) ↦ t.2) (by simp +contextual [Set.MapsTo]) x)
  invFun yz :=
    ⟨fun i ↦ (yz.1 i, yz.2 i), by
    filter_upwards [yz.1.2, yz.2.2] with i using Set.mk_mem_prod⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

lemma Equiv.restrictedProductProd_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductProd.symm ∘ Prod.map (inclusion _ _ hℱ) (inclusion _ _ hℱ) =
      inclusion (fun i ↦ A i × B i) (fun i ↦ C i ×ˢ D i) hℱ ∘ Equiv.restrictedProductProd.symm :=
  rfl

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

def Equiv.restrictedProductPi :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
  toFun x j := map (fun i t ↦ t _) (by simp +contextual [Set.MapsTo]) x
  invFun y := .mk (fun i j ↦ y j i) (by simp)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

lemma Equiv.restrictedProductPi_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductPi.symm ∘ Pi.map (fun i ↦ inclusion (A i) (C i) hℱ) =
      inclusion _ _ hℱ ∘ Equiv.restrictedProductPi.symm :=
  rfl

def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i]) :=
  Equiv.restrictedProductPi.trans (Equiv.piCongrRight fun _ ↦ Equiv.restrictedProductPi)

end pi

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in

def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)

def flatten_equiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl

@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flatten_equiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

def flatten_equiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flatten_equiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flatten_equiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten

section principal

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

section type

def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  toFun x := (fun i ↦ ⟨x i, x.2 i.2⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  by aesop⟩
  left_inv x := by ext; simp
  right_inv x := by
    ext i
    · simp
    · simp [dif_neg i.2]

end type

variable {T : ι → Type*} [Π i, SetLike (T i) (R i)] {A : Π i, T i}

section monoid

@[to_additive                                                          ]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl

end monoid

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]

open scoped RestrictedProduct

open Filter

section module

noncomputable def principalLinearEquivProd [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
    (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] ((Π i : S, C i) ×
      (Π i : (Sᶜ : Set ι), R i)) where
  __ := principalAddEquivSum R S (A := C)
  map_smul' _ _ := rfl

end module

end principal

end RestrictedProduct


