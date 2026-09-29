-- Prove2me | Definitions.Def_FiniteFlat_ClosureHopf
-- name    : FiniteFlat_ClosureHopf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/0f2b2976-1579-5917-8a8d-91b8d8c864a0
-- title:
--   Hopf structure maps on the schematic closure of a subalgebra
-- statement:
--   Throughout, $R$ is a commutative ring, $F$ a field that is an $R$-algebra, and $G$ a commutative ring; in the later sections $G$ carries an $R$-algebra, bialgebra or Hopf-algebra structure. For a subalgebra $B \subseteq F \otimes_R G$ of the generic fibre, [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19) is the $R$-subalgebra $\{g \in G : 1 \otimes g \in B\}$ of $G$. Two comparison maps are defined: [`tensorInclusion B`](../def/FiniteFlat_ClosureHopf.html#L22), the $R$-linear map $\mathrm{flatClosure}(B) \otimes_R \mathrm{flatClosure}(B) \to G \otimes_R G$ induced by the inclusion on both factors, whose range is [`closureTensorSpan B`](../def/FiniteFlat_ClosureHopf.html#L30), the $R$-span of $\{a \otimes b : a,b \in \mathrm{flatClosure}(B)\}$; and [`tensorToGenericFibre R F`](../def/FiniteFlat_ClosureHopf.html#L115), the map $G \otimes_R G \to (F \otimes_R G) \otimes_F (F \otimes_R G)$ with $g_1 \otimes g_2 \mapsto (1 \otimes g_1) \otimes_F (1 \otimes g_2)$, additive and semilinear along $R \to F$. When $R$ is a Noetherian principal ideal domain with fraction field $F$ and $G$ is a finite torsion-free $R$-module, both are injective, $\mathrm{flatClosure}(B)$ being free; moreover [`closureTensorSpan B`](../def/FiniteFlat_ClosureHopf.html#L30) is saturated ($r \cdot x$ in it with $r \neq 0$ forces $x$ in it, proved via a projection onto the closure along a complement), and $x \in G \otimes_R G$ lies in it as soon as its image in the generic fibre lies in the $F$-span of $B \otimes_F B$.
--
--   The predicate [`IsComulStable R F B`](../def/FiniteFlat_ClosureHopf.html#L232) says that for every $g \in \mathrm{flatClosure}(B)$ the image of $\Delta(g)$ under [`tensorToGenericFibre`](../def/FiniteFlat_ClosureHopf.html#L115) lies in the $F$-span of $\{b_1 \otimes_F b_2 : b_i \in B\}$ — a condition formulated through this comparison map rather than through a base-changed comultiplication. Under it, [`closureComul`](../def/FiniteFlat_ClosureHopf.html#L249) is the $R$-linear map $\mathrm{flatClosure}(B) \to \mathrm{flatClosure}(B) \otimes_R \mathrm{flatClosure}(B)$ characterised by [`tensorInclusion_closureComul`](../def/FiniteFlat_ClosureHopf.html#L260): composing with [`tensorInclusion`](../def/FiniteFlat_ClosureHopf.html#L22) returns $\Delta$ on the closure. [`closureCounit B`](../def/FiniteFlat_ClosureHopf.html#L269) is the restriction of the counit to a map $\mathrm{flatClosure}(B) \to R$; [`IsAntipodeStable R F B`](../def/FiniteFlat_ClosureHopf.html#L284) says the antipode maps $\mathrm{flatClosure}(B)$ into itself, and [`closureAntipode`](../def/FiniteFlat_ClosureHopf.html#L287) is the resulting $R$-linear endomorphism. These are structure maps only; no Hopf-algebra structure on the closure is assembled from them here. Finally [`genericFibreAlgHom B`](../def/FiniteFlat_ClosureHopf.html#L308) is the $F$-algebra map $F \otimes_R \mathrm{flatClosure}(B) \to F \otimes_R G$, $f \otimes h \mapsto f \otimes h$; for $R$ a domain with fraction field $F$ it is injective with image exactly $B$, yielding the $F$-algebra isomorphism [`genericFibreAlgEquiv`](../def/FiniteFlat_ClosureHopf.html#L360) : $F \otimes_R \mathrm{flatClosure}(B) \cong B$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (tensor products, `Bialgebra`/`HopfAlgebra` with `Coalgebra.comul`, `Coalgebra.counit`, `HopfAlgebra.antipode`, flatness and freeness over a principal ideal domain); [`flatClosure`](../def/FiniteFlat_SchematicClosure.html#L19) and the stability predicates [`IsComulStable`](../def/FiniteFlat_ClosureHopf.html#L232), [`IsAntipodeStable`](../def/FiniteFlat_ClosureHopf.html#L284) are the project's own.
--
--   **Where it is used.** This is the Hopf-algebraic form of the prolongation statement for subgroups of the generic fibre of a finite flat commutative group scheme over a discrete valuation ring: the schematic closure of a closed subgroup of the generic fibre inherits the structure maps, and its generic fibre recovers the given subgroup. It serves the treatment of finite flat group schemes that underlies the flat deformation condition in the modularity-lifting part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FiniteFlat_ClosureHopf.lean

import Mathlib
import Definitions.Def_FiniteFlat_SchematicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

section FlatClosureHopf

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 400000

section ModuleLevel

variable [Algebra R G]

noncomputable def tensorInclusion (B : Subalgebra F (F ⊗[R] G)) :
    (flatClosure B) ⊗[R] (flatClosure B) →ₗ[R] G ⊗[R] G :=
  TensorProduct.map (flatClosure B).val.toLinearMap (flatClosure B).val.toLinearMap

@[simp]
lemma tensorInclusion_tmul {B : Subalgebra F (F ⊗[R] G)} (x y : flatClosure B) :
    tensorInclusion B (x ⊗ₜ[R] y) = (x : G) ⊗ₜ[R] (y : G) := rfl

def closureTensorSpan (B : Subalgebra F (F ⊗[R] G)) : Submodule R (G ⊗[R] G) :=
  Submodule.span R (Set.image2 (· ⊗ₜ[R] ·) (flatClosure B : Set G) (flatClosure B : Set G))

lemma range_tensorInclusion (B : Subalgebra F (F ⊗[R] G)) :
    LinearMap.range (tensorInclusion B) = closureTensorSpan B := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨z, rfl⟩ := hx
    induction z with
    | zero => rw [map_zero]; exact (closureTensorSpan B).zero_mem
    | tmul a b =>
        rw [tensorInclusion_tmul]
        exact Submodule.subset_span (Set.mem_image2_of_mem a.2 b.2)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [closureTensorSpan, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : flatClosure B) ⊗ₜ[R] (⟨b, hb⟩ : flatClosure B), rfl⟩

theorem tensorInclusion_injective [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (tensorInclusion B) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R (flatClosure B) := flatClosure_free B
  have hι : Function.Injective ((flatClosure B).val.toLinearMap) := Subtype.val_injective
  have hfact : tensorInclusion B
      = ((flatClosure B).val.toLinearMap.rTensor G).comp
        ((flatClosure B).val.toLinearMap.lTensor (flatClosure B)) := by
    ext x y
    rfl
  rw [hfact, LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hι).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hι)

theorem mem_closureTensorSpan_of_smul_mem [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) {x : G ⊗[R] G} {r : R} (hr : r ≠ 0)
    (hx : r • x ∈ closureTensorSpan B) : x ∈ closureTensorSpan B := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'

  obtain ⟨C, hC⟩ := exists_isCompl_flatClosure (R := R) (F := F) (G := G) B
  set p : G →ₗ[R] G := (Subalgebra.toSubmodule (flatClosure B)).projection C hC with hp
  have hp_mem : ∀ g : G, p g ∈ flatClosure B := by
    intro g
    have h1 : p g ∈ Subalgebra.toSubmodule (flatClosure B) := by
      have h2 := Submodule.range_projection (p := Subalgebra.toSubmodule (flatClosure B))
        (q := C) hC
      exact h2 ▸ LinearMap.mem_range_self _ g
    simpa [Subalgebra.mem_toSubmodule] using h1
  have hp_fix : ∀ g : G, g ∈ flatClosure B → p g = g := by
    intro g hg
    rw [hp, Submodule.projection_eq_self_iff]
    simpa [Subalgebra.mem_toSubmodule] using hg

  set P : G ⊗[R] G →ₗ[R] G ⊗[R] G := TensorProduct.map p p with hP
  have hP_mem : ∀ z : G ⊗[R] G, P z ∈ closureTensorSpan B := by
    intro z
    induction z with
    | zero => rw [map_zero]; exact (closureTensorSpan B).zero_mem
    | tmul a b =>
        rw [hP, TensorProduct.map_tmul]
        exact Submodule.subset_span (Set.mem_image2_of_mem (hp_mem a) (hp_mem b))
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  have hP_fix : ∀ z, z ∈ closureTensorSpan B → P z = z := by
    intro z hz
    replace hz : z ∈ Submodule.span R
        (Set.image2 (· ⊗ₜ[R] ·) (flatClosure B : Set G) (flatClosure B : Set G)) := hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hw
        rw [hP, TensorProduct.map_tmul, hp_fix a ha, hp_fix b hb]
    | zero => rw [map_zero]
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂]
    | smul c w _ h => rw [map_smul, h]

  have h1 : P (r • x) = r • x := hP_fix _ hx
  have h2 : r • (P x - x) = 0 := by
    rw [smul_sub, ← map_smul, h1, sub_self]
  have h3 : P x = x := by
    rcases (Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance) r _ h2 with h | h
    · exact absurd h hr
    · exact sub_eq_zero.mp h
  exact h3 ▸ hP_mem x

variable (R F) in

noncomputable def tensorToGenericFibre (x : G ⊗[R] G) : (F ⊗[R] G) ⊗[F] (F ⊗[R] G) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R F F (F ⊗[R] G) G).symm
    ((LinearMap.rTensor G
      (Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).toLinearMap) x)

@[simp]
lemma tensorToGenericFibre_tmul (g₁ g₂ : G) :
    tensorToGenericFibre R F (g₁ ⊗ₜ[R] g₂)
      = ((1 : F) ⊗ₜ[R] g₁) ⊗ₜ[F] ((1 : F) ⊗ₜ[R] g₂) := by
  simp [tensorToGenericFibre]

lemma tensorToGenericFibre_zero : tensorToGenericFibre R F (0 : G ⊗[R] G) = 0 := by
  unfold tensorToGenericFibre
  rw [map_zero, map_zero]

lemma tensorToGenericFibre_add (x y : G ⊗[R] G) :
    tensorToGenericFibre R F (x + y)
      = tensorToGenericFibre R F x + tensorToGenericFibre R F y := by
  unfold tensorToGenericFibre
  rw [map_add, map_add]

lemma tensorToGenericFibre_smul (r : R) (x : G ⊗[R] G) :
    tensorToGenericFibre R F (r • x) = (algebraMap R F r) • tensorToGenericFibre R F x := by
  induction x with
  | zero => rw [smul_zero, tensorToGenericFibre_zero, smul_zero]
  | tmul g₁ g₂ =>
      simp only [TensorProduct.smul_tmul', tensorToGenericFibre_tmul, one_tmul_smul]
  | add x y hx hy =>
      rw [smul_add, tensorToGenericFibre_add, tensorToGenericFibre_add, hx, hy, smul_add]

theorem tensorToGenericFibre_injective [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G] :
    Function.Injective (tensorToGenericFibre R F (G := G)) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'

  have hφ : Function.Injective
      ((Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).toLinearMap) := by
    intro a b hab
    have key : ∀ g : G, ((Algebra.linearMap R F).rTensor G) ((TensorProduct.lid R G).symm g)
        = (1 : F) ⊗ₜ[R] g := by
      intro g
      simp
    have h1 : Function.Injective ((Algebra.linearMap R F).rTensor G) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R F)
    have h2 : (TensorProduct.lid R G).symm a = (TensorProduct.lid R G).symm b := by
      apply h1
      rw [key, key]
      simpa using hab
    exact (TensorProduct.lid R G).symm.injective h2

  intro x y hxy
  have h3 : Function.Injective ((Algebra.TensorProduct.includeRight
      (R := R) (A := F) (B := G)).toLinearMap.rTensor G) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hφ
  apply h3
  unfold tensorToGenericFibre at hxy
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
    R F F (F ⊗[R] G) G).symm.injective hxy

private lemma mul_smul_tmul (c₁ c₂ : F) (m n : F ⊗[R] G) :
    (c₁ * c₂) • (m ⊗ₜ[F] n) = (c₁ • m) ⊗ₜ[F] (c₂ • n) := by
  rw [mul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul, TensorProduct.smul_tmul']

theorem exists_smul_eq_tensorToGenericFibre_of_mem_span [IsDomain R] [IsFractionRing R F]
    {B : Subalgebra F (F ⊗[R] G)} {y : (F ⊗[R] G) ⊗[F] (F ⊗[R] G)}
    (hy : y ∈ Submodule.span F
      (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))) :
    ∃ (r : R) (z : G ⊗[R] G), r ≠ 0 ∧ z ∈ closureTensorSpan B ∧
      (algebraMap R F r) • y = tensorToGenericFibre R F z := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
      obtain ⟨r₁, g₁, hr₁, hg₁, e₁⟩ := exists_nonzero_smul_mem_flatClosure (R := R) (F := F) hb₁
      obtain ⟨r₂, g₂, hr₂, hg₂, e₂⟩ := exists_nonzero_smul_mem_flatClosure (R := R) (F := F) hb₂
      refine ⟨r₁ * r₂, g₁ ⊗ₜ[R] g₂, mul_ne_zero hr₁ hr₂,
        Submodule.subset_span (Set.mem_image2_of_mem hg₁ hg₂), ?_⟩
      rw [tensorToGenericFibre_tmul, ← e₁, ← e₂, map_mul, mul_smul_tmul]
  | zero =>
      exact ⟨1, 0, one_ne_zero, (closureTensorSpan B).zero_mem,
        by rw [smul_zero, tensorToGenericFibre_zero]⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
      obtain ⟨r₁, z₁, hr₁, hz₁, e₁⟩ := ih₁
      obtain ⟨r₂, z₂, hr₂, hz₂, e₂⟩ := ih₂
      refine ⟨r₁ * r₂, r₂ • z₁ + r₁ • z₂, mul_ne_zero hr₁ hr₂,
        add_mem (Submodule.smul_mem _ _ hz₁) (Submodule.smul_mem _ _ hz₂), ?_⟩
      rw [tensorToGenericFibre_add, tensorToGenericFibre_smul, tensorToGenericFibre_smul,
        ← e₁, ← e₂, map_mul]
      module
  | smul c y₁ _ ih =>
      obtain ⟨r, z, hr, hz, e⟩ := ih
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) c
      refine ⟨r * (s : R), a • z, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s),
        Submodule.smul_mem _ _ hz, ?_⟩
      rw [tensorToGenericFibre_smul, ← e, ← hs, map_mul]
      module

theorem mem_closureTensorSpan_of_tensorToGenericFibre_mem_span [IsDomain R]
    [IsPrincipalIdealRing R] [IsNoetherianRing R] [IsFractionRing R F]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} {x : G ⊗[R] G}
    (hx : tensorToGenericFibre R F x ∈ Submodule.span F
      (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))) :
    x ∈ closureTensorSpan B := by
  obtain ⟨r, z, hr, hz, e⟩ := exists_smul_eq_tensorToGenericFibre_of_mem_span hx
  have h1 : tensorToGenericFibre R F (r • x) = tensorToGenericFibre R F z := by
    rw [tensorToGenericFibre_smul]; exact e
  have h2 : r • x = z := tensorToGenericFibre_injective h1
  exact mem_closureTensorSpan_of_smul_mem B hr (h2 ▸ hz)

end ModuleLevel

section Bialgebra

variable [Bialgebra R G]

variable (R F) in

def IsComulStable (B : Subalgebra F (F ⊗[R] G)) : Prop :=
  ∀ g ∈ flatClosure B, tensorToGenericFibre R F (Coalgebra.comul (R := R) g) ∈
    Submodule.span F (Set.image2 (· ⊗ₜ[F] ·) (B : Set (F ⊗[R] G)) (B : Set (F ⊗[R] G)))

theorem comul_mem_closureTensorSpan [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) {g : G} (hg : g ∈ flatClosure B) :
    Coalgebra.comul (R := R) g ∈ closureTensorSpan B :=
  mem_closureTensorSpan_of_tensorToGenericFibre_mem_span (hB g hg)

theorem comul_mem_range_tensorInclusion [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) {g : G} (hg : g ∈ flatClosure B) :
    Coalgebra.comul (R := R) g ∈ LinearMap.range (tensorInclusion B) := by
  rw [range_tensorInclusion]
  exact comul_mem_closureTensorSpan hB hg

noncomputable def closureComul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    flatClosure B →ₗ[R] (flatClosure B) ⊗[R] (flatClosure B) :=
  (LinearEquiv.ofInjective (tensorInclusion B)
      (tensorInclusion_injective B)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (tensorInclusion B))
      ((Coalgebra.comul (R := R)).comp (flatClosure B).val.toLinearMap)
      (fun h => comul_mem_range_tensorInclusion hB h.2)

@[simp]
theorem tensorInclusion_closureComul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    tensorInclusion B (closureComul hB h) = Coalgebra.comul (R := R) (h : G) := by
  show tensorInclusion B ((LinearEquiv.ofInjective (tensorInclusion B)
      (tensorInclusion_injective B)).symm _) = _
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

noncomputable def closureCounit (B : Subalgebra F (F ⊗[R] G)) : flatClosure B →ₗ[R] R :=
  (Coalgebra.counit (R := R) (A := G)).comp (flatClosure B).val.toLinearMap

@[simp]
theorem closureCounit_apply (B : Subalgebra F (F ⊗[R] G)) (h : flatClosure B) :
    closureCounit B h = Coalgebra.counit (R := R) (h : G) := rfl

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra R G]

variable (R F) in

def IsAntipodeStable (B : Subalgebra F (F ⊗[R] G)) : Prop :=
  ∀ g ∈ flatClosure B, HopfAlgebra.antipode R g ∈ flatClosure B

def closureAntipode {B : Subalgebra F (F ⊗[R] G)} (hB : IsAntipodeStable R F B) :
    flatClosure B →ₗ[R] flatClosure B where
  toFun h := ⟨HopfAlgebra.antipode R (h : G), hB _ h.2⟩
  map_add' x y := by
    ext
    simp [map_add]
  map_smul' r x := by
    ext
    simp [map_smul]

@[simp]
theorem coe_closureAntipode_apply {B : Subalgebra F (F ⊗[R] G)} (hB : IsAntipodeStable R F B)
    (h : flatClosure B) :
    (closureAntipode hB h : G) = HopfAlgebra.antipode R (h : G) := rfl

end HopfAlgebra

section GenericFibre

variable [Algebra R G]

noncomputable def genericFibreAlgHom (B : Subalgebra F (F ⊗[R] G)) :
    F ⊗[R] (flatClosure B) →ₐ[F] F ⊗[R] G :=
  AlgHom.liftEquiv R F (flatClosure B) (F ⊗[R] G)
    ((Algebra.TensorProduct.includeRight (R := R) (A := F) (B := G)).comp (flatClosure B).val)

@[simp]
lemma genericFibreAlgHom_tmul (B : Subalgebra F (F ⊗[R] G)) (f : F) (h : flatClosure B) :
    genericFibreAlgHom B (f ⊗ₜ[R] h) = f ⊗ₜ[R] (h : G) := by
  simp [genericFibreAlgHom, TensorProduct.smul_tmul', smul_eq_mul]

theorem genericFibreAlgHom_injective [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (genericFibreAlgHom B) := by
  haveI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have hcoe : ⇑(genericFibreAlgHom B)
      = ⇑(LinearMap.lTensor F (flatClosure B).val.toLinearMap) := by
    funext x
    induction x with
    | zero => rw [map_zero, map_zero]
    | tmul f h => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hcoe]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

theorem range_genericFibreAlgHom [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : (genericFibreAlgHom B).range = B := by
  have hmem : ∀ x : F ⊗[R] (flatClosure B), genericFibreAlgHom B x ∈ B := by
    intro x
    induction x with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul f h =>
        rw [genericFibreAlgHom_tmul]
        have h1 : (1 : F) ⊗ₜ[R] (h : G) ∈ B := h.2
        have h2 : f ⊗ₜ[R] (h : G) = f • ((1 : F) ⊗ₜ[R] (h : G)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h2]
        exact B.smul_mem h1 f
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy
  apply le_antisymm
  · rintro y hy
    obtain ⟨x, rfl⟩ := ((genericFibreAlgHom B).mem_range).mp hy
    exact hmem x
  · have hspan : Subalgebra.toSubmodule B
        ≤ Subalgebra.toSubmodule (genericFibreAlgHom B).range := by
      rw [← span_image_flatClosure (R := R) (F := F) B, Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
      refine ((genericFibreAlgHom B).mem_range).mpr
        ⟨1 ⊗ₜ[R] (⟨g, hg⟩ : flatClosure B), ?_⟩
      rw [genericFibreAlgHom_tmul]
    intro x hx
    exact hspan hx

noncomputable def genericFibreAlgEquiv [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) : (F ⊗[R] (flatClosure B)) ≃ₐ[F] B :=
  (AlgEquiv.ofInjective (genericFibreAlgHom B) (genericFibreAlgHom_injective B)).trans
    (Subalgebra.equivOfEq _ _ (range_genericFibreAlgHom B))

end GenericFibre

end FlatClosureHopf


