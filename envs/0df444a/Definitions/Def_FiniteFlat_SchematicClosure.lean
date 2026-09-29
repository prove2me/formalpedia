-- Prove2me | Definitions.Def_FiniteFlat_SchematicClosure
-- name    : FiniteFlat_SchematicClosure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/87a74843-b68d-5a50-a9fb-04421352e6a0
-- title:
--   Flat closure of a subalgebra of the generic fibre
-- statement:
--   Fix a commutative ring $R$, an $R$-algebra $F$ which is a field, and a commutative $R$-algebra $G$. For an $F$-subalgebra $B$ of the base change $F \otimes_R G$, [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19) is the $R$-subalgebra of $G$ whose underlying set is $\{g \in G \mid 1 \otimes g \in B\}$; the subalgebra axioms are verified directly, the image of $r \in R$ being $\mathrm{algebraMap}\,r \otimes 1$. The membership criterion [`mem_flatClosure_iff`](../def/FiniteFlat_SchematicClosure.html#L46) records this description, [`flatClosure_mono`](../def/FiniteFlat_SchematicClosure.html#L49) its monotonicity in $B$, and [`le_flatClosure_iff`](../def/FiniteFlat_SchematicClosure.html#L52) the corresponding test for an $R$-subalgebra of $G$ to be contained in it; [`one_tmul_smul`](../def/FiniteFlat_SchematicClosure.html#L15) is the elementary identity $1 \otimes (r \cdot g) = \mathrm{algebraMap}\,r \cdot (1 \otimes g)$.
--
--   The module then establishes the module-theoretic properties of this construction. With $R$ Noetherian and $G$ module-finite over $R$, [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19) is module-finite over $R$; it is torsion-free whenever $G$ is; and if in addition $R$ is a principal ideal domain it is free, hence flat. Under the assumption that $F$ is a fraction field of the domain $R$, [`exists_nonzero_smul_eq_one_tmul`](../def/FiniteFlat_SchematicClosure.html#L77) shows every $x \in F \otimes_R G$ admits $r \neq 0$ in $R$ and $g \in G$ with $\mathrm{algebraMap}\,r \cdot x = 1 \otimes g$; [`exists_nonzero_smul_mem_flatClosure`](../def/FiniteFlat_SchematicClosure.html#L96) adds that $g$ lies in [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19) when $x \in B$, and [`span_image_flatClosure`](../def/FiniteFlat_SchematicClosure.html#L105) deduces that the $F$-span of $\{1 \otimes g : g \in \mathrm{flatClosure}\,B\}$ is exactly $B$, so the construction recovers $B$ on the generic fibre. Finally the quotient $G / \mathrm{flatClosure}\,B$ is shown torsion-free, module-finite, and (over a principal ideal domain) free, whence [`exists_isCompl_flatClosure`](../def/FiniteFlat_SchematicClosure.html#L153): the flat closure admits an $R$-submodule complement in $G$.
--
--   **Relation to Mathlib.** Mathlib has no schematic-closure construction; [`flatClosure`](../def/FiniteFlat_SchematicClosure.html#L19) is the project's own definition, built from Mathlib's `Subalgebra`, tensor products and the `Module.Finite`/`Module.Free`/`Module.Flat` hierarchy.
--
--   **Where it is used.** This is the affine form of the scheme-theoretic closure of a closed subscheme of the generic fibre, the commutative-algebra input to prolongation statements for finite flat group schemes over a discrete valuation ring. It feeds the treatment of flat (finite flat) local conditions at $p$ used in the deformation-theoretic part of the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FiniteFlat_SchematicClosure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

section FlatClosure

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G] [Algebra R G]

instance : IsScalarTower R F (F ⊗[R] G) := IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma one_tmul_smul (r : R) (g : G) :
    (1 : F) ⊗ₜ[R] (r • g) = (algebraMap R F r) • ((1 : F) ⊗ₜ[R] g) := by
  rw [TensorProduct.tmul_smul, algebraMap_smul]

def flatClosure (B : Subalgebra F (F ⊗[R] G)) : Subalgebra R G where
  carrier := {g : G | (1 : F) ⊗ₜ[R] g ∈ B}
  mul_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) * ((1 : F) ⊗ₜ[R] b) ∈ B := mul_mem ha hb
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
    exact h
  one_mem' := by
    show (1 : F) ⊗ₜ[R] (1 : G) ∈ B
    rw [← Algebra.TensorProduct.one_def]
    exact one_mem B
  add_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) + ((1 : F) ⊗ₜ[R] b) ∈ B := add_mem ha hb
    rw [← TensorProduct.tmul_add] at h
    exact h
  zero_mem' := by
    show (1 : F) ⊗ₜ[R] (0 : G) ∈ B
    rw [TensorProduct.tmul_zero]
    exact zero_mem B
  algebraMap_mem' r := by
    show (1 : F) ⊗ₜ[R] (algebraMap R G r) ∈ B
    have h1 : (1 : F) ⊗ₜ[R] (algebraMap R G r) = (algebraMap R F r) ⊗ₜ[R] (1 : G) := by
      rw [Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        ← Algebra.algebraMap_eq_smul_one]
    rw [h1, ← Algebra.TensorProduct.algebraMap_apply]
    exact B.algebraMap_mem _

@[simp]
lemma mem_flatClosure_iff {B : Subalgebra F (F ⊗[R] G)} {g : G} :
    g ∈ flatClosure B ↔ (1 : F) ⊗ₜ[R] g ∈ B := Iff.rfl

lemma flatClosure_mono {B B' : Subalgebra F (F ⊗[R] G)} (h : B ≤ B') :
    flatClosure B ≤ flatClosure B' := fun _ hg => h hg

lemma le_flatClosure_iff {B : Subalgebra F (F ⊗[R] G)} {S : Subalgebra R G} :
    S ≤ flatClosure B ↔ ∀ g ∈ S, (1 : F) ⊗ₜ[R] g ∈ B := Iff.rfl

theorem flatClosure_finite [IsNoetherianRing R] [Module.Finite R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Finite R (flatClosure B) := by
  haveI : IsNoetherian R G := isNoetherian_of_isNoetherianRing_of_finite R G
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (Subalgebra.toSubmodule (flatClosure B)))

theorem flatClosure_isTorsionFree [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.IsTorsionFree R (flatClosure B) :=
  Function.Injective.moduleIsTorsionFree _ Subtype.coe_injective (fun _ _ => rfl)

theorem flatClosure_free [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Free R (flatClosure B) := by
  haveI := flatClosure_finite (R := R) (F := F) (G := G) B
  haveI := flatClosure_isTorsionFree (R := R) (F := F) (G := G) B
  exact Module.free_of_finite_type_torsion_free'

theorem flatClosure_flat [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Flat R (flatClosure B) := by
  haveI := flatClosure_free (R := R) (F := F) (G := G) B
  exact Module.Flat.of_free

theorem exists_nonzero_smul_eq_one_tmul [IsDomain R] [IsFractionRing R F] (x : F ⊗[R] G) :
    ∃ (r : R) (g : G), r ≠ 0 ∧ (algebraMap R F r) • x = (1 : F) ⊗ₜ[R] g := by
  induction x with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul f g =>
      obtain ⟨p, hs⟩ := IsLocalization.surj (nonZeroDivisors R) f
      refine ⟨p.2, p.1 • g, nonZeroDivisors.coe_ne_zero p.2, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, hs, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      obtain ⟨r₁, g₁, h₁, e₁⟩ := hx
      obtain ⟨r₂, g₂, h₂, e₂⟩ := hy
      refine ⟨r₁ * r₂, r₂ • g₁ + r₁ • g₂, mul_ne_zero h₁ h₂, ?_⟩
      have hx' : (algebraMap R F (r₁ * r₂)) • x = (1 : F) ⊗ₜ[R] (r₂ • g₁) := by
        rw [map_mul, mul_comm, mul_smul, e₁, ← one_tmul_smul]
      have hy' : (algebraMap R F (r₁ * r₂)) • y = (1 : F) ⊗ₜ[R] (r₁ • g₂) := by
        rw [map_mul, mul_smul, e₂, ← one_tmul_smul]
      rw [smul_add, hx', hy', ← TensorProduct.tmul_add]

theorem exists_nonzero_smul_mem_flatClosure [IsDomain R] [IsFractionRing R F]
    {B : Subalgebra F (F ⊗[R] G)} {x : F ⊗[R] G} (hx : x ∈ B) :
    ∃ (r : R) (g : G), r ≠ 0 ∧ g ∈ flatClosure B ∧
      (algebraMap R F r) • x = (1 : F) ⊗ₜ[R] g := by
  obtain ⟨r, g, hr, e⟩ := exists_nonzero_smul_eq_one_tmul (R := R) (F := F) x
  refine ⟨r, g, hr, ?_, e⟩
  rw [mem_flatClosure_iff, ← e, Algebra.smul_def]
  exact mul_mem (B.algebraMap_mem _) hx

theorem span_image_flatClosure [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) :
    Submodule.span F ((fun g : G => (1 : F) ⊗ₜ[R] g) '' (flatClosure B : Set G))
      = Subalgebra.toSubmodule B := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hg
  · intro x hx
    obtain ⟨r, g, hr, hg, e⟩ := exists_nonzero_smul_mem_flatClosure (R := R) (F := F) hx
    have hru : (algebraMap R F r) ≠ 0 := fun h =>
      hr (IsFractionRing.injective R F (by rw [h, map_zero]))
    have hxe : x = (algebraMap R F r)⁻¹ • ((1 : F) ⊗ₜ[R] g) := by
      rw [← e, smul_smul, inv_mul_cancel₀ hru, one_smul]
    rw [hxe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)

theorem quotient_flatClosure_isTorsionFree [IsDomain R] [IsFractionRing R F]
    (B : Subalgebra F (F ⊗[R] G)) :
    Module.IsTorsionFree R (G ⧸ Subalgebra.toSubmodule (flatClosure B)) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r m hm
  by_cases hr : r = 0
  · exact Or.inl hr
  refine Or.inr ?_
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Subalgebra.mem_toSubmodule, mem_flatClosure_iff, one_tmul_smul] at hm
  rw [Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule, mem_flatClosure_iff]
  have hru : (algebraMap R F r) ≠ 0 := fun h =>
    hr (IsFractionRing.injective R F (by rw [h, map_zero]))
  have h2 : (algebraMap R F r)⁻¹ • ((algebraMap R F r) • ((1 : F) ⊗ₜ[R] g)) ∈ B := by
    rw [Algebra.smul_def]
    exact mul_mem (B.algebraMap_mem _) hm
  rwa [smul_smul, inv_mul_cancel₀ hru, one_smul] at h2

theorem quotient_flatClosure_finite [Module.Finite R G] (B : Subalgebra F (F ⊗[R] G)) :
    Module.Finite R (G ⧸ Subalgebra.toSubmodule (flatClosure B)) :=
  Module.Finite.of_surjective (Subalgebra.toSubmodule (flatClosure B)).mkQ
    (Submodule.Quotient.mk_surjective _)

theorem quotient_flatClosure_free [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F]
    [Module.Finite R G] (B : Subalgebra F (F ⊗[R] G)) :
    Module.Free R (G ⧸ Subalgebra.toSubmodule (flatClosure B)) := by
  haveI := quotient_flatClosure_isTorsionFree (R := R) (F := F) (G := G) B
  haveI := quotient_flatClosure_finite (R := R) (F := F) (G := G) B
  exact Module.free_of_finite_type_torsion_free'

theorem exists_isCompl_flatClosure [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F]
    [Module.Finite R G] (B : Subalgebra F (F ⊗[R] G)) :
    ∃ C : Submodule R G, IsCompl (Subalgebra.toSubmodule (flatClosure B)) C := by
  haveI := quotient_flatClosure_free (R := R) (F := F) (G := G) B
  set N : Submodule R G := Subalgebra.toSubmodule (flatClosure B) with hN

  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id)
    (Submodule.Quotient.mk_surjective N)
  have hsec : ∀ y : G ⧸ N, N.mkQ (s y) = y := fun y => congrFun (congrArg DFunLike.coe hs) y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  ·
    rw [Submodule.disjoint_def]
    rintro x hxN ⟨y, rfl⟩
    have h0 : N.mkQ (s y) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxN
    rw [hsec y] at h0
    rw [h0, map_zero]
  ·
    rw [codisjoint_iff, eq_top_iff]
    intro g _
    have hmem : g - s (N.mkQ g) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hsec, sub_self]
    have : g = (g - s (N.mkQ g)) + s (N.mkQ g) := by ring
    rw [this]
    exact Submodule.add_mem_sup hmem ⟨N.mkQ g, rfl⟩

end FlatClosure


