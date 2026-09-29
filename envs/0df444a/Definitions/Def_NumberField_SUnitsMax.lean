-- Prove2me | Definitions.Def_NumberField_SUnitsMax
-- name    : NumberField_SUnitsMax
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/87122040-db68-502f-98c2-d11c63b4737a
-- title:
--   S-units of the maximal extension unramified outside S
-- statement:
--   Throughout, $S$ is a finite set of rational primes and all algebraic extensions are taken inside $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. The predicate `IsSUnitMax S x`, for a unit $x \in \overline{\mathbb{Q}}^{\times}$, is the conjunction of two conditions: first, $x$ lies in some intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ satisfying `F.IsUnramifiedOutside S`, that is, $F$ is finite-dimensional over $\mathbb{Q}$ and, for every prime $q \notin S$ and every valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ (transported into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$) fixes $F$ pointwise; and second, for every prime $q \notin S$ and every such valuation subring $A$ lying over $q$, both $x$ and $x^{-1}$ belong to $A$. Thus $x$ is an algebraic number generating an extension unramified outside $S$ which is a unit at every place away from $S$. These elements form a subgroup `sUnitsMax S` of $\overline{\mathbb{Q}}^{\times}$ (closure under products uses the stability of `IsUnramifiedOutside` under joins of fields).
--
--   For an intermediate field $L$, `sUnitsMaxStable S L` is the intersection, over all $\gamma$ in the fixing subgroup of $L$ (i.e. $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$ acting on $\overline{\mathbb{Q}}^{\times}$), of the preimages of `sUnitsMax S` under $x \mapsto \gamma \cdot x$; membership is characterised by $\gamma \cdot x \in$ `sUnitsMax S` for all such $\gamma$. It is contained in `sUnitsMax S` (take $\gamma = 1$) and is stable under the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$. Its image `sUnitsMaxSubmodule S L` in the additive group `Additive`$\,\overline{\mathbb{Q}}^{\times}$ is a $\mathbb{Z}$-submodule, and `sUnitsMaxRep S L` is the resulting object of `Rep ℤ ↥L.fixingSubgroup`, namely the subrepresentation of the multiplicative action of $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$ on `Additive`$\,\overline{\mathbb{Q}}^{\times}$ cut out by that submodule. The accessor `sUnitsMaxRep.val` returns the underlying unit, and `sUnitsMaxRep.val_ρ` records that the representation acts by the Galois action on units.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here (`ValuationSubring` and its inertia subgroup, `IntermediateField.fixingSubgroup`, `MulDistribMulAction` and `Rep.ofMulDistribMulAction`, `Subgroup.toAddSubgroup`), but not the predicates `IsUnramifiedOutside` or `IsSUnitMax`: Mathlib's $S$-unit notions are attached to a fixed number field or Dedekind domain, whereas these are conditions on elements of $\overline{\mathbb{Q}}^{\times}$ formulated through valuation subrings of $\overline{\mathbb{Q}}$, and are the project's own.
--
--   **Where it is used.** The module provides the coefficient module for the Kummer sequence over the maximal extension of $\mathbb{Q}$ unramified outside $S$, in the form of a Galois representation over $\mathbb{Z}$, for use in the cohomological level arithmetic (global and local $H^1$/$H^2$ with level-constant cochains, Selmer conditions) of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SUnitsMax.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

variable (S : Finset Nat.Primes)

def IsSUnitMax (x : (AlgebraicClosure ℚ)ˣ) : Prop :=
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ (x : AlgebraicClosure ℚ) ∈ F) ∧
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      (x : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A

def sUnitsMax : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | IsSUnitMax S x}
  one_mem' := ⟨⟨⊥, IntermediateField.isUnramifiedOutside_bot S, by simp⟩, fun q _ A _ => ⟨by simp, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨⟨F, hF, hxF⟩, hx⟩ ⟨⟨F', hF', hyF'⟩, hy⟩
    refine ⟨⟨F ⊔ F', hF.sup hF', ?_⟩, fun q hq A hA => ⟨?_, ?_⟩⟩
    · rw [Units.val_mul]; exact mul_mem ((le_sup_left : F ≤ F ⊔ F') hxF) ((le_sup_right : F' ≤ F ⊔ F') hyF')
    · rw [Units.val_mul]; exact A.toSubring.mul_mem (hx q hq A hA).1 (hy q hq A hA).1
    · rw [mul_inv_rev, Units.val_mul]; exact A.toSubring.mul_mem (hy q hq A hA).2 (hx q hq A hA).2
  inv_mem' := by
    rintro x ⟨⟨F, hF, hxF⟩, hx⟩
    refine ⟨⟨F, hF, ?_⟩, fun q hq A hA => ⟨(hx q hq A hA).2, by simpa using (hx q hq A hA).1⟩⟩
    rw [Units.val_inv_eq_inv_val]; exact inv_mem hxF

theorem mem_sUnitsMax_iff (x : (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMax S ↔ IsSUnitMax S x := Iff.rfl

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

def sUnitsMaxStable : Subgroup (AlgebraicClosure ℚ)ˣ :=
  ⨅ γ : ↥L.fixingSubgroup, (sUnitsMax S).comap (MulDistribMulAction.toMonoidHom (AlgebraicClosure ℚ)ˣ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))

theorem mem_sUnitsMaxStable_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ sUnitsMaxStable S L ↔ ∀ γ : ↥L.fixingSubgroup, (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x ∈ sUnitsMax S := by
  simp only [sUnitsMaxStable, Subgroup.mem_iInf, Subgroup.mem_comap, MulDistribMulAction.toMonoidHom_apply]

theorem sUnitsMaxStable_le : sUnitsMaxStable S L ≤ sUnitsMax S := fun x hx => by
  have h := (mem_sUnitsMaxStable_iff S L x).1 hx 1
  rwa [show ((1 : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) = 1 from rfl, one_smul] at h

theorem smul_mem_sUnitsMaxStable (δ : ↥L.fixingSubgroup) {x : (AlgebraicClosure ℚ)ˣ} (hx : x ∈ sUnitsMaxStable S L) :
    (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • x ∈ sUnitsMaxStable S L := by
  rw [mem_sUnitsMaxStable_iff] at hx ⊢
  intro γ
  rw [← mul_smul]
  exact hx (γ * δ)

def sUnitsMaxSubmodule : Submodule ℤ (Additive (AlgebraicClosure ℚ)ˣ) := (Subgroup.toAddSubgroup (sUnitsMaxStable S L)).toIntSubmodule

theorem mem_sUnitsMaxSubmodule (x : Additive (AlgebraicClosure ℚ)ˣ) : x ∈ sUnitsMaxSubmodule S L ↔ Additive.toMul x ∈ sUnitsMaxStable S L := Iff.rfl

abbrev sUnitsMaxRep : Rep ℤ ↥L.fixingSubgroup :=
  Rep.of ((Rep.ofMulDistribMulAction ↥L.fixingSubgroup (AlgebraicClosure ℚ)ˣ).ρ.subrepresentation (sUnitsMaxSubmodule S L)
    fun γ _ hx => smul_mem_sUnitsMaxStable S L γ hx)

abbrev sUnitsMaxRep.val (x : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ := Additive.toMul x.1

theorem sUnitsMaxRep.val_ρ (γ : ↥L.fixingSubgroup) (x : sUnitsMaxRep S L) :
    sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ γ x) = (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • sUnitsMaxRep.val S L x := rfl

end NumberField.LevelArith

end


