-- Prove2me | Definitions.Def_AlgebraicCurve_NodalPic0
-- name    : AlgebraicCurve_NodalPic0
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/dfb4fdd7-1c5a-554c-8d59-768b3c9b5768
-- title:
--   Degree-zero Picard group of a nodal curve, via divisor data
-- statement:
--   Fix a field $K$, finitely many field extensions $\bar F_0,\dots,\bar F_{n-1}$ of $K$, and combinatorial gluing data consisting of maps $\mathrm{src},\mathrm{tgt}\colon \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ together with, for each edge $e$, places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$ (a place of $\bar F/K$ being, as in the divisor-class-group module, a valuation subring containing $K$, proper and a principal ideal ring, hence a discrete valuation ring, with $\mathrm{ord}$ its normalised valuation and $\deg$ the $K$-dimension of its residue field). `NodalData` is the group of tuples $E = (E_i)_i$ of divisors, $E_i \in \mathrm{Place}(K,\bar F_i) \to_{\mathrm{f}} \mathbb{Z}$. Two subgroups are defined. `NodalData.admissible` consists of the $E$ with $\deg E_i = 0$ for every $i$ and $E_{\mathrm{src}(e)}(x_s(e)) = E_{\mathrm{tgt}(e)}(x_t(e)) = 0$ for every edge $e$. `NodalData.IsNodalPrincipal` asserts the existence of nonzero $g_i \in \bar F_i$ and units $a_e \in K^{\times}$ such that $E_i(v) = v.\mathrm{ord}(g_i)$ for every place $v$ of $\bar F_i$, and such that at each edge both $g_{\mathrm{src}(e)}$ at $x_s(e)$ and $g_{\mathrm{tgt}(e)}$ at $x_t(e)$ satisfy `Place.HasValue` with the same value $a_e$ — that is, each lies in the corresponding valuation subring and has residue equal to the image of $a_e$ in the residue field. These data form the subgroup `nodalPrincipal`; membership criteria for both subgroups are recorded. `NodalPic0` is the quotient of `admissible` by the intersection of `nodalPrincipal` with it, with quotient map `NodalPic0.mk`, its surjectivity, and the criterion that `mk` of an admissible $E$ vanishes exactly when $E$ is nodal-principal.
--
--   **Relation to Mathlib.** Mathlib has no Picard group of a nodal or glued curve presented by tuples of divisors; these are the project's own notions, built on Mathlib's `ValuationSubring`, `Finsupp` and `QuotientAddGroup`, and on the project's `Place`, `Divisor` and `Place.HasValue`.
--
--   **Where it is used.** This is the multi-component analogue of [`AlgebraicCurve.GluedPic0`](../def/AlgebraicCurve_GluedPic0.html#L201), which treats a single field with a finite set of pairs of glued places: it models the degree-zero (multidegree-zero) part of the Picard group of a curve obtained by gluing the smooth curves with function fields $\bar F_i$ along the nodes prescribed by the edges, line bundles being trivialised at the nodes. It serves as the target for reduction of divisor classes on a semistable curve in the study of the relevant Jacobians and their torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_NodalPic0.lean

import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Nodal

variable (K : Type*) [Field K] {n m : ℕ} (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)] [∀ i, Algebra K (Fbar i)]

abbrev NodalData : Type _ := ∀ i : Fin n, Divisor K (Fbar i)

namespace NodalData

variable {K Fbar}
variable (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e)))

def admissible : AddSubgroup (NodalData K Fbar) where
  carrier := {E | (∀ i, E i ∈ Divisor.degZero (K := K) (F := Fbar i)) ∧
    ∀ e, E (src e) (xs e) = 0 ∧ E (tgt e) (xt e) = 0}
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => ⟨rfl, rfl⟩⟩
  add_mem' := by
    rintro E E' ⟨hE, hEn⟩ ⟨hE', hE'n⟩
    refine ⟨fun i => add_mem (hE i) (hE' i), fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.add_apply, Finsupp.add_apply, (hEn e).1, (hE'n e).1, add_zero]
    · rw [Pi.add_apply, Finsupp.add_apply, (hEn e).2, (hE'n e).2, add_zero]
  neg_mem' := by
    rintro E ⟨hE, hEn⟩
    refine ⟨fun i => neg_mem (hE i), fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.neg_apply, Finsupp.neg_apply, (hEn e).1, neg_zero]
    · rw [Pi.neg_apply, Finsupp.neg_apply, (hEn e).2, neg_zero]

theorem mem_admissible {E : NodalData K Fbar} :
    E ∈ admissible src tgt xs xt ↔ (∀ i, E i ∈ Divisor.degZero (K := K) (F := Fbar i)) ∧
      ∀ e, E (src e) (xs e) = 0 ∧ E (tgt e) (xt e) = 0 :=
  Iff.rfl

def IsNodalPrincipal (E : NodalData K Fbar) : Prop :=
  ∃ (g : ∀ i, Fbar i) (a : Fin m → Kˣ), (∀ i, g i ≠ 0) ∧
    (∀ i, ∀ v : Place K (Fbar i), E i v = v.ord (g i)) ∧
    ∀ e, (xs e).HasValue (g (src e)) (a e) ∧ (xt e).HasValue (g (tgt e)) (a e)

def nodalPrincipal : AddSubgroup (NodalData K Fbar) where
  carrier := {E | IsNodalPrincipal src tgt xs xt E}
  zero_mem' := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => one_ne_zero, fun i v => by simp, fun e => ⟨?_, ?_⟩⟩
    · simpa using (xs e).hasValue_one
    · simpa using (xt e).hasValue_one
  add_mem' := by
    rintro E E' ⟨g, a, hg, hE, hv⟩ ⟨g', a', hg', hE', hv'⟩
    refine ⟨fun i => g i * g' i, a * a', fun i => mul_ne_zero (hg i) (hg' i), fun i v => ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.add_apply, Finsupp.add_apply, hE i v, hE' i v, v.ord_mul (hg i) (hg' i)]
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv e).1.mul (hv' e).1
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv e).2.mul (hv' e).2
  neg_mem' := by
    rintro E ⟨g, a, hg, hE, hv⟩
    refine ⟨fun i => (g i)⁻¹, a⁻¹, fun i => inv_ne_zero (hg i), fun i v => ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.neg_apply, Finsupp.neg_apply, hE i v, v.ord_inv]
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv e).1.inv (a e).ne_zero
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv e).2.inv (a e).ne_zero

theorem mem_nodalPrincipal {E : NodalData K Fbar} :
    E ∈ nodalPrincipal src tgt xs xt ↔ IsNodalPrincipal src tgt xs xt E :=
  Iff.rfl

end NodalData

abbrev NodalPic0 (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e))) : Type _ :=
  ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt) ⧸
    (NodalData.nodalPrincipal (K := K) (Fbar := Fbar) src tgt xs xt).addSubgroupOf (NodalData.admissible src tgt xs xt)

namespace NodalPic0

variable {K Fbar}
variable (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e)))

def mk : ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt) →+ NodalPic0 K Fbar src tgt xs xt :=
  QuotientAddGroup.mk' _

theorem mk_surjective : Function.Surjective (mk (K := K) (Fbar := Fbar) src tgt xs xt) :=
  QuotientAddGroup.mk'_surjective _

theorem mk_eq_zero_iff (E : ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt)) :
    mk src tgt xs xt E = 0 ↔ NodalData.IsNodalPrincipal src tgt xs xt (E : NodalData K Fbar) := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  rfl

end NodalPic0

end Nodal

end AlgebraicCurve


