-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_ConjAction
-- name    : GroundTheory_TateCohomology_ConjAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:45.831272+00:00
-- url     : https://prove2.me/theorems/b2879f4b-4045-454f-bc5c-52647954980e
-- title:
--   Conj Action
-- statement:
--   Definitions and structural lemmas for Conj Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ConjAction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
def conjHom (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, ‹S.Normal›.conj_mem' (s : G) s.2 g⟩
  map_one' := by ext; simp
  map_mul' s t := by ext; simp only [Subgroup.coe_mul]; group
@[simp]
lemma coe_conjHom_apply (g : G) (s : S) : (conjHom S g s : G) = g⁻¹ * s * g := rfl
noncomputable def conjMor (g : G) : res (conjHom S g) (res S.subtype A) ⟶ res S.subtype A :=
  ofHom ⟨A.ρ g, fun s => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, coe_conjHom_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩
@[simp]
lemma conjMor_hom_apply (g : G) (a : A) : (conjMor A S g).hom a = A.ρ g a := rfl
noncomputable abbrev conjAct (n : ℕ) (g : G) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology (res S.subtype A) n :=
  map (conjHom S g) (conjMor A S g) n
lemma conjAct_one (n : ℕ) : conjAct A S n 1 = 𝟙 _ := by
  rw [← map_id]
  exact map_congr (by ext; simp) (by ext x; show A.ρ 1 x = x; rw [map_one]; rfl) n
lemma conjAct_mul (n : ℕ) (g h : G) :
    conjAct A S n (g * h) = conjAct A S n h ≫ conjAct A S n g := by
  rw [← map_comp]
  exact map_congr (by ext; simp; group)
    (by ext x; show A.ρ (g * h) x = A.ρ g (A.ρ h x); rw [map_mul]; rfl) n
noncomputable def conjRep (n : ℕ) :
    Representation k G (groupCohomology (res S.subtype A) n) where
  toFun g := (conjAct A S n g).hom
  map_one' := by rw [conjAct_one]; rfl
  map_mul' g h := by rw [conjAct_mul]; rfl
lemma conjRep_apply (n : ℕ) (g : G) (x : groupCohomology (res S.subtype A) n) :
    conjRep A S n g x = (conjAct A S n g).hom x := rfl
lemma conjRep_H1π (g : G) (f : cocycles₁ (res S.subtype A)) :
    conjRep A S 1 g (H1π _ f) = H1π _ (mapCocycles₁ (conjHom S g) (conjMor A S g) f) := by
  rw [conjRep_apply, H1π_comp_map_apply]
omit [S.Normal] in
variable {A S} in

lemma cocycle_conj (f : cocycles₁ (res S.subtype A)) (t u : S) :
    A.ρ t (f (t⁻¹ * u * t)) = f u + A.ρ u (f t) - f t := by
  have h := (mem_cocycles₁_iff (A := res S.subtype A) f).1 f.2
  have hinv : A.ρ t (f t⁻¹) = -f t := cocycles₁_map_inv (A := res S.subtype A) f t
  have e1 : A.ρ t ((res S.subtype A).ρ (t⁻¹ * u) (f t)) = A.ρ u (f t) := by
    rw [res_obj_ρ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have e2 : A.ρ t ((res S.subtype A).ρ t⁻¹ (f u)) = f u := by
    rw [res_obj_ρ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subgroup.coe_inv]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [h, h, map_add, map_add, hinv, e1, e2]
  abel
instance : Representation.IsTrivial ((conjRep A S 1).comp S.subtype) where
  out t := by
    ext x
    induction x using H1_induction_on with | h f =>
    change conjRep A S 1 t (H1π _ f) = H1π _ f
    rw [conjRep_H1π, H1π_eq_iff]
    refine ⟨f t, funext fun u => ?_⟩
    have hc : conjHom S (t : G) u = t⁻¹ * u * t := Subtype.ext rfl
    change A.ρ u (f t) - f t = A.ρ t (f (conjHom S (t : G) u)) - f u
    rw [hc, cocycle_conj]
    abel
noncomputable abbrev h1QuotAction :
    Representation k (G ⧸ S) (groupCohomology (res S.subtype A) 1) :=
  (conjRep A S 1).ofQuotient S
lemma mem_h1QuotAction_invariants (x : groupCohomology (res S.subtype A) 1) :
    x ∈ (h1QuotAction A S).invariants ↔ ∀ g : G, conjRep A S 1 g x = x :=
  ⟨fun h g => h (g : G ⧸ S), fun h q => QuotientGroup.induction_on q fun g => h g⟩
lemma cocycle_conj_sub (φ : cocycles₁ A) (g : G) (s : G) :
    A.ρ g (φ (g⁻¹ * s * g)) - φ s = A.ρ s (φ g) - φ g := by
  have h := (mem_cocycles₁_iff φ).1 φ.2
  have hinv : A.ρ g (φ g⁻¹) = -φ g := cocycles₁_map_inv φ g
  rw [h, h, map_add, map_add, hinv, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply,
    ← map_mul, mul_inv_cancel_left, mul_inv_cancel, map_one, Module.End.one_apply]
  abel
lemma restriction_mem_invariants (x : groupCohomology A 1) :
    (map S.subtype (𝟙 (res S.subtype A)) 1).hom x ∈ (h1QuotAction A S).invariants := by
  rw [mem_h1QuotAction_invariants]
  intro g
  induction x using H1_induction_on with | h φ =>
  rw [H1π_comp_map_apply, conjRep_H1π, H1π_eq_iff]
  refine ⟨φ g, funext fun s => ?_⟩
  change A.ρ s (φ g) - φ g = A.ρ g (φ (g⁻¹ * s * g)) - φ s
  rw [cocycle_conj_sub]
noncomputable def restrictionInv :
    groupCohomology A 1 →ₗ[k] (h1QuotAction A S).invariants :=
  (map S.subtype (𝟙 (res S.subtype A)) 1).hom.codRestrict _ (restriction_mem_invariants A S)
end GroundTheory.GroupCoh


