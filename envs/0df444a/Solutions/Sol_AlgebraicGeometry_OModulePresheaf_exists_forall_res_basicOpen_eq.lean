-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d0c2115d-2a0d-5365-ae24-b2a700ff846d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

namespace GlueAux

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π}

abbrev ρ (U : V.affineOpens) (f : Γ(V, U.1)) : Γ(V, U.1) →+* Γ(V, V.basicOpen f) :=
  (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom

lemma res_smul' (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (y : F.obj U.1) :
    F.res (V.basicOpen_le f) (a • y) = ρ U f a • F.res (V.basicOpen_le f) y :=
  F.res_smul _ a y

lemma basicOpen_mul_le_left (U : V.affineOpens) (f g : Γ(V, U.1)) : V.basicOpen (f * g) ≤ V.basicOpen f :=
  (V.basicOpen_mul f g).trans_le inf_le_left

lemma basicOpen_mul_le_right (U : V.affineOpens) (f g : Γ(V, U.1)) : V.basicOpen (f * g) ≤ V.basicOpen g :=
  (V.basicOpen_mul f g).trans_le inf_le_right

lemma exists_common_lift (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type v} [Fintype ι]
    (h : ι → Γ(V, U.1)) (x : ∀ j, F.obj (V.basicOpen (h j))) :
    ∃ (N : ℕ) (y : ι → F.obj U.1), ∀ j, F.res (V.basicOpen_le (h j)) (y j) = ρ U (h j) (h j ^ N) • x j := by
  classical
  have H : ∀ j, ∃ (n : ℕ) (y : F.obj U.1), F.res (V.basicOpen_le (h j)) y = ρ U (h j) (h j ^ n) • x j :=
    fun j => (hF U (h j)).1 (x j)
  choose n y hy using H
  refine ⟨Finset.univ.sup n, fun j => h j ^ (Finset.univ.sup n - n j) • y j, fun j => ?_⟩
  rw [res_smul', hy, ← mul_smul, ← map_mul, pow_sub_mul_pow _ (Finset.le_sup (Finset.mem_univ j))]

lemma exists_common_kill (hF : F.IsQuasicoherent) (U : V.affineOpens) {κ : Type v} [Fintype κ]
    (g : κ → Γ(V, U.1)) (z : κ → F.obj U.1) (hz : ∀ p, F.res (V.basicOpen_le (g p)) (z p) = 0) :
    ∃ K : ℕ, ∀ p, (g p ^ K) • z p = 0 := by
  classical
  have H : ∀ p, ∃ n : ℕ, (g p ^ n) • z p = 0 := fun p => (hF U (g p)).2 (z p) (hz p)
  choose n hn using H
  refine ⟨Finset.univ.sup n, fun p => ?_⟩
  rw [← pow_sub_mul_pow _ (Finset.le_sup (Finset.mem_univ p)), mul_smul, hn, smul_zero]

theorem exists_forall_res_basicOpen_eq (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type v} [Fintype ι]
    (h : ι → Γ(V, U.1)) (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j))
    (x : ∀ j, F.obj (V.basicOpen (h j)))
    (hx : ∀ j k, F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_left) (x j) =
      F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_right) (x k)) :
    ∃ y : F.obj U.1, ∀ j, F.res (V.basicOpen_le (h j)) y = x j := by
  classical

  obtain ⟨N, y, hy⟩ := exists_common_lift hF U h x

  let z : ι × ι → F.obj U.1 := fun p => (h p.2 ^ N) • y p.1 - (h p.1 ^ N) • y p.2
  have hz : ∀ p : ι × ι, F.res (V.basicOpen_le (h p.1 * h p.2)) (z p) = 0 := by
    rintro ⟨j, k⟩
    change F.res (V.basicOpen_le (h j * h k)) ((h k ^ N) • y j - (h j ^ N) • y k) = 0
    have ej : V.basicOpen (h j * h k) ≤ V.basicOpen (h j) := basicOpen_mul_le_left U (h j) (h k)
    have ek : V.basicOpen (h j * h k) ≤ V.basicOpen (h k) := basicOpen_mul_le_right U (h j) (h k)
    have rj : F.res (V.basicOpen_le (h j * h k)) (y j) = F.res ej (ρ U (h j) (h j ^ N) • x j) := by
      rw [← hy j, F.res_res]
    have rk : F.res (V.basicOpen_le (h j * h k)) (y k) = F.res ek (ρ U (h k) (h k ^ N) • x k) := by
      rw [← hy k, F.res_res]
    rw [map_sub, res_smul', res_smul', rj, rk, F.res_smul, F.res_smul, ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, ← V.presheaf.map_comp, ← V.presheaf.map_comp, smul_smul, smul_smul, sub_eq_zero]
    have e1 : (homOfLE (V.basicOpen_le (h j))).op ≫ (homOfLE ej).op = (homOfLE (V.basicOpen_le (h j * h k))).op :=
      Subsingleton.elim _ _
    have e2 : (homOfLE (V.basicOpen_le (h k))).op ≫ (homOfLE ek).op = (homOfLE (V.basicOpen_le (h j * h k))).op :=
      Subsingleton.elim _ _
    rw [e1, e2, ← map_mul, ← map_mul, mul_comm (h k ^ N) (h j ^ N)]
    exact congrArg _ (hx j k)
  obtain ⟨K, hK⟩ := exists_common_kill hF U (fun p : ι × ι => h p.1 * h p.2) z hz

  let y' : ι → F.obj U.1 := fun j => (h j ^ K) • y j
  have hcross : ∀ j k, (h k ^ (N + K)) • y' j = (h j ^ (N + K)) • y' k := by
    intro j k
    have := hK (j, k)
    change ((h j * h k) ^ K) • ((h k ^ N) • y j - (h j ^ N) • y k) = 0 at this
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at this
    change (h k ^ (N + K)) • ((h j ^ K) • y j) = (h j ^ (N + K)) • ((h k ^ K) • y k)
    rw [smul_smul, smul_smul]
    convert this using 2 <;> ring
  have hy' : ∀ j, F.res (V.basicOpen_le (h j)) (y' j) = ρ U (h j) (h j ^ (N + K)) • x j := by
    intro j
    change F.res (V.basicOpen_le (h j)) ((h j ^ K) • y j) = _
    rw [res_smul', hy, smul_smul, ← map_mul, ← pow_add, add_comm]

  have hspan : Ideal.span (Set.range h) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    refine hcov.trans (iSup_le fun j => ?_)
    exact le_iSup (fun f : Set.range h => V.basicOpen f.1) ⟨h j, j, rfl⟩
  have hspan' : Ideal.span (Set.range fun j => h j ^ (N + K)) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hspan (N + K)
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan'.symm ▸ Submodule.mem_top : (1 : Γ(V, U.1)) ∈ _)

  refine ⟨∑ j, a j • y' j, fun k => ?_⟩
  have hk : (h k ^ (N + K)) • ∑ j, a j • y' j = y' k := by
    rw [Finset.smul_sum]
    calc ∑ j, (h k ^ (N + K)) • (a j • y' j) = ∑ j, a j • ((h j ^ (N + K)) • y' k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_comm, hcross j k]
      _ = (∑ j, a j * h j ^ (N + K)) • y' k := by rw [Finset.sum_smul]; simp_rw [mul_smul]
      _ = y' k := by rw [ha, one_smul]

  have hunit : IsUnit (ρ U (h k) (h k ^ (N + K))) := by
    rw [map_pow]
    exact (RingedSpace.isUnit_res_basicOpen (X := V.toLocallyRingedSpace.toRingedSpace) (h k)).pow (N + K)
  refine (hunit.smul_left_cancel).mp ?_
  rw [← res_smul', hk, hy']

end GlueAux

end

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π}
    (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : ∀ j, F.obj (V.basicOpen (h j)))
    (hx : ∀ j k, F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_left) (x j) =
      F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_right) (x k)) :
    ∃ y : F.obj U.1, ∀ j, F.res (V.basicOpen_le (h j)) y = x j :=
  GlueAux.exists_forall_res_basicOpen_eq hF U h hcov x hx

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq (solution)
