-- Prove2me | solution 1 for Algebra.exists_lift_basis_of_surjective_of_monogenic_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0b8fa09c-1dd8-5fa3-bbac-5f1543c45085

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial

universe u v w x

noncomputable section

namespace MonogenicLiftSol

open Classical in

theorem main
    (R' : Type u) [CommRing R'] [IsLocalRing R'] (R : Type v) [CommRing R] [IsLocalRing R]
    (π : R' →+* R) (hπ : Function.Surjective π)
    (C : Type w) [CommRing C] [Algebra R C] (ι : Type x) [Fintype ι]
    (e : Module.Basis ι R C) (i₀ : ι) (he : e i₀ = 1)
    (y : C) (hy : ∀ z : C, ∃ q : R[X],
      z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C')
      (σ : C' →+* C),
      e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
  haveI : Module.Free R C := Module.Free.of_basis e
  haveI : Module.Finite R C := Module.Finite.of_basis e
  haveI : Nonempty ι := ⟨i₀⟩

  have hspan_all : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro z _
    obtain ⟨q, hq⟩ := hy z
    have h1 : aeval y q ∈ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
      rw [aeval_eq_sum_range]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have h2 : z = aeval y q + (z - aeval y q) := by ring
    rw [h2]
    exact Submodule.add_mem_sup h1 hq

  set χ : R[X] := (Algebra.lmul R C y).charpoly with hχdef
  have hχm : χ.Monic := LinearMap.charpoly_monic _
  have hχdeg : χ.natDegree = Fintype.card ι := by
    rw [hχdef, LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis e]
  have hχy : aeval y χ = 0 := by
    have h0 : Algebra.lmul R C (aeval y χ) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]
      exact LinearMap.aeval_self_charpoly _
    exact Algebra.lmul_injective (R := R) (by rw [h0, map_zero])
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hχ1 : χ ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hχdeg, natDegree_one] at this
    omega

  obtain ⟨χ', hχ'map, hχ'deg, hχ'm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hπ χ) hχm
  set d : ℕ := χ'.natDegree with hddef
  have hd : d = Fintype.card ι := by rw [hχ'deg, hχdeg]
  have hd0 : 0 < d := by rw [hd]; exact hcard

  set v : Fin d → C := fun j => y ^ (j : ℕ) with hvdef
  have hv_span : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range v) := by
    refine hspan_all.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk : y ^ k = aeval y (X ^ k %ₘ χ) := by
      rw [aeval_modByMonic_eq_self_of_root hχy, map_pow, aeval_X]
    have hlt : (X ^ k %ₘ χ).natDegree < d := by
      rw [hd, ← hχdeg]
      exact natDegree_modByMonic_lt _ hχm hχ1
    change y ^ k ∈ Submodule.span R (Set.range v)
    rw [hk, aeval_eq_sum_range' hlt, ← Fin.sum_univ_eq_sum_range]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let ιd : ι ≃ Fin d := (Fintype.equivFinOfCardEq hd.symm)
  have hv_li : LinearIndependent R v := by
    let L : (Fin d →₀ R) →ₗ[R] C := Finsupp.linearCombination R v
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact top_le_iff.mp hv_span
    let inj : (Fin d →₀ R) →ₗ[R] C :=
      e.repr.symm.toLinearMap ∘ₗ (Finsupp.domLCongr ιd.symm).toLinearMap
    have hinj : Function.Injective inj :=
      e.repr.symm.injective.comp (Finsupp.domLCongr ιd.symm).injective
    exact OrzechProperty.injective_of_surjective_of_injective inj L hinj hL
  let vB : Module.Basis (Fin d) R C := Module.Basis.mk hv_li hv_span
  have hvB : ∀ j, vB j = y ^ (j : ℕ) := fun j => by rw [Module.Basis.mk_apply]

  haveI : Module.Free R' (AdjoinRoot χ') := hχ'm.free_adjoinRoot
  haveI : Module.Finite R' (AdjoinRoot χ') := hχ'm.finite_adjoinRoot
  let pb : PowerBasis R' (AdjoinRoot χ') := AdjoinRoot.powerBasis' hχ'm
  have hpbdim : pb.dim = d := rfl
  have hpb : ∀ j : Fin d, pb.basis j = AdjoinRoot.root χ' ^ (j : ℕ) := fun j => by
    rw [PowerBasis.coe_basis]; rfl
  have hev : χ'.eval₂ ((algebraMap R C).comp π) y = 0 := by
    rw [← Polynomial.eval₂_map, hχ'map]
    exact hχy
  let σ : AdjoinRoot χ' →+* C := AdjoinRoot.lift ((algebraMap R C).comp π) y hev
  have hσ_of : ∀ r, σ (algebraMap R' (AdjoinRoot χ') r) = algebraMap R C (π r) := fun r => by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of hev
  have hσ_root : ∀ k : ℕ, σ (AdjoinRoot.root χ' ^ k) = y ^ k := fun k => by
    rw [map_pow, AdjoinRoot.lift_root]
  have hσ_smul : ∀ (r : R') (c : AdjoinRoot χ'), σ (r • c) = π r • σ c := fun r c => by
    rw [Algebra.smul_def, map_mul, hσ_of, ← Algebra.smul_def]
  have hσ_sum : ∀ a : Fin d → R', σ (∑ j, a j • pb.basis j) = ∑ j, π (a j) • v j := fun a => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hσ_smul, hpb, hσ_root]

  have hkerσ : ∀ c : AdjoinRoot χ', σ c = 0 →
      c ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) := by
    intro c hc
    have hc' : c = ∑ j : Fin d, pb.basis.repr c j • pb.basis j := (pb.basis.sum_repr c).symm
    rw [hc', hσ_sum] at hc
    have hzero : ∀ j, π (pb.basis.repr c j) = 0 := fun j =>
      linearIndependent_iff'.mp hv_li Finset.univ (fun j => π (pb.basis.repr c j)) hc j
        (Finset.mem_univ j)
    rw [hc']
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hzero j)) Submodule.mem_top

  let s : R → R' := Function.surjInv hπ
  have hs : ∀ r, π (s r) = r := Function.surjInv_eq hπ
  let j₀ : Fin d := ⟨0, hd0⟩
  have hvB0 : vB j₀ = 1 := by rw [hvB]; simp [j₀]
  have hP0 : ∀ j : Fin d, vB.repr (e i₀) j = if j = j₀ then 1 else 0 := fun j => by
    rw [he, ← hvB0, vB.repr_self, Finsupp.single_apply]
    by_cases h : j = j₀
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  let P' : ι → Fin d → R' := fun i j =>
    if i = i₀ then (if j = j₀ then 1 else 0) else s (vB.repr (e i) j)
  have hP' : ∀ i j, π (P' i j) = vB.repr (e i) j := by
    intro i j
    by_cases hi : i = i₀
    · subst hi
      simp only [P', if_true, hP0]
      split_ifs <;> simp
    · simp only [P', if_neg hi, hs]
  let ev : ι → AdjoinRoot χ' := fun i => ∑ j, P' i j • pb.basis j
  have hσev : ∀ i, σ (ev i) = e i := fun i => by
    change σ (∑ j, P' i j • pb.basis j) = e i
    rw [hσ_sum]
    conv_rhs => rw [← vB.sum_repr (e i)]
    exact Finset.sum_congr rfl fun j _ => by rw [hP', hvB]
  have hev0 : ev i₀ = 1 := by
    change ∑ j, P' i₀ j • pb.basis j = 1
    rw [Finset.sum_eq_single j₀]
    · simp only [P', if_true, one_smul, hpb]
      simp [j₀]
    · intro j _ hj
      simp only [P', if_true, if_neg hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ j₀) h

  have hkerπ : RingHom.ker π ≤ (⊥ : Ideal R').jacobson :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hev_span : (⊤ : Submodule R' (AdjoinRoot χ')) ≤ Submodule.span R' (Set.range ev) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hkerπ
    intro c _
    let c'' : AdjoinRoot χ' := ∑ i, s (e.repr (σ c) i) • ev i
    have hc'' : c'' ∈ Submodule.span R' (Set.range ev) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hσc'' : σ c'' = σ c := by
      change σ (∑ i, s (e.repr (σ c) i) • ev i) = σ c
      rw [map_sum]
      conv_rhs => rw [← e.sum_repr (σ c)]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ_smul, hs, hσev]
    have hdiff : c - c'' ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) :=
      hkerσ _ (by rw [map_sub, hσc'', sub_self])
    have : c = c'' + (c - c'') := by ring
    rw [this]
    exact Submodule.add_mem_sup hc'' hdiff

  have hev_li : LinearIndependent R' ev := by
    let L : (ι →₀ R') →ₗ[R'] AdjoinRoot χ' := Finsupp.linearCombination R' ev
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact top_le_iff.mp hev_span
    let inj : (ι →₀ R') →ₗ[R'] AdjoinRoot χ' :=
      pb.basis.repr.symm.toLinearMap ∘ₗ (Finsupp.domLCongr ιd).toLinearMap
    have hinj : Function.Injective inj :=
      pb.basis.repr.symm.injective.comp (Finsupp.domLCongr ιd).injective
    exact OrzechProperty.injective_of_surjective_of_injective inj L hinj hL
  let e' : Module.Basis ι R' (AdjoinRoot χ') := Module.Basis.mk hev_li hev_span
  refine ⟨AdjoinRoot χ', inferInstance, inferInstance, e', σ, ?_, hσ_of, fun i => ?_⟩
  · rw [Module.Basis.mk_apply]; exact hev0
  · rw [Module.Basis.mk_apply]; exact hσev i

end MonogenicLiftSol

end

theorem solution
    (R' : Type u) [CommRing R'] [IsLocalRing R'] (R : Type v) [CommRing R] [IsLocalRing R]
    (π : R' →+* R) (hπ : Function.Surjective π)
    (C : Type w) [CommRing C] [Algebra R C] (ι : Type x) [Fintype ι]
    (e : Module.Basis ι R C) (i₀ : ι) (he : e i₀ = 1)
    (hmono : ∃ y : C, ∀ z : C, ∃ q : R[X],
      z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C')
      (σ : C' →+* C),
      e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
  obtain ⟨y, hy⟩ := hmono
  exact MonogenicLiftSol.main R' R π hπ C ι e i₀ he y hy

end S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre
end P2MW
export P2MW.S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre (solution)
