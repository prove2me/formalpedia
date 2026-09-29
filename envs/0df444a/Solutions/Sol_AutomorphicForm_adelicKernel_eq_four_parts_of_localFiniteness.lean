-- Prove2me | solution 1 for AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4b2345d9-d02e-59c1-bf03-ad7168ec61fd

import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness

set_option autoImplicit false

open Matrix Polynomial AutomorphicForm

open scoped NumberField

noncomputable section

namespace M4aP3B
namespace Rows

variable {K : Type*} [Field K]

theorem charpoly_smul_one (c : K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)).charpoly = (X - C c) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp only [Matrix.trace_smul, Matrix.trace_one, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, smul_eq_mul, mul_one, Nat.cast_ofNat, map_mul, map_pow, map_ofNat]
  ring

theorem isRoot_iff_of_sq {p : K[X]} {a : K} (h : p = (X - C a) ^ 2) (x : K) :
    p.IsRoot x ↔ x = a := by
  subst h
  simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C, sq_eq_zero_iff, sub_eq_zero]

theorem isRoot_iff_of_pair {p : K[X]} {a b : K} (h : p = (X - C a) * (X - C b)) (x : K) :
    p.IsRoot x ↔ x = a ∨ x = b := by
  subst h
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]

theorem classification_charpoly (M : Matrix (Fin 2) (Fin 2) K) :
    IsCentralType M ∨ IsEllipticType M ∨ IsHyperbolicType M ∨ IsUnipotentType M := by
  by_cases hroot : ∀ a : K, ¬M.charpoly.IsRoot a
  · exact Or.inr (Or.inl hroot)
  · push Not at hroot
    obtain ⟨a, ha⟩ := hroot
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
    have hmonic : M.charpoly.Monic := Matrix.charpoly_monic M
    have hdeg : M.charpoly.natDegree = 2 := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hXa : (X - C a).Monic := monic_X_sub_C a
    have hqmonic : q.Monic := by
      have hm := hmonic
      rw [hq] at hm
      exact hXa.of_mul_monic_left hm
    have hqdeg : q.natDegree = 1 := by
      have h2 : ((X - C a) * q).natDegree = 2 := by rw [← hq]; exact hdeg
      rw [hXa.natDegree_mul hqmonic, natDegree_X_sub_C] at h2
      omega
    obtain ⟨b, hqb⟩ : ∃ b : K, q = X - C b :=
      ⟨-(q.coeff 0), by rw [map_neg, sub_neg_eq_add]; exact hqmonic.eq_X_add_C hqdeg⟩
    have hfact : M.charpoly = (X - C a) * (X - C b) := by rw [hq, hqb]
    by_cases hab : a = b
    · rw [← hab] at hfact
      have hsq : M.charpoly = (X - C a) ^ 2 := by rw [hfact, sq]
      by_cases hc : IsCentralType M
      · exact Or.inl hc
      · exact Or.inr (Or.inr (Or.inr ⟨hc, a, hsq⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a, b, hab, hfact⟩))

theorem not_isUnipotentType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsUnipotentType M := fun hu => hu.1 h

theorem not_isHyperbolicType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsHyperbolicType M := by
  rintro ⟨a, b, hab, hfact⟩
  obtain ⟨c, hc⟩ := h
  have hsq : M.charpoly = (X - C c) ^ 2 := by rw [hc]; exact charpoly_smul_one c
  have ha : a = c := (isRoot_iff_of_sq hsq a).mp ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))
  have hb : b = c := (isRoot_iff_of_sq hsq b).mp ((isRoot_iff_of_pair hfact b).mpr (Or.inr rfl))
  exact hab (ha.trans hb.symm)

theorem not_isEllipticType_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsCentralType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨c, hc⟩ := h
  have hsq : M.charpoly = (X - C c) ^ 2 := by rw [hc]; exact charpoly_smul_one c
  exact he c ((isRoot_iff_of_sq hsq c).mpr rfl)

theorem not_isHyperbolicType_of_isUnipotentType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsUnipotentType M) : ¬IsHyperbolicType M := by
  rintro ⟨a, b, hab, hfact⟩
  obtain ⟨-, c, hsq⟩ := h
  have ha : a = c := (isRoot_iff_of_sq hsq a).mp ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))
  have hb : b = c := (isRoot_iff_of_sq hsq b).mp ((isRoot_iff_of_pair hfact b).mpr (Or.inr rfl))
  exact hab (ha.trans hb.symm)

theorem not_isEllipticType_of_isUnipotentType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsUnipotentType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨-, a, hsq⟩ := h
  exact he a ((isRoot_iff_of_sq hsq a).mpr rfl)

theorem not_isEllipticType_of_isHyperbolicType {M : Matrix (Fin 2) (Fin 2) K}
    (h : IsHyperbolicType M) : ¬IsEllipticType M := by
  intro he
  obtain ⟨a, b, -, hfact⟩ := h
  exact he a ((isRoot_iff_of_pair hfact a).mpr (Or.inl rfl))

theorem union_cells_eq_univ :
    centralCell K ∪ (ellipticCell K ∪ (hyperbolicCell K ∪ unipotentCell K)) = Set.univ := by
  ext γ
  simp only [Set.mem_union, Set.mem_univ, iff_true, centralCell, ellipticCell,
    hyperbolicCell, unipotentCell, Set.mem_setOf_eq]
  exact classification_charpoly _

theorem disjoint_central_rest :
    Disjoint (centralCell K) (ellipticCell K ∪ (hyperbolicCell K ∪ unipotentCell K)) := by
  rw [Set.disjoint_left]
  rintro γ hc (he | hh | hu)
  · exact not_isEllipticType_of_isCentralType hc he
  · exact not_isHyperbolicType_of_isCentralType hc hh
  · exact not_isUnipotentType_of_isCentralType hc hu

theorem disjoint_elliptic_rest :
    Disjoint (ellipticCell K) (hyperbolicCell K ∪ unipotentCell K) := by
  rw [Set.disjoint_left]
  rintro γ he (hh | hu)
  · exact not_isEllipticType_of_isHyperbolicType hh he
  · exact not_isEllipticType_of_isUnipotentType hu he

theorem disjoint_hyperbolic_unipotent :
    Disjoint (hyperbolicCell K) (unipotentCell K) := by
  rw [Set.disjoint_left]
  exact fun γ hh hu => not_isHyperbolicType_of_isUnipotentType hu hh

section Split

variable (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]

theorem adelicKernel_eq_four_parts_impl
    (h : AdelicKernelLocalFiniteness F)
    {f : AdelicGL2 (𝓞 F) F → M} {C : Set (AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AdelicGL2 (𝓞 F) F) :
    adelicKernel F f x y
      = adelicKernelCentralPart F f x y + adelicKernelEllipticPart F f x y
        + adelicKernelHyperbolicPart F f x y + adelicKernelUnipotentPart F f x y := by
  have hfin : (Function.support fun γ : GL (Fin 2) F =>
      f (x⁻¹ * globalPoints (𝓞 F) F γ * y)).Finite := by
    apply Set.Finite.subset (h C hC x y)
    intro γ hγ
    exact hsupp hγ
  unfold adelicKernel adelicKernelCentralPart adelicKernelEllipticPart
    adelicKernelHyperbolicPart adelicKernelUnipotentPart
  rw [← finsum_mem_univ, ← union_cells_eq_univ (K := F),
    finsum_mem_union' (disjoint_central_rest (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _),
    finsum_mem_union' (disjoint_elliptic_rest (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _),
    finsum_mem_union' (disjoint_hyperbolic_unipotent (K := F)) (hfin.inter_of_right _)
      (hfin.inter_of_right _)]
  abel

end Split

end M4aP3B.Rows

set_option autoImplicit false
open Matrix
open scoped NumberField

theorem solution
    (F : Type) [Field F] [NumberField F] {M : Type*} [AddCommMonoid M]
    (h : AutomorphicForm.AdelicKernelLocalFiniteness F)
    {f : AutomorphicForm.AdelicGL2 (𝓞 F) F → M}
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)}
    (hC : IsCompact C) (hsupp : Function.support f ⊆ C)
    (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    AutomorphicForm.adelicKernel F f x y
      = AutomorphicForm.adelicKernelCentralPart F f x y
        + AutomorphicForm.adelicKernelEllipticPart F f x y
        + AutomorphicForm.adelicKernelHyperbolicPart F f x y
        + AutomorphicForm.adelicKernelUnipotentPart F f x y := by
  exact M4aP3B.Rows.adelicKernel_eq_four_parts_impl F h hC hsupp x y

end
end S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness
end P2MW
export P2MW.S_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness (solution)
