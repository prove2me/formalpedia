-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:53:15.179012+00:00
-- url     : https://prove2.me/theorems/0fcd25e2-42cb-5771-8e4e-942aff60c7e8
-- title:
--   Projection
-- statement:
--   Definitions and structural lemmas for Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_eq_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_canon_sub
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_sub
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_mem_cartanSub
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isDiagExp_or
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_upL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_mem_nPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nPlusU_le_spanUpper
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_isDiagExp_of_hasUpper
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_lower_of_diag
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_upper_of_diag
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_repr_canon
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open Classical in

noncomputable def hcProjLin : U n →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  pbw.constr ℂ fun m => if IsDiagExp m then monomial (diagExp m) 1 else 0
theorem hcProjLin_canon_of_isDiagExp {m : Fin n × Fin n →₀ ℕ} (h : IsDiagExp m) :
    hcProjLin (canon m) = monomial (diagExp m) 1 := by
  rw [hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_pos h]
theorem hcProjLin_canon_of_not {m : Fin n × Fin n →₀ ℕ} (h : ¬ IsDiagExp m) :
    hcProjLin (canon m) = 0 := by
  rw [hcProjLin, ← pbw_apply, Module.Basis.constr_basis, if_neg h]
theorem canon_of_isDiagExp {m : Fin n × Fin n →₀ ℕ} (h : IsDiagExp m) :
    canon m = hcEmb (monomial (diagExp m) 1) := by
  have hz : ∀ a, ¬ IsDiag a → m a = 0 := fun a ha => by
    by_contra h'; exact ha (h a h')
  rw [canon_eq_triangular, blockW_eq_nil (l := lowL n) (fun a ha => hz a
      (not_lower_of_diag.mt (not_not.2 (mem_lowL.1 ha)) |> fun h' => fun hd => h' hd)),
    blockW_eq_nil (l := upL n) (fun a ha => hz a fun hd => not_upper_of_diag hd (mem_upL.1 ha))]
  simp
noncomputable def diagEmbExp (μ : Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.mapDomain (fun i => (i, i)) μ
theorem diagEmbExp_injective : Function.Injective (fun i : Fin n => (i, i)) :=
  fun _ _ h => congrArg Prod.fst h
theorem isDiagExp_diagEmbExp (μ : Fin n →₀ ℕ) : IsDiagExp (diagEmbExp μ) := by
  intro a ha
  by_contra hd
  apply ha
  rw [diagEmbExp, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨i, rfl⟩
  exact hd rfl
theorem diagExp_diagEmbExp (μ : Fin n →₀ ℕ) : diagExp (diagEmbExp μ) = μ := by
  ext i
  rw [diagExp_apply, diagEmbExp, Finsupp.mapDomain_apply diagEmbExp_injective]
theorem hcEmb_monomial_one (μ : Fin n →₀ ℕ) : hcEmb (monomial μ 1) = canon (diagEmbExp μ) := by
  rw [canon_of_isDiagExp (isDiagExp_diagEmbExp μ), diagExp_diagEmbExp]
theorem hcProjLin_hcEmb (p : MvPolynomial (Fin n) ℂ) : hcProjLin (hcEmb p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [show monomial μ c = c • monomial μ (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, map_smul, hcEmb_monomial_one, hcProjLin_canon_of_isDiagExp (isDiagExp_diagEmbExp μ),
      diagExp_diagEmbExp]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
theorem hcProjLin_eq_zero_of_mem_nPlusU {x : U n} (hx : x ∈ nPlusU n) : hcProjLin x = 0 := by
  have hx' : x ∈ Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, HasUpper m ∧ canon m = x} :=
    nPlusU_le_spanUpper hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hm)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]
theorem sum_mul_rootAt (a : Fin n × Fin n) :
    ∑ k : Fin n, (k : ℤ) * rootAt a k = (a.1 : ℤ) - a.2 := by
  simp only [rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
theorem sum_mul_wt (m : Fin n × Fin n →₀ ℕ) :
    ∑ k : Fin n, (k : ℤ) * wt m k = m.sum fun a c => (c : ℤ) * ((a.1 : ℤ) - a.2) := by
  simp only [wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_mul_rootAt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
theorem hasUpper_of_wt_eq_zero {m : Fin n × Fin n →₀ ℕ} (hw : ∀ k, wt m k = 0) (hl : HasLower m) :
    HasUpper m := by
  by_contra hu
  have h0 : ∑ k : Fin n, (k : ℤ) * wt m k = 0 := by simp [hw]
  rw [sum_mul_wt, Finsupp.sum] at h0
  obtain ⟨a, ha, hma⟩ := hl
  have hnonneg : ∀ b ∈ m.support, 0 ≤ (m b : ℤ) * ((b.1 : ℤ) - b.2) := by
    intro b hb
    refine mul_nonneg (by positivity) ?_
    by_contra hneg
    apply hu
    refine ⟨b, ?_, Finsupp.mem_support_iff.1 hb⟩
    simp only [IsUpper]
    have : (b.1 : ℤ) < b.2 := by linarith
    exact_mod_cast this
  have hpos : 0 < (m a : ℤ) * ((a.1 : ℤ) - a.2) := by
    refine mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hma) ?_
    simp only [IsLower] at ha
    have : (a.2 : ℤ) < a.1 := by exact_mod_cast ha
    linarith
  have := Finset.sum_pos' hnonneg ⟨a, Finsupp.mem_support_iff.2 hma, hpos⟩
  linarith
theorem sub_hcEmb_mem_nPlusU {z : U n} (hz : ∀ k, e (k, k) * z = z * e (k, k)) :
    z - hcEmb (hcProjLin z) ∈ nPlusU n := by
  set s := (pbw.repr z).support
  set c := fun m => pbw.repr z m
  have hzs : z = ∑ m ∈ s, c m • canon m := (sum_repr_canon z).symm
  have hwt : ∀ m ∈ s, ∀ k, wt m k = 0 := by
    intro m hm k
    have h0 : ∑ m ∈ s, (c m * (wt m k : ℂ)) • canon m = 0 := by
      have := sub_eq_zero.2 (hz k)
      rw [hzs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at this
      rw [← this]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul]
    have := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
    have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
    exact_mod_cast (mul_eq_zero.1 this).resolve_left hc
  rw [hzs, map_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [map_smul, map_smul, ← smul_sub]
  refine Submodule.smul_mem _ _ ?_
  rcases isDiagExp_or m with h | h | h
  · rw [hcProjLin_canon_of_isDiagExp h, ← canon_of_isDiagExp h, sub_self]
    exact Submodule.zero_mem _
  · rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper h), map_zero, sub_zero]
    exact canon_mem_nPlusU h
  · have hu := hasUpper_of_wt_eq_zero (hwt m hm) h
    rw [hcProjLin_canon_of_not (not_isDiagExp_of_hasUpper hu), map_zero, sub_zero]
    exact canon_mem_nPlusU hu
theorem mul_e_diag_mem_nPlusU {x : U n} (hx : x ∈ nPlusU n) (k : Fin n) :
    x * e (k, k) ∈ nPlusU n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, a, ha, rfl⟩ := hx
    have h := e_diag_mul_sub k a
    have : u * e a * e (k, k) = (u * e (k, k)) * e a - (rootAt a k : ℂ) • (u * e a) := by
      rw [mul_assoc, mul_assoc, ← mul_smul_comm, ← mul_sub, ← h]; noncomm_ring
    rw [this]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, a, ha, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, a, ha, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
theorem mul_mem_nPlusU_of_mem_cartanSub {x y : U n} (hx : x ∈ nPlusU n) (hy : y ∈ cartanSub n) :
    x * y ∈ nPlusU n := by
  let S : Subalgebra ℂ (U n) :=
    { carrier := {y | ∀ x ∈ nPlusU n, x * y ∈ nPlusU n}
      mul_mem' := fun {a b} ha hb x hx => by rw [← mul_assoc]; exact hb _ (ha x hx)
      add_mem' := fun {a b} ha hb x hx => by rw [mul_add]; exact Submodule.add_mem _ (ha x hx) (hb x hx)
      algebraMap_mem' := fun r x hx => by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]; exact Submodule.smul_mem _ r hx }
  have : cartanSub n ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩ x hx
    exact mul_e_diag_mem_nPlusU hx k
  exact this hy x hx
abbrev centralizerT (n : ℕ) : Subalgebra ℂ (U n) := Subalgebra.centralizer ℂ (cartanSet n)
theorem commute_e_diag_of_mem {z : U n} (hz : z ∈ centralizerT n) (k : Fin n) :
    e (k, k) * z = z * e (k, k) :=
  (Subalgebra.mem_centralizer_iff ℂ).1 hz _ ⟨k, rfl⟩
theorem hcProjLin_one : hcProjLin (1 : U n) = 1 := by
  rw [← canon_zero, hcProjLin_canon_of_isDiagExp (fun a h => absurd rfl h)]
  have : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [this, ← C_1, monomial_zero']
theorem hcProjLin_mul {z z' : U n} (hz : z ∈ centralizerT n) (hz' : z' ∈ centralizerT n) :
    hcProjLin (z * z') = hcProjLin z * hcProjLin z' := by
  set p := hcProjLin z
  set p' := hcProjLin z'
  have hx := sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz)
  have hx' := sub_hcEmb_mem_nPlusU (commute_e_diag_of_mem hz')
  set x := z - hcEmb p
  set x' := z' - hcEmb p'
  have hzz : z * z' = hcEmb (p * p') + (hcEmb p * x' + x * hcEmb p' + x * x') := by
    rw [map_mul]; simp only [x, x']; noncomm_ring
  rw [hzz, map_add, hcProjLin_hcEmb]
  have : hcEmb p * x' + x * hcEmb p' + x * x' ∈ nPlusU n :=
    Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_nPlusU _ hx')
      (mul_mem_nPlusU_of_mem_cartanSub hx (hcEmb_mem_cartanSub p'))) (mul_mem_nPlusU _ hx')
  rw [hcProjLin_eq_zero_of_mem_nPlusU this, add_zero]
noncomputable def hcProj0 : centralizerT n →ₐ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun z := hcProjLin (z : U n)
  map_one' := hcProjLin_one
  map_mul' z z' := hcProjLin_mul z.2 z'.2
  map_zero' := by simp
  map_add' z z' := by simp
  commutes' r := by
    show hcProjLin (algebraMap ℂ (U n) r) = algebraMap ℂ _ r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hcProjLin_one, Algebra.algebraMap_eq_smul_one]
noncomputable def rhoVec (n : ℕ) : Fin n → ℂ := fun i => ((n : ℂ) - 1) / 2 - (i : ℂ)
noncomputable def translate (c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval fun i => X i + C (c i)
noncomputable def harishChandraHom : Subalgebra.center ℂ (U n) →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  (translate (-rhoVec n)).comp
    (hcProj0.comp (Subalgebra.inclusion (Subalgebra.center_le_centralizer ℂ (cartanSet n))))
end GroundTheory.Automorphic.HarishChandra


