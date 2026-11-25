-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:09.697808+00:00
-- url     : https://prove2.me/theorems/7e3c7504-9d60-4b65-a9f5-efedcdd8c94a
-- title:
--   Choose Le Pow Div Factorial
-- statement:
--   Definitions and structural lemmas for Choose Le Pow Div Factorial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ChooseLePowDivFactorial.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsProjFrame_isRatProjFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secTrace_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_fg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sec_mul_sec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
theorem prod_div_pow_degree (x : κ → Ω) (j : κ) (m : κ →₀ ℕ) :
    (m.prod fun i k => x i ^ k) / x j ^ (Finsupp.degree m) = m.prod fun i k => (x i / x j) ^ k := by
  simp only [Finsupp.prod, Finsupp.degree, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  rfl
theorem div_pow_mem_fnField (x : κ → Ω) (j : κ) {n : ℕ} {s : Ω} (hs : s ∈ sec ℤ x n) :
    s / x j ^ n ∈ fnField x := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.sec at hs
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hs
  have hhom := (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.sum_div]
  refine sum_mem fun m hm => ?_
  have hdeg : Finsupp.degree m = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hhom (MvPolynomial.mem_support_iff.1 hm)
  rw [mul_div_assoc]
  refine mul_mem ?_ ?_
  · rw [eq_intCast]
    exact intCast_mem _ _
  · have hprod := prod_div_pow_degree x j m
    rw [hdeg] at hprod
    rw [show (∏ i ∈ m.support, x i ^ m i) = m.prod fun i k => x i ^ k from rfl, hprod]
    exact prod_mem fun i _ => pow_mem (IntermediateField.subset_adjoin ℚ {t : Ω | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩) _
theorem alpha_mem (x : κ → Ω) (e : Fin (D + 1) → κ) {k n δ : ℕ} (ε : Fin δ → Ω)
    (hε : ∀ l, ε l ∈ sec ℤ x k) (P : Fin δ → Ω) (hP : ∀ l, P l ∈ sec ℤ (x ∘ e) n) :
    ∑ l, P l * ε l ∈ sec ℤ x (n + k) := by
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← sec_mul_sec]
  refine Submodule.mul_mem_mul ?_ (hε l)
  have hl := hP l
  unfold ReciprocityTheory.ChartRestriction.G.Geo.sec at hl ⊢
  obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hl
  refine Submodule.mem_map.2 ⟨MvPolynomial.rename e p, ?_, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule n _).2
      (((MvPolynomial.mem_homogeneousSubmodule n p).1 hp).rename_isHomogeneous)
  · rw [← hpe]
    simp [MvPolynomial.aeval_rename]
theorem secTrace_add (x : κ → Ω) (e : Fin (D + 1) → κ) (_h : IsRatProjFrame x e) (n : ℕ) {s t : Ω}
    (hs : s ∈ sec ℤ x n) (ht : t ∈ sec ℤ x n) :
    secTrace x e n (s + t) = secTrace x e n s + secTrace x e n t := by
  have hs' := div_pow_mem_fnField x (e 0) hs
  have ht' := div_pow_mem_fnField x (e 0) ht
  have hst : (s + t) / x (e 0) ^ n ∈ fnField x := by
    rw [add_div]
    exact add_mem hs' ht'
  unfold secTrace fnTrace
  rw [dif_pos hst, dif_pos hs', dif_pos ht']
  have key : (⟨(s + t) / x (e 0) ^ n, hst⟩ : IntermediateField.extendScalars (fnField_comp_le x e)) =
      ⟨s / x (e 0) ^ n, hs'⟩ + ⟨t / x (e 0) ^ n, ht'⟩ := Subtype.ext (add_div s t _)
  rw [key, map_add]
  push_cast
  ring
instance sec_moduleFinite (x : κ → Ω) (n : ℕ) : Module.Finite ℤ (sec ℤ x n) :=
  Module.Finite.iff_fg.mpr (sec_fg x n)
instance sec_moduleFree (x : κ → Ω) (n : ℕ) : Module.Free ℤ (sec ℤ x n) := inferInstance
noncomputable def alphaMap (x : κ → Ω) (e : Fin (D + 1) → κ) {k δ : ℕ} (ε : Fin δ → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (n : ℕ) : (Fin δ → sec ℤ (x ∘ e) n) →ₗ[ℤ] sec ℤ x (n + k) where
  toFun P := ⟨∑ l, (P l : Ω) * ε l, alpha_mem x e ε hε (fun l => P l) (fun l => (P l).2)⟩
  map_add' P Q := by ext; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c P := by ext; simp [Finset.mul_sum, mul_assoc]
noncomputable def betaMap (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) {k δ : ℕ} (ε : Fin δ → Ω)
    (hε : ∀ l, ε l ∈ sec ℤ x k) (n : ℕ) : sec ℤ x n →+ (Fin δ → sec ℤ (x ∘ e) (n + k)) :=
  AddMonoidHom.mk' (fun s l => ⟨secTrace x e (n + k) ((s : Ω) * ε l), secTrace_mem x e h (n + k)
      (by rw [← sec_mul_sec]; exact Submodule.mul_mem_mul s.2 (hε l))⟩)
    (fun s t => by
      funext l; ext
      simp only [Submodule.coe_add, add_mul, Pi.add_apply]
      have h1 := Submodule.mul_mem_mul s.2 (hε l)
      have h2 := Submodule.mul_mem_mul t.2 (hε l)
      rw [sec_mul_sec] at h1 h2
      exact secTrace_add x e h.isRatProjFrame (n + k) h1 h2)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


