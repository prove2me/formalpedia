-- Prove2me | solution 1 for AlgebraicCurve.natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7b3cfd9a-adf0-56d9-9d9c-d7371ba3ba95

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (hdeg : ∀ v : Place k F, v.deg = 1)
    (hfin : ∀ D : Divisor k F, FiniteDimensional k ↥(LSpace D))
    (hRR : ∀ D : Divisor k F, 2 * (genusFF k F : ℤ) - 1 ≤ D.degree → (ell D : ℤ) = D.degree + 1 - genusFF k F)
    (W : Finset (Place k F)) (NP : Set (Place k F × Place k F))
    (hNP : ∀ w ∈ W, ∃ v' : Place k F, (w, v') ∈ NP)
    (D₁ D₂ : Divisor k F) (hD₁ : ∀ w ∈ W, D₁ w = 0)
    (hdeg₁ : 2 * (genusFF k F : ℤ) - 1 + W.card ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF k F : ℤ) - 1 ≤ D₂.degree)
    {m : ℕ} (x : Fin m → F × F)
    (hx₁ : ∀ a, ∀ v : Place k F, (x a).1 = 0 ∨ -D₁ v ≤ v.ord (x a).1)
    (hx₂ : ∀ a, ∀ v : Place k F, (x a).2 = 0 ∨ -D₂ v ≤ v.ord (x a).2)
    (hxNP : ∀ a, ∀ nd ∈ NP, ∃ c : k, nd.1.HasValue (x a).1 c ∧ nd.2.HasValue (x a).2 c)
    (hli : LinearIndependent k x) :
    (m : ℤ) ≤ D₁.degree + D₂.degree + 2 - 2 * (genusFF k F : ℤ) - W.card := by
  classical
  haveI : ∀ D : Divisor k F, FiniteDimensional k ↥(LSpace D) := hfin

  have hvadd : ∀ {v : Place k F} {g g' : F} {a a' : k}, v.HasValue g a → v.HasValue g' a' →
      v.HasValue (g + g') (a + a') := fun {v g g' a a'} h h' =>
    ⟨add_mem h.mem h'.mem, by
      rw [show (⟨g + g', add_mem h.mem h'.mem⟩ : v.toValuationSubring) = ⟨g, h.mem⟩ + ⟨g', h'.mem⟩ from rfl]
      simp only [map_add, h.residue_eq, h'.residue_eq]⟩

  let nodeDiv : Divisor k F := ∑ w ∈ W, Finsupp.single w 1
  have nodeDiv_of_mem : ∀ {v}, v ∈ W → nodeDiv v = 1 := fun {v} hv => by
    simp [nodeDiv, Finsupp.single_apply, hv]
  have nodeDiv_of_not_mem : ∀ {v}, v ∉ W → nodeDiv v = 0 := fun {v} hv => by
    simp [nodeDiv, Finsupp.single_apply, hv]
  have degree_nodeDiv : Divisor.degree nodeDiv = W.card := by
    show Divisor.degree (∑ w ∈ W, Finsupp.single w 1) = _
    rw [map_sum]
    simp [Divisor.degree_single, hdeg]

  have fst_mem : ∀ {y : F × F}, (∀ v : Place k F, y.1 = 0 ∨ -D₁ v ≤ v.ord y.1) →
      (∀ nd ∈ NP, ∃ c : k, nd.1.HasValue y.1 c ∧ nd.2.HasValue y.2 c) → y.2 = 0 →
      y.1 ∈ riemannRochSpace (D₁ - nodeDiv) := by
    intro y hy₁ hyNP hy2
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases h0 : y.1 = 0
    · exact Or.inl h0
    right
    rw [Finsupp.sub_apply]
    by_cases hv : v ∈ W
    · rw [hD₁ v hv, nodeDiv_of_mem hv]
      obtain ⟨v', hvv'⟩ := hNP v hv
      have hval : v.HasValue y.1 0 := by
        obtain ⟨c, hc₁, hc₂⟩ := hyNP (v, v') hvv'
        rw [hy2] at hc₂
        have h00 : (v' : Place k F).HasValue (0 : F) 0 := by
          have h := Place.hasValue_algebraMap v' (0 : k)
          rwa [map_zero] at h
        have hc0 : c = 0 := Place.HasValue.unique hc₂ h00
        rw [hc0] at hc₁
        exact hc₁

      have hpos : 0 < v.ord y.1 := by
        have hmax : (⟨y.1, hval.mem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
          (IsLocalRing.residue_eq_zero_iff _).mp (by rw [hval.residue_eq, map_zero])
        have hnonunit : ¬ IsUnit (⟨y.1, hval.mem⟩ : v.toValuationSubring) :=
          _root_.mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)
        have hle : v.adicValuation y.1 ≤ 1 := by
          rw [show y.1 = ((⟨y.1, hval.mem⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
        have hne1 : v.adicValuation y.1 ≠ 1 := fun h1 =>
          hnonunit ((v.adicValuation_coe_eq_one_iff ⟨y.1, hval.mem⟩).mp h1)
        have hlt : v.adicValuation y.1 < 1 := lt_of_le_of_ne hle hne1
        have hlog : WithZero.log (v.adicValuation y.1) < 0 := by
          rw [← WithZero.exp_zero] at hlt
          exact (WithZero.log_lt_iff_lt_exp (v.adicValuation_ne_zero h0)).mpr hlt
        unfold Place.ord
        omega
      omega
    · rw [nodeDiv_of_not_mem hv, sub_zero]
      exact (hy₁ v).resolve_left h0

  haveI : FiniteDimensional k (Submodule.span k (Set.range x)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range x)
  have hU : Module.finrank k (Submodule.span k (Set.range x)) = m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]

  let PC : Submodule k (F × F) :=
    { carrier := {y | (∀ v : Place k F, y.1 = 0 ∨ -D₁ v ≤ v.ord y.1) ∧ (∀ v : Place k F, y.2 = 0 ∨ -D₂ v ≤ v.ord y.2) ∧
        ∀ nd ∈ NP, ∃ c : k, nd.1.HasValue y.1 c ∧ nd.2.HasValue y.2 c}
      zero_mem' := by
        refine ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun nd _ => ⟨0, ?_, ?_⟩⟩
        · have h := Place.hasValue_algebraMap nd.1 (0 : k); rwa [map_zero] at h
        · have h := Place.hasValue_algebraMap nd.2 (0 : k); rwa [map_zero] at h
      add_mem' := by
        intro a b ha hb
        refine ⟨?_, ?_, ?_⟩
        · exact mem_riemannRochSpace_iff.mp
            (add_mem (mem_riemannRochSpace_iff.mpr ha.1) (mem_riemannRochSpace_iff.mpr hb.1))
        · exact mem_riemannRochSpace_iff.mp
            (add_mem (mem_riemannRochSpace_iff.mpr ha.2.1) (mem_riemannRochSpace_iff.mpr hb.2.1))
        · intro nd hnd
          obtain ⟨c, hc₁, hc₂⟩ := ha.2.2 nd hnd
          obtain ⟨d, hd₁, hd₂⟩ := hb.2.2 nd hnd
          exact ⟨c + d, hvadd hc₁ hd₁, hvadd hc₂ hd₂⟩
      smul_mem' := by
        intro r a ha
        refine ⟨?_, ?_, ?_⟩
        · exact mem_riemannRochSpace_iff.mp (Submodule.smul_mem _ r (mem_riemannRochSpace_iff.mpr ha.1))
        · exact mem_riemannRochSpace_iff.mp (Submodule.smul_mem _ r (mem_riemannRochSpace_iff.mpr ha.2.1))
        · intro nd hnd
          obtain ⟨c, hc₁, hc₂⟩ := ha.2.2 nd hnd
          refine ⟨r * c, ?_, ?_⟩
          · rw [Prod.smul_fst, Algebra.smul_def]
            exact Place.HasValue.mul (v := nd.1) (Place.hasValue_algebraMap nd.1 r) hc₁
          · rw [Prod.smul_snd, Algebra.smul_def]
            exact Place.HasValue.mul (v := nd.2) (Place.hasValue_algebraMap nd.2 r) hc₂ }
  have hUV : Submodule.span k (Set.range x) ≤ PC := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨hx₁ a, hx₂ a, hxNP a⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Submodule.span k (Set.range x) →ₗ[k] F,
      φ = (LinearMap.snd k F F).comp (Submodule.span k (Set.range x)).subtype := ⟨_, rfl⟩

  have hrange : LinearMap.range φ ≤ riemannRochSpace D₂ := by
    rw [hφ, LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    exact mem_riemannRochSpace_iff.mpr (hx₂ a)
  have h₂ : Module.finrank k (LinearMap.range φ) ≤ ell D₂ := Submodule.finrank_mono hrange

  have hsnd : ∀ y : LinearMap.ker φ, ((y.1 : F × F)).2 = 0 := by
    intro y
    have h' : φ y.1 = 0 := LinearMap.mem_ker.mp y.2
    have h3 := congrArg (fun ψ : ↥(Submodule.span k (Set.range x)) →ₗ[k] F => ψ y.1) hφ
    exact h3.symm.trans h'
  have h₁ : Module.finrank k (LinearMap.ker φ) ≤ ell (D₁ - nodeDiv) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := LinearMap.codRestrict
      (riemannRochSpace (D₁ - nodeDiv))
      ((LinearMap.fst k F F).comp
        ((Submodule.span k (Set.range x)).subtype.comp (LinearMap.ker φ).subtype)) ?hmem) ?hinj
    case hmem =>
      intro y
      have hy := hUV y.1.2
      exact fst_mem hy.1 hy.2.2 (hsnd y)
    case hinj =>
      intro y z hyz
      have hy1 : ((y.1 : F × F)).1 = ((z.1 : F × F)).1 := congrArg Subtype.val hyz
      have hy2 : ((y.1 : F × F)).2 = ((z.1 : F × F)).2 := (hsnd y).trans (hsnd z).symm
      exact Subtype.ext (Subtype.ext (Prod.ext hy1 hy2))
  have hle : Module.finrank k (Submodule.span k (Set.range x)) ≤ ell D₂ + ell (D₁ - nodeDiv) :=
    calc Module.finrank k (Submodule.span k (Set.range x))
        = Module.finrank k (LinearMap.range φ) + Module.finrank k (LinearMap.ker φ) :=
          (LinearMap.finrank_range_add_finrank_ker φ).symm
      _ ≤ ell D₂ + ell (D₁ - nodeDiv) := add_le_add h₂ h₁

  have hdeg₁' : Divisor.degree (D₁ - nodeDiv) = D₁.degree - W.card := by
    rw [map_sub, degree_nodeDiv]
  have hRR₁ := hRR (D₁ - nodeDiv) (by rw [hdeg₁']; omega)
  have hRR₂ := hRR D₂ hdeg₂
  rw [hdeg₁'] at hRR₁
  omega

end S_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue
end P2MW
export P2MW.S_AlgebraicCurve_natCast_le_degree_add_degree_of_linearIndependent_of_mem_riemannRochSpace_of_hasValue (solution)
