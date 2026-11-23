-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:35.041872+00:00
-- url     : https://prove2.me/theorems/e00de1ec-8607-40d2-af52-78307a3a9a70
-- title:
--   Analytic Algebraic Germ
-- statement:
--   Definitions and structural lemmas for Analytic Algebraic Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AnalyticAlgebraicGerm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
theorem eventuallyEq_zero_codiscrete_iff {f : ℂ → ℂ} :
    f =ᶠ[codiscrete ℂ] 0 ↔ ∀ x, ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  change {z | f z = (0 : ℂ → ℂ) z} ∈ codiscreteWithin univ ↔ _
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [compl_univ, union_empty, mem_univ, true_implies, Pi.zero_apply]
  rfl
theorem eventuallyEq_zero_codiscrete_of_nhdsNE {f : ℂ → ℂ} (hf : Meromorphic f) {x : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] x, f z = 0) : f =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff]
  intro u
  have hx : meromorphicOrderAt f x = ⊤ := meromorphicOrderAt_eq_top_iff.2 h
  by_contra hu
  have hu' : meromorphicOrderAt f u ≠ ⊤ := fun ht ↦ hu (meromorphicOrderAt_eq_top_iff.1 ht)
  exact (hf.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ u) (mem_univ x) hu' hx
theorem eventually_ne_zero_codiscrete {f : ℂ → ℂ} (hf : Meromorphic f)
    (h : ¬ f =ᶠ[codiscrete ℂ] 0) : ∀ᶠ z in codiscrete ℂ, f z ≠ 0 := by
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := fun u _ ht ↦
    h (eventuallyEq_zero_codiscrete_of_nhdsNE hf (meromorphicOrderAt_eq_top_iff.1 ht))
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hf.meromorphicOn (s := univ)) hall
theorem isOpen_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : IsOpen S :=
  (mem_codiscrete'.1 hS).1
theorem eventually_analyticAt {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∀ᶠ z in codiscrete ℂ, AnalyticAt ℂ f z :=
  (hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin
theorem deriv_eventuallyEq_codiscrete {f g : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] g) :
    deriv f =ᶠ[codiscrete ℂ] deriv g := by
  have hS := isOpen_of_mem_codiscrete h
  filter_upwards [h] with z hz
  exact Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hS.mem_nhds hz) fun w hw ↦ hw)
def meroSubalgebra : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | Meromorphic f}
  mul_mem' hf hg := Meromorphic.mul hf hg
  add_mem' hf hg := Meromorphic.add hf hg
  algebraMap_mem' c := Meromorphic.const c
def meroNull : Ideal meroSubalgebra where
  carrier := {f | (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0}
  add_mem' {f g} hf hg := by
    change (fun z ↦ f.1 z + g.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf, hg] with z h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    change ((0 : meroSubalgebra) : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0
    exact Filter.EventuallyEq.rfl
  smul_mem' c f hf := by
    change (fun z ↦ c.1 z * f.1 z) =ᶠ[codiscrete ℂ] 0
    filter_upwards [hf] with z h
    simp only [Pi.zero_apply] at h ⊢
    rw [h, mul_zero]
theorem mem_meroNull {f : meroSubalgebra} : f ∈ meroNull ↔ (f : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0 :=
  Iff.rfl
instance meroNull_isMaximal : meroNull.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 ↦ ?_, fun J x hle hx hxJ ↦ ?_⟩
  · have h := (eventuallyEq_zero_codiscrete_iff.1 (mem_meroNull.1 h1)) 0
    obtain ⟨z, hz⟩ := h.exists
    exact one_ne_zero hz
  · have hf : Meromorphic (x : ℂ → ℂ) := x.2
    have hne := eventually_ne_zero_codiscrete hf hx
    let y : meroSubalgebra := ⟨(x : ℂ → ℂ)⁻¹, hf.inv⟩
    have hxy : x * y - 1 ∈ meroNull := by
      rw [mem_meroNull]
      change (fun z ↦ x.1 z * (x.1 z)⁻¹ - 1) =ᶠ[codiscrete ℂ] 0
      filter_upwards [hne] with z hz
      simp only [Pi.zero_apply]
      rw [mul_inv_cancel₀ hz, sub_self]
    have h1 : (1 : meroSubalgebra) = x * y - (x * y - 1) := by ring
    rw [h1]
    exact J.sub_mem (J.mul_mem_right y hxJ) (hle hxy)
abbrev MeroField : Type := meroSubalgebra ⧸ meroNull
noncomputable instance : Field MeroField := Ideal.Quotient.field _
noncomputable instance : DecidableEq MeroField := Classical.decEq _
open Classical in

def germ (f : ℂ → ℂ) : MeroField :=
  if h : Meromorphic f then Ideal.Quotient.mk meroNull ⟨f, h⟩ else 0
theorem germ_of {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = Ideal.Quotient.mk meroNull ⟨f, hf⟩ :=
  dif_pos hf
theorem germ_surjective (u : MeroField) : ∃ f : ℂ → ℂ, Meromorphic f ∧ germ f = u := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact ⟨f, hf, germ_of hf⟩
theorem germ_eq_germ_iff {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ f = germ g ↔ f =ᶠ[codiscrete ℂ] g := by
  rw [germ_of hf, germ_of hg, Ideal.Quotient.eq, mem_meroNull]
  change (f - g) =ᶠ[codiscrete ℂ] 0 ↔ _
  exact Filter.eventuallyEq_iff_sub.symm
theorem germ_congr {f g : ℂ → ℂ} (hf : Meromorphic f) (h : f =ᶠ[codiscrete ℂ] g) :
    germ f = germ g :=
  (germ_eq_germ_iff hf (hf.congr_codiscrete h)).2 h
theorem germ_add {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f + g) = germ f + germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.add hg), ← map_add]
  rfl
theorem germ_mul {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f * g) = germ f * germ g := by
  rw [germ_of hf, germ_of hg, germ_of (hf.mul hg), ← map_mul]
  rfl
theorem germ_const (c : ℂ) : germ (fun _ ↦ c) = algebraMap ℂ MeroField c := by
  rw [germ_of (Meromorphic.const c)]
  rfl
theorem germ_zero : germ (0 : ℂ → ℂ) = 0 := by
  have := germ_const 0
  rw [map_zero] at this
  exact this
theorem comp_affine_eventuallyEq_zero {f : ℂ → ℂ} (h : f =ᶠ[codiscrete ℂ] 0) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : (fun z ↦ f (t * z + s)) =ᶠ[codiscrete ℂ] 0 := by
  rw [eventuallyEq_zero_codiscrete_iff] at h ⊢
  intro x
  have hc : Continuous fun z : ℂ ↦ t * z + s := by fun_prop
  have hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ := fun z hz hz' ↦ hz (by
    simp only [mem_singleton_iff, add_left_inj] at hz' ⊢
    exact mul_left_cancel₀ ht hz')
  exact (hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually (h _)
theorem meromorphic_comp_affine {f : ℂ → ℂ} (hf : Meromorphic f) (t s : ℂ) :
    Meromorphic fun z ↦ f (t * z + s) := fun x ↦
  (hf (t * x + s)).comp_analyticAt (g := fun z ↦ t * z + s) (by fun_prop)
def compAffineSub (t s : ℂ) : meroSubalgebra →ₐ[ℂ] meroSubalgebra where
  toFun f := ⟨fun z ↦ f.1 (t * z + s), meromorphic_comp_affine f.2 t s⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
def affineComp (t s : ℂ) (ht : t ≠ 0) : MeroField →ₐ[ℂ] MeroField :=
  Ideal.Quotient.liftₐ meroNull ((Ideal.Quotient.mkₐ ℂ meroNull).comp (compAffineSub t s))
    fun f hf ↦ by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact comp_affine_eventuallyEq_zero hf ht s
def rep (u : MeroField) : ℂ → ℂ := (germ_surjective u).choose
theorem meromorphic_rep (u : MeroField) : Meromorphic (rep u) := (germ_surjective u).choose_spec.1
theorem germ_rep (u : MeroField) : germ (rep u) = u := (germ_surjective u).choose_spec.2
theorem rep_germ {f : ℂ → ℂ} (hf : Meromorphic f) : rep (germ f) =ᶠ[codiscrete ℂ] f :=
  (germ_eq_germ_iff (meromorphic_rep _) hf).1 (germ_rep _)
def derivFun (u : MeroField) : MeroField := germ (deriv (rep u))
theorem derivFun_germ {f : ℂ → ℂ} (hf : Meromorphic f) : derivFun (germ f) = germ (deriv f) :=
  germ_congr (meromorphic_rep _).deriv (deriv_eventuallyEq_codiscrete (rep_germ hf))
theorem derivFun_add (u v : MeroField) : derivFun (u + v) = derivFun u + derivFun v := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_add hf hg, derivFun_germ (hf.add hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_add hf.deriv hg.deriv]
  apply germ_congr (hf.add hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  exact deriv_add h1.differentiableAt h2.differentiableAt
theorem derivFun_mul (u v : MeroField) :
    derivFun (u * v) = u * derivFun v + v * derivFun u := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  obtain ⟨g, hg, rfl⟩ := germ_surjective v
  rw [← germ_mul hf hg, derivFun_germ (hf.mul hg), derivFun_germ hf, derivFun_germ hg,
    ← germ_mul hf hg.deriv, ← germ_mul hg hf.deriv, ← germ_add (hf.mul hg.deriv) (hg.mul hf.deriv)]
  apply germ_congr (hf.mul hg).deriv
  filter_upwards [eventually_analyticAt hf, eventually_analyticAt hg] with z h1 h2
  rw [deriv_mul h1.differentiableAt h2.differentiableAt]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring
theorem derivFun_algebraMap (c : ℂ) : derivFun (algebraMap ℂ MeroField c) = 0 := by
  rw [← germ_const, derivFun_germ (Meromorphic.const c)]
  have : deriv (fun _ : ℂ ↦ c) = 0 := by
    funext z
    simp
  rw [this, germ_zero]
theorem derivFun_smul (c : ℂ) (u : MeroField) : derivFun (c • u) = c • derivFun u := by
  rw [Algebra.smul_def, derivFun_mul, derivFun_algebraMap, mul_zero, add_zero, Algebra.smul_def]
def germDeriv : Derivation ℂ MeroField MeroField :=
  Derivation.mk' { toFun := derivFun, map_add' := derivFun_add, map_smul' := derivFun_smul }
    fun u v ↦ by
      show derivFun (u * v) = u • derivFun v + v • derivFun u
      rw [derivFun_mul, smul_eq_mul, smul_eq_mul]
end Elliptic
end GroundTheory.Global


