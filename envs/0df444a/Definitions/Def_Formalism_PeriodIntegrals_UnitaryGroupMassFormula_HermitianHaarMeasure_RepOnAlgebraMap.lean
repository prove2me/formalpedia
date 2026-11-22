-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:53.576374+00:00
-- url     : https://prove2.me/theorems/ecda4176-4a7e-4d89-987d-eeb093baeffe
-- title:
--   Rep On Algebra Map
-- statement:
--   Definitions and structural lemmas for Rep On Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
def pr (μ : Measure α) (ι : α → β) (f h : β → ℂ) : ℂ := ∫ x, f (ι x) * star (h (ι x)) ∂μ
def IntOn (μ : Measure α) (ι : α → β) (𝓕 : Submodule ℂ (β → ℂ)) : Prop :=
  ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, Integrable (fun x => f (ι x) * star (h (ι x))) μ
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
theorem pr_conj (f h : β → ℂ) : pr μ ι h f = star (pr μ ι f h) := by
  simp only [pr]
  rw [show star (∫ x, f (ι x) * star (h (ι x)) ∂μ) = (starRingEnd ℂ) (∫ x, f (ι x) * star (h (ι x)) ∂μ) from rfl,
    ← integral_conj]
  congr 1
  funext x
  simp [mul_comm]
theorem pr_smul_left (c : ℂ) (f h : β → ℂ) : pr μ ι (c • f) h = c * pr μ ι f h := by
  simp only [pr, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
theorem pr_add_left (hI : IntOn μ ι 𝓕) {f f' h : β → ℂ} (hf : f ∈ 𝓕) (hf' : f' ∈ 𝓕) (hh : h ∈ 𝓕) :
    pr μ ι (f + f') h = pr μ ι f h + pr μ ι f' h := by
  simp only [pr, Pi.add_apply, add_mul]
  exact integral_add (hI f hf h hh) (hI f' hf' h hh)
theorem pr_sub_left (hI : IntOn μ ι 𝓕) {f f' h : β → ℂ} (hf : f ∈ 𝓕) (hf' : f' ∈ 𝓕) (hh : h ∈ 𝓕) :
    pr μ ι (f - f') h = pr μ ι f h - pr μ ι f' h := by
  simp only [pr, Pi.sub_apply, sub_mul]
  exact integral_sub (hI f hf h hh) (hI f' hf' h hh)
def N (hI : IntOn μ ι 𝓕) : Submodule ℂ 𝓕 where
  carrier := {f | ∀ h ∈ 𝓕, pr μ ι f.1 h = 0}
  zero_mem' := by
    intro h _
    simp [pr]
  add_mem' := by
    intro a b ha hb h hh
    simp only [Submodule.coe_add]
    rw [pr_add_left hI a.2 b.2 hh, ha h hh, hb h hh, add_zero]
  smul_mem' := by
    intro c a ha h hh
    simp only [Submodule.coe_smul]
    rw [pr_smul_left, ha h hh, mul_zero]
abbrev X (hI : IntOn μ ι 𝓕) := 𝓕 ⧸ N hI
variable (hI : IntOn μ ι 𝓕)
def rep (x : X hI) : 𝓕 := (Submodule.Quotient.mk_surjective (N hI) x).choose
theorem mk_rep (x : X hI) : Submodule.Quotient.mk (rep hI x) = x := (Submodule.Quotient.mk_surjective (N hI) x).choose_spec
theorem pr_left_eq_of_sub_mem_N {f f' : 𝓕} (hf : f - f' ∈ N hI) (h : β → ℂ) (hh : h ∈ 𝓕) :
    pr μ ι f.1 h = pr μ ι f'.1 h := by
  have hf' : ∀ k ∈ 𝓕, pr μ ι (f - f').1 k = 0 := hf
  have := hf' h hh
  rw [Submodule.coe_sub, pr_sub_left hI f.2 f'.2 hh] at this
  exact sub_eq_zero.mp this
theorem pr_eq_of_sub {f f' h h' : 𝓕} (hf : f - f' ∈ N hI) (hh : h - h' ∈ N hI) :
    pr μ ι f.1 h.1 = pr μ ι f'.1 h'.1 := by
  rw [pr_left_eq_of_sub_mem_N hI hf h.1 h.2, pr_conj (μ := μ) (ι := ι) h.1 f'.1,
    pr_conj (μ := μ) (ι := ι) h'.1 f'.1, pr_left_eq_of_sub_mem_N hI hh f'.1 f'.2]
def ip (x y : X hI) : ℂ := pr μ ι (rep hI x).1 (rep hI y).1
theorem ip_mk (f h : 𝓕) : ip hI (Submodule.Quotient.mk f) (Submodule.Quotient.mk h) = pr μ ι f.1 h.1 := by
  unfold ip
  apply pr_eq_of_sub hI
  · exact (Submodule.Quotient.eq _).mp (mk_rep hI _)
  · exact (Submodule.Quotient.eq _).mp (mk_rep hI _)
theorem ip_conj (x y : X hI) : ip hI y x = star (ip hI x y) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [ip_mk, ip_mk, pr_conj]
theorem ip_add_left (x x' y : X hI) : ip hI (x + x') y = ip hI x y + ip hI x' y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x'
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_add, ip_mk, ip_mk, ip_mk, Submodule.coe_add,
    pr_add_left hI f.2 f'.2 h.2]
theorem ip_smul_left (c : ℂ) (x y : X hI) : ip hI (c • x) y = c * ip hI x y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_smul, ip_mk, ip_mk, Submodule.coe_smul, pr_smul_left]
theorem ip_add_right (x y y' : X hI) : ip hI x (y + y') = ip hI x y + ip hI x y' := by
  rw [ip_conj hI (y + y') x, ip_add_left, star_add, ← ip_conj hI y x,
    ← ip_conj hI y' x]
theorem ip_smul_right (c : ℂ) (x y : X hI) : ip hI x (c • y) = star c * ip hI x y := by
  rw [ip_conj hI (c • y) x, ip_smul_left, star_mul', ← ip_conj hI y x]
theorem ip_sub_left (x x' y : X hI) : ip hI (x - x') y = ip hI x y - ip hI x' y := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  obtain ⟨f', rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x'
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) y
  rw [← Submodule.Quotient.mk_sub, ip_mk, ip_mk, ip_mk, Submodule.coe_sub,
    pr_sub_left hI f.2 f'.2 h.2]
theorem ip_sub_right (x y y' : X hI) : ip hI x (y - y') = ip hI x y - ip hI x y' := by
  rw [ip_conj hI (y - y') x, ip_sub_left, star_sub, ← ip_conj hI y x,
    ← ip_conj hI y' x]
theorem eq_zero_of_ip (x : X hI) (hx : ∀ y, ip hI x y = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  rw [Submodule.Quotient.mk_eq_zero]
  show ∀ h ∈ 𝓕, pr μ ι f.1 h = 0
  intro h hh
  have := hx (Submodule.Quotient.mk ⟨h, hh⟩)
  rwa [ip_mk] at this
theorem eq_of_ip_right {S T : Module.End ℂ (X hI)} (h : ∀ x y, ip hI x (S y) = ip hI x (T y)) : S = T := by
  refine LinearMap.ext fun y => ?_
  rw [← sub_eq_zero]
  apply eq_zero_of_ip hI
  intro x
  rw [ip_conj hI x, ip_sub_right, h x y, sub_self, star_zero]
def Adj : Subalgebra ℂ (Module.End ℂ (X hI)) where
  carrier := {T | ∃ T' : Module.End ℂ (X hI), ∀ x y, ip hI (T x) y = ip hI x (T' y)}
  mul_mem' := by
    rintro S T ⟨S', hS⟩ ⟨T', hT⟩
    refine ⟨T' * S', fun x y => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hS, hT]
  add_mem' := by
    rintro S T ⟨S', hS⟩ ⟨T', hT⟩
    refine ⟨S' + T', fun x y => ?_⟩
    simp only [LinearMap.add_apply]
    rw [ip_add_left, ip_add_right, hS, hT]
  algebraMap_mem' := by
    intro c
    refine ⟨algebraMap ℂ (Module.End ℂ (X hI)) (star c), fun x y => ?_⟩
    simp only [Module.algebraMap_end_apply]
    rw [ip_smul_left, ip_smul_right, star_star]
abbrev A := ↥(Adj hI)
def adjOf (T : A hI) : Module.End ℂ (X hI) := T.2.choose
theorem adjOf_spec (T : A hI) (x y : X hI) : ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (adjOf hI T y) := T.2.choose_spec x y
theorem adjOf_mem (T : A hI) : adjOf hI T ∈ Adj hI := by
  show ∃ T' : Module.End ℂ (X hI), ∀ x y, ip hI (adjOf hI T x) y = ip hI x (T' y)
  refine ⟨(T : Module.End ℂ (X hI)), fun x y => ?_⟩
  rw [ip_conj hI y (adjOf hI T x), ← adjOf_spec, ← ip_conj hI ((T : Module.End ℂ (X hI)) y) x]
theorem adjOf_unique (T : A hI) (S : Module.End ℂ (X hI))
    (h : ∀ x y, ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (S y)) : adjOf hI T = S := by
  apply eq_of_ip_right hI
  intro x y
  rw [← adjOf_spec, h]
instance instStar : Star (A hI) := ⟨fun T => ⟨adjOf hI T, adjOf_mem hI T⟩⟩
theorem star_coe (T : A hI) : ((star T : A hI) : Module.End ℂ (X hI)) = adjOf hI T := rfl
theorem star_spec (T : A hI) (x y : X hI) :
    ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x (((star T : A hI) : Module.End ℂ (X hI)) y) := adjOf_spec hI T x y
theorem star_eq_of (T S : A hI)
    (h : ∀ x y, ip hI ((T : Module.End ℂ (X hI)) x) y = ip hI x ((S : Module.End ℂ (X hI)) y)) : star T = S := by
  apply Subtype.ext
  rw [star_coe]
  exact adjOf_unique hI T _ h
instance instStarRing : StarRing (A hI) where
  star_involutive T := by
    apply star_eq_of
    intro x y
    rw [ip_conj hI y, ← star_spec, ← ip_conj]
  star_mul S T := by
    apply star_eq_of
    intro x y
    show ip hI ((S : Module.End ℂ (X hI)) ((T : Module.End ℂ (X hI)) x)) y =
      ip hI x (((star T : A hI) : Module.End ℂ (X hI)) (((star S : A hI) : Module.End ℂ (X hI)) y))
    rw [star_spec, star_spec]
  star_add S T := by
    apply star_eq_of
    intro x y
    show ip hI ((S : Module.End ℂ (X hI)) x + (T : Module.End ℂ (X hI)) x) y =
      ip hI x (((star S : A hI) : Module.End ℂ (X hI)) y + ((star T : A hI) : Module.End ℂ (X hI)) y)
    rw [ip_add_left, ip_add_right, star_spec, star_spec]
instance instStarModule : StarModule ℂ (A hI) where
  star_smul c T := by
    apply star_eq_of
    intro x y
    show ip hI (c • (T : Module.End ℂ (X hI)) x) y = ip hI x (star c • ((star T : A hI) : Module.End ℂ (X hI)) y)
    rw [ip_smul_left, ip_smul_right, star_star, star_spec]
open scoped Classical in

def mk' (f : β → ℂ) : X hI := if hf : f ∈ 𝓕 then Submodule.Quotient.mk ⟨f, hf⟩ else 0
theorem mk'_of {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI f = Submodule.Quotient.mk ⟨f, hf⟩ := by
  rw [mk', dif_pos hf]
theorem mk'_surj (x : X hI) : ∃ f ∈ 𝓕, mk' hI f = x := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (N hI) x
  exact ⟨f.1, f.2, mk'_of hI f.2⟩
theorem ip_mk' {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : ip hI (mk' hI f) (mk' hI h) = pr μ ι f h := by
  rw [mk'_of hI hf, mk'_of hI hh, ip_mk]
theorem mk'_add {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : mk' hI (f + h) = mk' hI f + mk' hI h := by
  rw [mk'_of hI (𝓕.add_mem hf hh), mk'_of hI hf, mk'_of hI hh, ← Submodule.Quotient.mk_add]
  rfl
theorem mk'_smul (c : ℂ) {f : β → ℂ} (hf : f ∈ 𝓕) : mk' hI (c • f) = c • mk' hI f := by
  rw [mk'_of hI (𝓕.smul_mem c hf), mk'_of hI hf, ← Submodule.Quotient.mk_smul]
  rfl
theorem mk'_sub {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : mk' hI (f - h) = mk' hI f - mk' hI h := by
  rw [mk'_of hI (𝓕.sub_mem hf hh), mk'_of hI hf, mk'_of hI hh, ← Submodule.Quotient.mk_sub]
  rfl
section onG
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
include hG in
theorem pr_vanish {F : β → ℂ} (hF : ∀ g ∈ G, F g = 0) (h : β → ℂ) : pr μ ι F h = 0 := by
  unfold pr
  apply integral_eq_zero_of_ae
  filter_upwards [hG] with x hx
  simp [hF _ hx]
include hG in
theorem mk'_eq_of_eqOn {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) (he : ∀ g ∈ G, f g = h g) :
    mk' hI f = mk' hI h := by
  rw [← sub_eq_zero, ← mk'_sub hI hf hh, mk'_of hI (𝓕.sub_mem hf hh), Submodule.Quotient.mk_eq_zero]
  show ∀ k ∈ 𝓕, pr μ ι (f - h) k = 0
  intro k _
  exact pr_vanish G hG (fun g hg => by simp [he g hg]) k
structure AdjOp (Φ Φ' : (β → ℂ) → (β → ℂ)) : Prop where
  mem : ∀ f ∈ 𝓕, Φ f ∈ 𝓕
  mem' : ∀ f ∈ 𝓕, Φ' f ∈ 𝓕
  lin : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, ∀ c : ℂ, ∀ g ∈ G, Φ (fun x => f x + c * h x) g = Φ f g + c * Φ h g
  lin' : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, ∀ c : ℂ, ∀ g ∈ G, Φ' (fun x => f x + c * h x) g = Φ' f g + c * Φ' h g
  adj : ∀ f ∈ 𝓕, ∀ h ∈ 𝓕, pr μ ι (Φ f) h = pr μ ι f (Φ' h)
variable {G}
theorem AdjOp.symm {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ' Φ where
  mem := hΦ.mem'
  mem' := hΦ.mem
  lin := hΦ.lin'
  lin' := hΦ.lin
  adj f hf h hh := by
    rw [pr_conj, ← hΦ.adj h hh f hf, ← pr_conj]
theorem adjOp_map_add_smul {Φ Φ' : (β → ℂ) → (β → ℂ)}
    (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) (c : ℂ) :
    ∀ g ∈ G, Φ (f + c • h) g = Φ f g + c * Φ h g :=
  fun g hg => hΦ.lin f hf h hh c g hg
theorem AdjOp.zero {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') :
    ∀ g ∈ G, Φ 0 g = 0 := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) (𝓕.zero_mem) (𝓕.zero_mem) 1 g hg
  rw [smul_zero, add_zero] at this
  linear_combination -this
theorem AdjOp.add {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : ∀ g ∈ G, Φ (f + h) g = Φ f g + Φ h g := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) hf hh 1 g hg
  rwa [one_smul, one_mul] at this
theorem AdjOp.smul {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    (c : ℂ) {h : β → ℂ} (hh : h ∈ 𝓕) : ∀ g ∈ G, Φ (c • h) g = c * Φ h g := by
  intro g hg
  have := (_root_.PI.QnHermHaar.Gen.adjOp_map_add_smul hΦ) (𝓕.zero_mem) hh c g hg
  rwa [zero_add, hΦ.zero g hg, zero_add] at this
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)
def opF {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : 𝓕 →ₗ[ℂ] X hI where
  toFun f := mk' hI (Φ f.1)
  map_add' f h := by
    show mk' hI (Φ (f.1 + h.1)) = mk' hI (Φ f.1) + mk' hI (Φ h.1)
    rw [mk'_eq_of_eqOn hI G hG (hΦ.mem _ (𝓕.add_mem f.2 h.2)) (𝓕.add_mem (hΦ.mem _ f.2) (hΦ.mem _ h.2))
      (fun g hg => by rw [hΦ.add f.2 h.2 g hg]; rfl)]
    exact mk'_add hI (hΦ.mem _ f.2) (hΦ.mem _ h.2)
  map_smul' c f := by
    show mk' hI (Φ (c • f.1)) = c • mk' hI (Φ f.1)
    rw [mk'_eq_of_eqOn hI G hG (hΦ.mem _ (𝓕.smul_mem c f.2)) (𝓕.smul_mem c (hΦ.mem _ f.2))
      (fun g hg => by rw [hΦ.smul c f.2 g hg]; rfl)]
    exact mk'_smul hI c (hΦ.mem _ f.2)
def opX {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : Module.End ℂ (X hI) :=
  (N hI).liftQ (opF hI hG hΦ) (by
    intro f hf
    rw [LinearMap.mem_ker]
    show mk' hI (Φ f.1) = 0
    rw [mk'_of hI (hΦ.mem _ f.2), Submodule.Quotient.mk_eq_zero]
    intro h hh
    rw [hΦ.adj f.1 f.2 h hh]
    exact hf _ (hΦ.mem' h hh))
theorem opX_mk' {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f : β → ℂ} (hf : f ∈ 𝓕) : opX hI hG hΦ (mk' hI f) = mk' hI (Φ f) := by
  rw [mk'_of hI hf]
  rfl
def toA {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ') : A hI :=
  ⟨opX hI hG hΦ, opX hI hG hΦ.symm, fun x y => by
    obtain ⟨f, hf, rfl⟩ := mk'_surj hI x
    obtain ⟨h, hh, rfl⟩ := mk'_surj hI y
    rw [opX_mk' hI hG hΦ hf, opX_mk' hI hG hΦ.symm hh, ip_mk' hI (hΦ.mem _ hf) hh,
      ip_mk' hI hf (hΦ.mem' _ hh)]
    exact hΦ.adj f hf h hh⟩
def RepOn (T : A hI) (Φ : (β → ℂ) → β → ℂ) : Prop :=
  ∀ f ∈ 𝓕, Φ f ∈ 𝓕 ∧ (T : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f)
end onG
end PI.QnHermHaar.Gen


