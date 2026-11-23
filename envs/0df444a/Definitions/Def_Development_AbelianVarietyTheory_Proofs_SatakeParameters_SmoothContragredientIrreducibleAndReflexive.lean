-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:59.706262+00:00
-- url     : https://prove2.me/theorems/fefdc096-70f8-47da-a3d2-154ecd61d23b
-- title:
--   Smooth Contragredient Irreducible And Reflexive
-- statement:
--   Definitions and structural lemmas for Smooth Contragredient Irreducible And Reflexive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SmoothContragredientIrreducibleAndReflexive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
theorem mem_fix {X : Type} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ G X}
    {K : Subgroup G} {v : X} : v ∈ fixed σ K ↔ ∀ h ∈ K, σ h v = v := by
  simp [fixed, eig]
theorem isLocallyConstant_orbit {π : Representation ℂ G V} (hπ : IsSmooth π) (u : V) :
    IsLocallyConstant fun g : G => π g u := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | π x u = u}) := (hπ u).preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simp)] with x hx
  have hx' : π (g⁻¹ * x) u = u := hx
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
theorem eq_zero_of_fixed_twKer {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {w : V} (hw : w ∈ fixed π K) (hw' : w ∈ twKer π K 1) : w = 0 := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨T, hTS, hwT⟩ := Submodule.mem_span_finite_of_mem_span hw'
  have hT : ∀ t ∈ T, ∃ (n : K) (v : V), t = π n v - v := by
    intro t ht
    obtain ⟨n, v, e⟩ := hTS ht
    exact ⟨n, v, by simpa using e⟩
  choose! n v hnv using hT
  let O : Set V := ⋃ t ∈ T, Set.range fun h : K => π h (v t)
  have hOfin : O.Finite := Set.Finite.biUnion T.finite_toSet fun t _ =>
    ((isLocallyConstant_orbit hπ (v t)).comp_continuous continuous_subtype_val).range_finite
  have hOst : ∀ (k : K) (x : V), x ∈ O → π k x ∈ O := by
    intro k x hx
    simp only [O, Set.mem_iUnion, Set.mem_range] at hx ⊢
    obtain ⟨t, ht, h, rfl⟩ := hx
    exact ⟨t, ht, k * h, by simp [map_mul]⟩
  have hvO : ∀ t ∈ T, v t ∈ O := fun t ht => by
    simp only [O, Set.mem_iUnion, Set.mem_range]
    exact ⟨t, ht, 1, by simp⟩
  haveI : Finite O := hOfin
  let φ : K → O → O := fun k x => ⟨π k x.1, hOst k x.1 x.2⟩
  have hφmul : ∀ k k' : K, φ (k * k') = φ k ∘ φ k' := by
    intro k k'; funext x; apply Subtype.ext; simp [φ, map_mul]
  have hφone : φ 1 = id := by funext x; apply Subtype.ext; simp [φ]
  let ι := Set.range φ
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Nonempty ι := ⟨⟨φ 1, 1, rfl⟩⟩
  let r : ι → K := fun f => f.2.choose
  have hr : ∀ f : ι, φ (r f) = f.1 := fun f => f.2.choose_spec
  let A : V →ₗ[ℂ] V := ∑ f : ι, π (r f)
  have hAO : ∀ x (hx : x ∈ O), A x = ∑ f : ι, (f.1 ⟨x, hx⟩).1 := by
    intro x hx
    simp only [A, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact congrArg Subtype.val (congrFun (hr f) ⟨x, hx⟩)
  let e : K → ι ≃ ι := fun k =>
    { toFun := fun f => ⟨f.1 ∘ φ k, r f * k, by rw [hφmul, hr f]⟩
      invFun := fun f => ⟨f.1 ∘ φ k⁻¹, r f * k⁻¹, by rw [hφmul, hr f]⟩
      left_inv := fun f => Subtype.ext (by
        show (f.1 ∘ φ k) ∘ φ k⁻¹ = f.1
        rw [Function.comp_assoc, ← hφmul, mul_inv_cancel, hφone, Function.comp_id])
      right_inv := fun f => Subtype.ext (by
        show (f.1 ∘ φ k⁻¹) ∘ φ k = f.1
        rw [Function.comp_assoc, ← hφmul, inv_mul_cancel, hφone, Function.comp_id]) }
  have hAinv : ∀ (k : K) x, x ∈ O → A (π k x) = A x := by
    intro k x hx
    rw [hAO _ (hOst k x hx), hAO x hx]
    exact Fintype.sum_equiv (e k) _ _ (fun f => rfl)
  have hker : (T : Set V) ⊆ LinearMap.ker A := by
    intro t ht
    rw [SetLike.mem_coe, LinearMap.mem_ker, hnv t ht, map_sub, hAinv _ _ (hvO t ht), sub_self]
  have hA0 : A w = 0 := LinearMap.mem_ker.1 (Submodule.span_le.2 hker hwT)
  have hAw : A w = (Fintype.card ι : ℂ) • w := by
    simp only [A, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun f _ => mem_fix.1 hw _ (r f).2, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
  have hne : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [hAw] at hA0
  exact (smul_eq_zero.1 hA0).resolve_left hne
end GlobalTheory.ContraRefl
namespace GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
theorem form_ext {X : Type} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ G X} (hσ : IsSmooth σ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {l l' : Module.Dual ℂ X}
    (hl : ∀ h ∈ K, ∀ w, l (σ h w) = l w) (hl' : ∀ h ∈ K, ∀ w, l' (σ h w) = l' w)
    (h : ∀ w ∈ fixed σ K, l w = l' w) : l = l' := by
  ext u
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hσ hK (l - l') u fun g hg => by
    simp [hl g hg, hl' g hg]
  simp only [LinearMap.sub_apply, h v hv, sub_self] at e
  exact sub_eq_zero.1 e.symm
theorem exists_fixed_contra {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (m : Module.Dual ℂ (fixed π K)) :
    ∃ l : smoothPart π.dual, (∀ h ∈ K, contra π h l = l) ∧
      ∀ v : fixed π K, (l : Module.Dual ℂ V) v = m v := by
  classical
  set N := twKer π K 1
  let g : fixed π K →ₗ[ℂ] V ⧸ N := N.mkQ ∘ₗ (fixed π K).subtype
  have hg : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have : (v : V) ∈ N := (Submodule.Quotient.mk_eq_zero N).1 hv
    exact Subtype.ext (eq_zero_of_fixed_twKer hπ hK v.2 this)
  obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective g hg
  let l₀ : Module.Dual ℂ V := m ∘ₗ g' ∘ₗ N.mkQ
  have hinv : ∀ h ∈ K, ∀ u, l₀ (π h u) = l₀ u := by
    intro h hh u
    have : N.mkQ (π h u) = N.mkQ u := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨⟨h, hh⟩, u, by simp⟩
    simp only [l₀, LinearMap.comp_apply, this]
  have hdual : ∀ h ∈ K, π.dual h l₀ = l₀ := by
    intro h hh
    ext u
    exact hinv _ (inv_mem hh) u
  refine ⟨⟨l₀, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) hdual)⟩,
    fun h hh => Subtype.ext (hdual h hh), fun v => ?_⟩
  have := LinearMap.congr_fun hg' v
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  show m (g' (N.mkQ v)) = m v
  rw [show N.mkQ (v : V) = g v from rfl, this]
def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype
theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) :
    ((l : smoothPart π.dual) : Module.Dual ℂ V) (π h w) = ((l : smoothPart π.dual) : Module.Dual ℂ V) w := by
  have h1 := mem_fix.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]
theorem res_injective {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) : Function.Injective (res π K) := by
  intro l l' h
  refine Subtype.ext (Subtype.ext ?_)
  exact form_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
    fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
theorem res_surjective {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Surjective (res π K) := by
  intro m
  obtain ⟨l, h1, h2⟩ := exists_fixed_contra hπ ho hK m
  exact ⟨⟨l, mem_fix.2 h1⟩, LinearMap.ext h2⟩
theorem exists_smooth_form_ne {π : Representation ℂ G V} (hπ : IsSmooth π)
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {v : V} (hv : v ≠ 0) : ∃ l : smoothPart π.dual, (l : Module.Dual ℂ V) v ≠ 0 := by
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((hπ v).mem_nhds (by simp))
  have hvK : v ∈ fixed π K := mem_fix.2 fun h hh => hKs hh
  obtain ⟨m, hm⟩ : ∃ m : Module.Dual ℂ (fixed π K), m ⟨v, hvK⟩ ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hv (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hne))
  obtain ⟨l, -, hl⟩ := exists_fixed_contra hπ ho hc m
  exact ⟨l, by rw [show v = ((⟨v, hvK⟩ : fixed π K) : V) from rfl, hl]; exact hm⟩
end GlobalTheory.ContraRefl
namespace GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
def ev (π : Representation ℂ G V) (hπ : IsSmooth π) : V →ₗ[ℂ] smoothPart (contra π).dual where
  toFun v := ⟨Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
      have hg' : π g v = v := hg
      ext l
      show (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = (l : Module.Dual ℂ V) v
      rw [inv_inv, hg'])⟩
  map_add' v w := Subtype.ext (LinearMap.ext fun l => by simp)
  map_smul' c v := Subtype.ext (LinearMap.ext fun l => by simp)
def evMap (π : Representation ℂ G V) (hπ : IsSmooth π) : π.IntertwiningMap (contra (contra π)) where
  toLinearMap := ev π hπ
  isIntertwining' g := by
    refine LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun l => ?_)
    show (l : Module.Dual ℂ V) (π g v) = (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v)
    rw [inv_inv]
theorem evMap_bijective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) : Function.Bijective (evMap π hπ.1) := by
  constructor
  · show Function.Injective (ev π hπ.1)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra h0
    obtain ⟨l, hl⟩ := exists_smooth_form_ne hπ.1 hG h0
    exact hl (LinearMap.congr_fun (congrArg Subtype.val hv) l)
  · intro Λ
    obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra (contra π) Λ).mem_nhds (by simp))
    haveI := hπ.2 K ho hc
    have hbij : Function.Bijective (res π K) := ⟨res_injective hπ.1 hc, res_surjective hπ.1 ho hc⟩
    let e := LinearEquiv.ofBijective (res π K) hbij
    let μ : Module.Dual ℂ (fixed (contra π) K) :=
      (Λ : Module.Dual ℂ (smoothPart π.dual)) ∘ₗ (fixed (contra π) K).subtype
    obtain ⟨v, hv⟩ := (Module.evalEquiv ℂ (fixed π K)).surjective (μ ∘ₗ e.symm.toLinearMap)
    have hfix : ∀ x : fixed (contra π) K,
        (Λ : Module.Dual ℂ (smoothPart π.dual)) x = ((x : smoothPart π.dual) : Module.Dual ℂ V) v := by
      intro x
      have h1 := LinearMap.congr_fun hv (e x)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
      exact h1.symm
    refine ⟨v, Subtype.ext (form_ext (isSmooth_contra π) hc (fun h hh w => ?_) (fun h hh w => ?_) fun w hw => ?_)⟩
    · show ((contra π h w : smoothPart π.dual) : Module.Dual ℂ V) v = (w : Module.Dual ℂ V) v
      rw [contra_apply, mem_fix.1 v.2 _ (inv_mem hh)]
    · have h1 : (contra π).dual h⁻¹ (Λ : Module.Dual ℂ (smoothPart π.dual)) = Λ :=
        congrArg Subtype.val (show contra (contra π) h⁻¹ Λ = Λ from hKs (inv_mem hh))
      conv_rhs => rw [← h1]
      show _ = (Λ : Module.Dual ℂ (smoothPart π.dual)) (contra π h⁻¹⁻¹ w)
      rw [inv_inv]
    · exact (hfix ⟨w, hw⟩).symm
def evEquiv
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsAdmissible π) : π.Equiv (contra (contra π)) :=
  (evMap π hπ.1).ofBijective (evMap_bijective hG hπ)
end GlobalTheory.ContraRefl
namespace GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
def contraMap {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ G X} {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ) :
    (contra τ).IntertwiningMap (contra σ) where
  toLinearMap :=
    { toFun := fun l => ⟨(l : Module.Dual ℂ Y) ∘ₗ f.toLinearMap,
        mem_smoothPart_of_nhds (Filter.mem_of_superset
          ((show IsOpen {g : G | τ.dual g (l : Module.Dual ℂ Y) = l} from l.2).mem_nhds
            (by show τ.dual 1 (l : Module.Dual ℂ Y) = l; rw [map_one, Module.End.one_apply]))
          fun g hg => by
            have hg' : τ.dual g (l : Module.Dual ℂ Y) = l := hg
            ext x
            show (l : Module.Dual ℂ Y) (f (σ g⁻¹ x)) = (l : Module.Dual ℂ Y) (f x)
            rw [f.isIntertwining]
            exact LinearMap.congr_fun hg' (f x))⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun x => ?_)
    show (l : Module.Dual ℂ Y) (τ g⁻¹ (f x)) = (l : Module.Dual ℂ Y) (f (σ g⁻¹ x))
    rw [f.isIntertwining]
def contraEquiv {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ G X} {τ : Representation ℂ G Y} (e : σ.Equiv τ) :
    (contra τ).Equiv (contra σ) :=
  (contraMap e.toIntertwiningMap).ofBijective (by
    refine Function.bijective_iff_has_inverse.2 ⟨contraMap e.symm.toIntertwiningMap, fun l => ?_, fun l => ?_⟩
    · refine Subtype.ext (LinearMap.ext fun y => ?_)
      show (l : Module.Dual ℂ Y) (e (e.symm y)) = (l : Module.Dual ℂ Y) y
      rw [e.apply_symm_apply]
    · refine Subtype.ext (LinearMap.ext fun x => ?_)
      show (l : Module.Dual ℂ X) (e.symm (e x)) = (l : Module.Dual ℂ X) x
      rw [e.symm_apply_apply])
end GlobalTheory.ContraRefl


