-- Prove2me | solution 1 for AutomorphicForm.hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/57d90175-6c95-535d-8fc6-bdfe3bce593a

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top

set_option autoImplicit false

open MeasureTheory Set Filter Function
open scoped ENNReal Pointwise Topology

noncomputable section

namespace R3TwGeo

section Equiv

variable {G : Type*} [Group G] (H : Subgroup G)

theorem out_inv_mul_mem (g : G) : ((g : G ⧸ H)).out⁻¹ * g ∈ H := by
  rw [← QuotientGroup.eq]
  exact QuotientGroup.out_eq' _

theorem mk_out_mul_coe (q : G ⧸ H) (h : H) : ((q.out * (h : G) : G) : G ⧸ H) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']

def quotientProdEquiv : (G ⧸ H) × H ≃ G where
  toFun p := p.1.out * (p.2 : G)
  invFun g := ((g : G ⧸ H), ⟨((g : G ⧸ H)).out⁻¹ * g, out_inv_mul_mem H g⟩)
  left_inv := by
    rintro ⟨q, h⟩
    have hq : ((q.out * (h : G) : G) : G ⧸ H) = q := mk_out_mul_coe H q h
    refine Prod.ext hq (Subtype.ext ?_)
    simp only [hq, inv_mul_cancel_left]
  right_inv g := by
    simp only [mul_inv_cancel_left]

@[scoped simp] theorem quotientProdEquiv_apply (p : (G ⧸ H) × H) :
    quotientProdEquiv H p = p.1.out * (p.2 : G) := rfl

end Equiv

section Invariance

variable {G α : Type*} [Group G] [MulAction G α] (H : Subgroup G)

theorem apply_inv_smul_of_invariant {X : Sort*} {f : α → X} (hinv : ∀ (h : H) (x : α), f (h • x) = f x)
    (h : H) (x : α) : f ((h : G)⁻¹ • x) = f x := by
  have := hinv h⁻¹ x
  rwa [Subgroup.smul_def, Subgroup.coe_inv] at this

theorem apply_out_mul_inv_smul {X : Sort*} {f : α → X} (hinv : ∀ (h : H) (x : α), f (h • x) = f x)
    (q : G ⧸ H) (h : H) (x : α) : f ((q.out * (h : G))⁻¹ • x) = f (q.out⁻¹ • x) := by
  rw [mul_inv_rev, mul_smul]
  exact apply_inv_smul_of_invariant H hinv h _

end Invariance

section LIntegral

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

omit [Countable G] [MeasurableConstSMul G α] in
theorem smulInvariantMeasure_subgroup (H : Subgroup G) : SMulInvariantMeasure H α μ :=
  ⟨fun h _s hs => SMulInvariantMeasure.measure_preimage_smul (h : G) hs⟩

omit [Countable G] in
theorem setLIntegral_smul_set (g : G) (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ x in g • s, f x ∂μ = ∫⁻ x in s, f (g • x) ∂μ := by
  rw [← image_smul]
  exact ((measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)
    f s).symm

theorem setLIntegral_eq_tsum_quotient (H : Subgroup G) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain H t μ)
    {f : α → ℝ≥0∞} (hinv : ∀ (h : H) (x : α), f (h • x) = f x) :
    ∫⁻ x in t, f x ∂μ = ∑' q : G ⧸ H, ∫⁻ x in s, f (q.out⁻¹ • x) ∂μ := by
  haveI := smulInvariantMeasure_subgroup (μ := μ) H
  calc ∫⁻ x in t, f x ∂μ
      = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := hs.setLIntegral_eq_tsum' f t
    _ = ∑' p : (G ⧸ H) × H,
          ∫⁻ x in (p.1.out * (p.2 : G)) • t ∩ s, f ((p.1.out * (p.2 : G))⁻¹ • x) ∂μ :=
        ((quotientProdEquiv H).tsum_eq (fun g => ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ)).symm
    _ = ∑' q : G ⧸ H, ∑' h : H,
          ∫⁻ x in q.out • ((h : G) • t) ∩ s, f (q.out⁻¹ • x) ∂μ := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun q => tsum_congr fun h => ?_
        simp_rw [apply_out_mul_inv_smul H hinv, mul_smul]
    _ = ∑' q : G ⧸ H, ∑' h : H, ∫⁻ x in (h : G) • t ∩ q.out⁻¹ • s, f x ∂μ := by
        refine tsum_congr fun q => tsum_congr fun h => ?_
        have hset : q.out • ((h : G) • t ∩ q.out⁻¹ • s) = q.out • ((h : G) • t) ∩ s := by
          rw [smul_set_inter, smul_inv_smul]
        rw [← hset, setLIntegral_smul_set]
        simp_rw [inv_smul_smul]
    _ = ∑' q : G ⧸ H, ∫⁻ x in q.out⁻¹ • s, f x ∂μ := by
        refine tsum_congr fun q => ?_
        rw [ht.setLIntegral_eq_tsum f (q.out⁻¹ • s)]
        refine tsum_congr fun h => ?_
        rw [inter_comm]
        rfl
    _ = ∑' q : G ⧸ H, ∫⁻ x in s, f (q.out⁻¹ • x) ∂μ :=
        tsum_congr fun q => setLIntegral_smul_set _ _ _

theorem setLIntegral_eq_setLIntegral_tsum_quotient (H : Subgroup G) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain H t μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hinv : ∀ (h : H) (x : α), f (h • x) = f x) :
    ∫⁻ x in t, f x ∂μ = ∫⁻ x in s, ∑' q : G ⧸ H, f (q.out⁻¹ • x) ∂μ := by
  haveI : Countable (G ⧸ H) := (QuotientGroup.mk_surjective (s := H)).countable
  rw [setLIntegral_eq_tsum_quotient H hs ht hinv, lintegral_tsum]
  exact fun q =>
    ((hf.comp_quasiMeasurePreserving (measurePreserving_smul _ μ).quasiMeasurePreserving)).restrict

end LIntegral

section Measurability

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

omit [Countable G] [MeasurableSpace α] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] in
theorem subgroup_smul_set (H : Subgroup G) (h : H) (t : Set α) : (h : G) • t = h • t := rfl

theorem aestronglyMeasurable_of_invariant (H : Subgroup G) {t : Set α}
    (ht : IsFundamentalDomain H t μ) {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] {f : α → β}
    (hf : AEStronglyMeasurable f (μ.restrict t)) (hinv : ∀ (h : H) (x : α), f (h • x) = f x) :
    AEStronglyMeasurable f μ := by
  haveI := smulInvariantMeasure_subgroup (μ := μ) H
  rw [← ht.sum_restrict]
  refine AEStronglyMeasurable.sum_measure fun h => ?_
  have he : MeasurableEmbedding ((h : H) • · : α → α) := measurableEmbedding_const_smul _
  rw [← image_smul, ← ((measurePreserving_smul h μ).restrict_image_emb he _).aestronglyMeasurable_comp_iff he]
  simpa only [Function.comp_def, hinv] using hf

end Measurability

section Bochner

variable {G α E : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Countable G] in
theorem setIntegral_smul_set (g : G) (f : α → E) (s : Set α) :
    ∫ x in g • s, f x ∂μ = ∫ x in s, f (g • x) ∂μ := by
  rw [← image_smul]
  exact (measurePreserving_smul g μ).setIntegral_image_emb (measurableEmbedding_const_smul g) f s

omit [NormedSpace ℝ E] in

theorem integrableOn_smul_of_invariant (H : Subgroup G) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain H t μ)
    {f : α → E} (hft : IntegrableOn f t μ) (hinv : ∀ (h : H) (x : α), f (h • x) = f x) (g : G) :
    IntegrableOn f (g • s) μ := by
  haveI : Countable (G ⧸ H) := (QuotientGroup.mk_surjective (s := H)).countable
  refine ⟨(aestronglyMeasurable_of_invariant H ht hft.1 hinv).restrict, ?_⟩
  have hinv' : ∀ (h : H) (x : α), (‖f (h • x)‖ₑ) = ‖f x‖ₑ := fun h x => by rw [hinv]
  obtain ⟨⟨q, h⟩, hqh⟩ := (quotientProdEquiv H).surjective g⁻¹
  have hg : g = (h : G)⁻¹ * q.out⁻¹ := by
    rw [← inv_inv g, ← hqh, quotientProdEquiv_apply, mul_inv_rev]
  calc ∫⁻ x in g • s, ‖f x‖ₑ ∂μ
      = ∫⁻ x in q.out⁻¹ • s, ‖f ((h : G)⁻¹ • x)‖ₑ ∂μ := by
        rw [hg, mul_smul, setLIntegral_smul_set]
    _ = ∫⁻ x in s, ‖f (q.out⁻¹ • x)‖ₑ ∂μ := by
        simp_rw [apply_inv_smul_of_invariant H hinv]
        exact setLIntegral_smul_set _ _ _
    _ ≤ ∑' q' : G ⧸ H, ∫⁻ x in s, ‖f (q'.out⁻¹ • x)‖ₑ ∂μ := ENNReal.le_tsum q
    _ = ∫⁻ x in t, ‖f x‖ₑ ∂μ :=
        (setLIntegral_eq_tsum_quotient H hs ht (f := fun x => ‖f x‖ₑ) hinv').symm
    _ < ⊤ := hft.2

theorem hasSum_setIntegral_quotient (H : Subgroup G) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain H t μ)
    {f : α → E} (hft : IntegrableOn f t μ) (hinv : ∀ (h : H) (x : α), f (h • x) = f x) :
    HasSum (fun q : G ⧸ H => ∫ x in s, f (q.out⁻¹ • x) ∂μ) (∫ x in t, f x ∂μ) := by
  haveI := smulInvariantMeasure_subgroup (μ := μ) H
  have h1 : HasSum (fun g : G => ∫ x in g • s ∩ t, f x ∂μ) (∫ x in t, f x ∂μ) := by
    have hsum : (Measure.sum fun g : G => (μ.restrict t).restrict (g • s)) = μ.restrict t :=
      hs.sum_restrict_of_ac Measure.restrict_le_self.absolutelyContinuous
    have key := hasSum_integral_measure (μ := fun g : G => (μ.restrict t).restrict (g • s)) (f := f)
      (by rw [hsum]; exact hft)
    rw [hsum] at key
    simpa only [hs.restrict_restrict] using key
  have h2 : HasSum (fun p : (G ⧸ H) × H => ∫ x in (p.1.out * (p.2 : G))⁻¹ • s ∩ t, f x ∂μ)
      (∫ x in t, f x ∂μ) :=
    (((quotientProdEquiv H).trans (Equiv.inv G)).hasSum_iff
      (f := fun g : G => ∫ x in g • s ∩ t, f x ∂μ)).2 h1
  refine h2.prod_fiberwise fun q => ?_
  have h3 : ∀ h : H, ∫ x in (q.out * (h : G))⁻¹ • s ∩ t, f x ∂μ =
      ∫ x in h • t ∩ q.out⁻¹ • s, f x ∂μ := by
    intro h
    have hset : (q.out * (h : G))⁻¹ • s ∩ t = (h : G)⁻¹ • (h • t ∩ q.out⁻¹ • s) := by
      rw [Set.inter_comm ((q.out * (h : G))⁻¹ • s) t, mul_inv_rev, mul_smul, smul_set_inter,
        ← subgroup_smul_set, inv_smul_smul]
    rw [hset, setIntegral_smul_set]
    simp_rw [apply_inv_smul_of_invariant H hinv]
  simp_rw [h3]
  have hint : IntegrableOn f (q.out⁻¹ • s) μ := integrableOn_smul_of_invariant H hs ht hft hinv _
  have h4 : HasSum (fun h : H => ∫ x in h • t ∩ q.out⁻¹ • s, f x ∂μ) (∫ x in q.out⁻¹ • s, f x ∂μ) := by
    have hsum : (Measure.sum fun h : H => (μ.restrict (q.out⁻¹ • s)).restrict (h • t)) =
        μ.restrict (q.out⁻¹ • s) :=
      ht.sum_restrict_of_ac Measure.restrict_le_self.absolutelyContinuous
    have key := hasSum_integral_measure
      (μ := fun h : H => (μ.restrict (q.out⁻¹ • s)).restrict (h • t)) (f := f)
      (by rw [hsum]; exact hint)
    rw [hsum] at key
    simpa only [ht.restrict_restrict] using key
  rwa [setIntegral_smul_set] at h4

end Bochner

section Orbit

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

theorem invariant_of_equivariant {X : Sort*} (k : β → α → X)
    (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x)) (b₀ : β) :
    ∀ (h : MulAction.stabilizer G b₀) (x : α), k b₀ (h • x) = k b₀ x := by
  intro h x
  have hb : (h : G)⁻¹ • b₀ = b₀ := inv_smul_eq_iff.2 (MulAction.mem_stabilizer_iff.1 h.2).symm
  have := hk (h : G)⁻¹ b₀ x
  rw [hb, inv_inv] at this
  exact this.symm

theorem tsum_quotient_stabilizer_eq_tsum_orbit {X : Type*} [AddCommMonoid X] [TopologicalSpace X]
    (k : β → α → X) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x)) (b₀ : β) (x : α) :
    ∑' q : G ⧸ MulAction.stabilizer G b₀, k b₀ (q.out⁻¹ • x) =
      ∑' b : MulAction.orbit G b₀, k b x := by
  rw [← (MulAction.orbitEquivQuotientStabilizer G b₀).symm.tsum_eq
    (fun b : MulAction.orbit G b₀ => k b x)]
  refine tsum_congr fun q => ?_
  have hq : ((MulAction.orbitEquivQuotientStabilizer G b₀).symm q : β) = q.out • b₀ := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact MulAction.orbitEquivQuotientStabilizer_symm_apply G b₀ q.out
  rw [hq, hk]

theorem hasSum_orbit_iff {X Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y]
    (k : β → α → X) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x)) (b₀ : β)
    (I : (α → X) → Y) (a : Y) :
    HasSum (fun b : MulAction.orbit G b₀ => I (k b)) a ↔
      HasSum (fun q : G ⧸ MulAction.stabilizer G b₀ => I (fun x => k b₀ (q.out⁻¹ • x))) a := by
  rw [← (MulAction.orbitEquivQuotientStabilizer G b₀).symm.hasSum_iff]
  have hq : ∀ q : G ⧸ MulAction.stabilizer G b₀,
      ((MulAction.orbitEquivQuotientStabilizer G b₀).symm q : β) = q.out • b₀ := fun q => by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact MulAction.orbitEquivQuotientStabilizer_symm_apply G b₀ q.out
  have hfun : ((fun b : MulAction.orbit G b₀ => I (k b)) ∘
      (MulAction.orbitEquivQuotientStabilizer G b₀).symm) =
      fun q => I (fun x => k b₀ (q.out⁻¹ • x)) := by
    funext q
    simp only [Function.comp_apply, hq q]
    congr 1
    funext x
    exact hk _ _ _
  rw [hfun]

variable [Countable G] [MeasurableSpace α] [MeasurableConstSMul G α] {μ : Measure α}
  [SMulInvariantMeasure G α μ]

theorem setLIntegral_stabilizer_eq_setLIntegral_tsum_orbit (b₀ : β) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain (MulAction.stabilizer G b₀) t μ)
    (k : β → α → ℝ≥0∞) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x))
    (hmeas : AEMeasurable (k b₀) μ) :
    ∫⁻ x in t, k b₀ x ∂μ = ∫⁻ x in s, ∑' b : MulAction.orbit G b₀, k b x ∂μ := by
  have hinv := invariant_of_equivariant k hk b₀
  rw [setLIntegral_eq_setLIntegral_tsum_quotient (MulAction.stabilizer G b₀) hs ht hmeas hinv]
  simp_rw [tsum_quotient_stabilizer_eq_tsum_orbit k hk b₀]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasSum_setIntegral_orbit (b₀ : β) {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain (MulAction.stabilizer G b₀) t μ)
    (k : β → α → E) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x))
    (hint : IntegrableOn (k b₀) t μ) :
    HasSum (fun b : MulAction.orbit G b₀ => ∫ x in s, k b x ∂μ) (∫ x in t, k b₀ x ∂μ) := by
  have hinv := invariant_of_equivariant k hk b₀
  rw [hasSum_orbit_iff k hk b₀ (fun F => ∫ x in s, F x ∂μ)]
  exact hasSum_setIntegral_quotient (MulAction.stabilizer G b₀) hs ht hint hinv

end Orbit

section Family

variable {G α β : Type*} [Group G] [Countable G] [MulAction G α] [MulAction G β] [Countable β]
  [MeasurableSpace α] [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {Q : Type*} [Countable Q]

omit [Countable G] [MulAction G α] [Countable β] [MeasurableSpace α] [MeasurableConstSMul G α]
  [Countable Q] in

theorem tsum_iUnion_enorm_eq_tsum_tsum_orbit {E : Type*} [NormedAddCommGroup E]
    (rep : Q → β) (hdisj : Pairwise (Disjoint on fun q => MulAction.orbit G (rep q)))
    (k : β → α → E) (x : α) :
    ∑' b : ⋃ q, MulAction.orbit G (rep q), ‖k b x‖ₑ =
      ∑' q, ∑' b : MulAction.orbit G (rep q), ‖k b x‖ₑ := by
  rw [← (Set.unionEqSigmaOfDisjoint hdisj).symm.tsum_eq
    (fun b : ⋃ q, MulAction.orbit G (rep q) => ‖k b x‖ₑ), ENNReal.tsum_sigma']
  rfl

omit [Countable G] [MulAction G α] [MeasurableConstSMul G α] [Countable Q] in
theorem aemeasurable_tsum_orbit_enorm {E : Type*} [NormedAddCommGroup E] (b₀ : β) (k : β → α → E)
    (hkm : ∀ b, AEStronglyMeasurable (k b) μ) (ν : Measure α) (hν : ν ≪ μ) :
    AEMeasurable (fun x => ∑' b : MulAction.orbit G b₀, ‖k b x‖ₑ) ν :=
  AEMeasurable.tsum fun b => ((hkm b).mono_ac hν).enorm

theorem tsum_setLIntegral_stabilizer_enorm_eq {E : Type*} [NormedAddCommGroup E]
    {s : Set α} (hs : IsFundamentalDomain G s μ)
    (rep : Q → β) (hdisj : Pairwise (Disjoint on fun q => MulAction.orbit G (rep q)))
    (t : Q → Set α) (ht : ∀ q, IsFundamentalDomain (MulAction.stabilizer G (rep q)) (t q) μ)
    (k : β → α → E) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x))
    (hkm : ∀ b, AEStronglyMeasurable (k b) μ) :
    ∑' q, ∫⁻ x in t q, ‖k (rep q) x‖ₑ ∂μ =
      ∫⁻ x in s, ∑' b : ⋃ q, MulAction.orbit G (rep q), ‖k b x‖ₑ ∂μ := by
  have hk' : ∀ (g : G) (b : β) (x : α), (‖k (g • b) x‖ₑ) = ‖k b (g⁻¹ • x)‖ₑ := fun g b x => by
    rw [hk]
  have h1 : ∀ q, ∫⁻ x in t q, ‖k (rep q) x‖ₑ ∂μ =
      ∫⁻ x in s, ∑' b : MulAction.orbit G (rep q), ‖k b x‖ₑ ∂μ := fun q =>
    setLIntegral_stabilizer_eq_setLIntegral_tsum_orbit (rep q) hs (ht q) (fun b x => ‖k b x‖ₑ) hk'
      (hkm (rep q)).enorm
  simp_rw [h1, tsum_iUnion_enorm_eq_tsum_tsum_orbit rep hdisj k]
  rw [lintegral_tsum]
  exact fun q => aemeasurable_tsum_orbit_enorm (rep q) k hkm _
    Measure.restrict_le_self.absolutelyContinuous

theorem integrableOn_of_lintegral_tsum_lt_top {E : Type*} [NormedAddCommGroup E]
    {s : Set α} (hs : IsFundamentalDomain G s μ)
    (rep : Q → β) (hdisj : Pairwise (Disjoint on fun q => MulAction.orbit G (rep q)))
    (t : Q → Set α) (ht : ∀ q, IsFundamentalDomain (MulAction.stabilizer G (rep q)) (t q) μ)
    (k : β → α → E) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x))
    (hkm : ∀ b, AEStronglyMeasurable (k b) μ)
    (hfin : ∫⁻ x in s, ∑' b : ⋃ q, MulAction.orbit G (rep q), ‖k b x‖ₑ ∂μ < ⊤) (q : Q) :
    IntegrableOn (k (rep q)) (t q) μ := by
  refine ⟨(hkm (rep q)).restrict, ?_⟩
  calc ∫⁻ x in t q, ‖k (rep q) x‖ₑ ∂μ
      ≤ ∑' q', ∫⁻ x in t q', ‖k (rep q') x‖ₑ ∂μ := ENNReal.le_tsum q
    _ = ∫⁻ x in s, ∑' b : ⋃ q, MulAction.orbit G (rep q), ‖k b x‖ₑ ∂μ :=
        tsum_setLIntegral_stabilizer_enorm_eq hs rep hdisj t ht k hk hkm
    _ < ⊤ := hfin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasSum_setIntegral_stabilizer_family
    {s : Set α} (hs : IsFundamentalDomain G s μ)
    (rep : Q → β) (hdisj : Pairwise (Disjoint on fun q => MulAction.orbit G (rep q)))
    (t : Q → Set α) (ht : ∀ q, IsFundamentalDomain (MulAction.stabilizer G (rep q)) (t q) μ)
    (k : β → α → E) (hk : ∀ (g : G) (b : β) (x : α), k (g • b) x = k b (g⁻¹ • x))
    (hkm : ∀ b, AEStronglyMeasurable (k b) μ)
    (hfin : ∫⁻ x in s, ∑' b : ⋃ q, MulAction.orbit G (rep q), ‖k b x‖ₑ ∂μ < ⊤) :
    HasSum (fun q => ∫ x in t q, k (rep q) x ∂μ)
      (∫ x in s, ∑' b : ⋃ q, MulAction.orbit G (rep q), k b x ∂μ) := by
  set U : Set β := ⋃ q, MulAction.orbit G (rep q) with hU
  by_cases hE : CompleteSpace E
  swap
  · simp [integral, hE, hasSum_zero]
  haveI : Countable U := inferInstance

  have hmeasU : ∀ b : U, AEStronglyMeasurable (k b) (μ.restrict s) := fun b => (hkm b).restrict
  have hmeasE : AEMeasurable (fun x => ∑' b : U, ‖k b x‖ₑ) (μ.restrict s) :=
    AEMeasurable.tsum fun b => (hmeasU b).enorm
  have hae : ∀ᵐ x ∂μ.restrict s, ∑' b : U, ‖k b x‖ₑ < ⊤ := ae_lt_top' hmeasE hfin.ne
  have hsumm : ∀ᵐ x ∂μ.restrict s, Summable fun b : U => ‖k b x‖ := by
    refine hae.mono fun x hx => ?_
    have h1 : Summable fun b : U => ‖k b x‖₊ := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa only [enorm_eq_nnnorm] using hx.ne
    simpa only [coe_nnnorm] using NNReal.summable_coe.2 h1
  have H1 : HasSum (fun b : U => ∫ x in s, k b x ∂μ) (∫ x in s, ∑' b : U, k b x ∂μ) := by
    refine hasSum_integral_of_dominated_convergence (fun (b : U) x => ‖k b x‖) hmeasU
      (fun b => Eventually.of_forall fun x => le_rfl) hsumm ?_ ?_
    · refine ⟨?_, ?_⟩
      · have : (fun x => ∑' b : U, ‖k b x‖) =ᵐ[μ.restrict s] fun x => (∑' b : U, ‖k b x‖ₑ).toReal := by
          refine hsumm.mono fun x hx => ?_
          have hx' : Summable fun b : U => ‖k b x‖₊ := by
            simpa only [← NNReal.summable_coe, coe_nnnorm] using hx
          simp only [enorm_eq_nnnorm]
          rw [← ENNReal.coe_tsum hx', ENNReal.coe_toReal, NNReal.coe_tsum]
          simp only [coe_nnnorm]
        exact (hmeasE.ennreal_toReal.aestronglyMeasurable).congr this.symm
      · dsimp only [HasFiniteIntegral]
        refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
        refine hsumm.mono fun x hx => le_of_eq ?_
        have hx' : Summable fun b : U => ‖k b x‖₊ := by
          simpa only [← NNReal.summable_coe, coe_nnnorm] using hx
        have h2 : (∑' b : U, ‖k b x‖) = ((∑' b : U, ‖k b x‖₊ : NNReal) : ℝ) := by
          simp only [NNReal.coe_tsum, coe_nnnorm]
        rw [Real.enorm_eq_ofReal (tsum_nonneg fun _ => norm_nonneg _), h2, ENNReal.ofReal_coe_nnreal,
          ENNReal.coe_tsum hx']
        simp only [enorm_eq_nnnorm]
    · exact hsumm.mono fun x hx => hx.of_norm.hasSum

  have H2 : HasSum (fun p : Σ q, MulAction.orbit G (rep q) => ∫ x in s, k p.2 x ∂μ)
      (∫ x in s, ∑' b : U, k b x ∂μ) := by
    have := ((Set.unionEqSigmaOfDisjoint hdisj).symm.hasSum_iff
      (f := fun b : U => ∫ x in s, k b x ∂μ)).2 H1
    convert this using 2
    rfl

  refine H2.sigma fun q => ?_
  exact hasSum_setIntegral_orbit (rep q) hs (ht q) k hk
    (integrableOn_of_lintegral_tsum_lt_top hs rep hdisj t ht k hk hkm hfin q)

end Family

section TwistAction

variable {L : Type*} [Field L]

set_option linter.unusedVariables false in

def SigmaTwist (σ : L →+* L) : Type _ := Matrix.GeneralLinearGroup (Fin 2) L

variable (σ : L →+* L)

def SigmaTwist.mk : Matrix.GeneralLinearGroup (Fin 2) L ≃ SigmaTwist σ := Equiv.refl _

scoped instance SigmaTwist.instMulAction : MulAction (Matrix.GeneralLinearGroup (Fin 2) L) (SigmaTwist σ) where
  smul g δ := SigmaTwist.mk σ (AutomorphicForm.sigmaConj σ g ((SigmaTwist.mk σ).symm δ))
  one_smul δ := by
    show SigmaTwist.mk σ (AutomorphicForm.sigmaConj σ 1 ((SigmaTwist.mk σ).symm δ)) = δ
    rw [AutomorphicForm.sigmaConj_one_left]
    rfl
  mul_smul g h δ := by
    show SigmaTwist.mk σ (AutomorphicForm.sigmaConj σ (g * h) ((SigmaTwist.mk σ).symm δ)) =
      SigmaTwist.mk σ (AutomorphicForm.sigmaConj σ g (AutomorphicForm.sigmaConj σ h
        ((SigmaTwist.mk σ).symm δ)))
    congr 1
    simp only [AutomorphicForm.sigmaConj, map_mul, _root_.mul_inv_rev]
    group

p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist"
scoped instance SigmaTwist.instCountable [Countable L] : Countable (SigmaTwist σ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : Matrix.GeneralLinearGroup (Fin 2) L → _))
    Units.val_injective

p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist"
theorem SigmaTwist.smul_mk (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    g • SigmaTwist.mk σ δ = SigmaTwist.mk σ (g * δ * (Matrix.GeneralLinearGroup.map σ g)⁻¹) := rfl

theorem SigmaTwist.mk_symm_smul (g : Matrix.GeneralLinearGroup (Fin 2) L) (b : SigmaTwist σ) :
    (SigmaTwist.mk σ).symm (g • b) =
      g * (SigmaTwist.mk σ).symm b * (Matrix.GeneralLinearGroup.map σ g)⁻¹ := rfl

theorem SigmaTwist.stabilizer_mk (δ₀ : Matrix.GeneralLinearGroup (Fin 2) L) :
    MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) L) (SigmaTwist.mk σ δ₀) =
      AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map σ) δ₀ := by
  ext t
  rw [MulAction.mem_stabilizer_iff, AutomorphicForm.mem_sigmaCentralizer_iff, SigmaTwist.smul_mk]
  exact (SigmaTwist.mk σ).apply_eq_iff_eq

theorem SigmaTwist.mem_orbit_mk_iff (δ₀ δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    SigmaTwist.mk σ δ ∈ MulAction.orbit (Matrix.GeneralLinearGroup (Fin 2) L) (SigmaTwist.mk σ δ₀) ↔
      AutomorphicForm.IsSigmaConj σ δ₀ δ := by
  rw [MulAction.mem_orbit_iff]
  refine exists_congr fun g => ?_
  rw [SigmaTwist.smul_mk, eq_comm]
  exact (SigmaTwist.mk σ).apply_eq_iff_eq

end TwistAction
p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist"

section GlobalAction

variable (R L : Type*) [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

@[reducible] def globalAction :
    MulAction (Matrix.GeneralLinearGroup (Fin 2) L) (AutomorphicForm.AdelicGL2 R L) :=
  MulAction.compHom _ (AutomorphicForm.globalPoints R L)

attribute [local instance] globalAction

theorem globalAction_smul_def (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AutomorphicForm.AdelicGL2 R L) :
    γ • x = AutomorphicForm.globalPoints R L γ * x := rfl

theorem measurableConstSMul_globalAction [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)]
    [MeasurableMul (AutomorphicForm.AdelicGL2 R L)] :
    MeasurableConstSMul (Matrix.GeneralLinearGroup (Fin 2) L) (AutomorphicForm.AdelicGL2 R L) :=
  ⟨fun γ => measurable_const_mul (AutomorphicForm.globalPoints R L γ)⟩

theorem globalPoints_injective [NumberField L] : Function.Injective (AutomorphicForm.globalPoints R L) := by
  intro γ γ' h
  refine Matrix.GeneralLinearGroup.ext fun i j => NumberField.AdeleRing.algebraMap_injective R L ?_
  have := congrArg (fun g : AutomorphicForm.AdelicGL2 R L =>
    (g : Matrix (Fin 2) (Fin 2) (NumberField.AdeleRing R L)) i j) h
  simpa only [AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply] using this

theorem isFundamentalDomain_globalAction [NumberField L]
    [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)]
    (μ : Measure (AutomorphicForm.AdelicGL2 R L)) (Φ : Set (AutomorphicForm.AdelicGL2 R L))
    (h : IsFundamentalDomain (AutomorphicForm.globalPoints R L).range Φ μ) :
    IsFundamentalDomain (Matrix.GeneralLinearGroup (Fin 2) L) Φ μ := by
  have hinj := globalPoints_injective R L
  refine h.preimage_of_equiv (f := id) (Measure.QuasiMeasurePreserving.id μ)
    (e := fun p : (AutomorphicForm.globalPoints R L).range => (MonoidHom.ofInjective hinj).symm p)
    (MonoidHom.ofInjective hinj).symm.bijective fun p x => ?_
  show AutomorphicForm.globalPoints R L ((MonoidHom.ofInjective hinj).symm p) * x =
    (p : AutomorphicForm.AdelicGL2 R L) * x
  rw [← MonoidHom.ofInjective_apply hinj, MulEquiv.apply_symm_apply]

theorem smulInvariantMeasure_globalAction [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)]
    (μ : Measure (AutomorphicForm.AdelicGL2 R L))
    [SMulInvariantMeasure (AutomorphicForm.globalPoints R L).range (AutomorphicForm.AdelicGL2 R L) μ] :
    SMulInvariantMeasure (Matrix.GeneralLinearGroup (Fin 2) L) (AutomorphicForm.AdelicGL2 R L) μ :=
  ⟨fun γ _s hs => SMulInvariantMeasure.measure_preimage_smul
    (⟨AutomorphicForm.globalPoints R L γ, γ, rfl⟩ : (AutomorphicForm.globalPoints R L).range) hs⟩

theorem isFundamentalDomain_subgroup_of_map [NumberField L] [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)]
    (μ : Measure (AutomorphicForm.AdelicGL2 R L)) (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) L))
    (Ψ : Set (AutomorphicForm.AdelicGL2 R L))
    (hΨ : IsFundamentalDomain (H.map (AutomorphicForm.globalPoints R L)) Ψ μ) :
    IsFundamentalDomain H Ψ μ := by
  have hinj := globalPoints_injective R L
  refine hΨ.preimage_of_equiv (f := id) (Measure.QuasiMeasurePreserving.id μ)
    (e := fun p : H.map (AutomorphicForm.globalPoints R L) => (H.equivMapOfInjective _ hinj).symm p)
    (H.equivMapOfInjective _ hinj).symm.bijective fun p x => ?_
  show AutomorphicForm.globalPoints R L
      (((H.equivMapOfInjective _ hinj).symm p : H) : Matrix.GeneralLinearGroup (Fin 2) L) * x =
    ((p : AutomorphicForm.AdelicGL2 R L)) * x
  congr 1
  conv_rhs => rw [← MulEquiv.apply_symm_apply (H.equivMapOfInjective _ hinj) p]
  exact (Subgroup.coe_equivMapOfInjective_apply H _ hinj _).symm

theorem twistedIntegrand_equivariant {X : Type*} (σ : L →+* L)
    (σA : AutomorphicForm.AdelicGL2 R L →* AutomorphicForm.AdelicGL2 R L)
    (hσA : ∀ γ : Matrix.GeneralLinearGroup (Fin 2) L,
      σA (AutomorphicForm.globalPoints R L γ) =
        AutomorphicForm.globalPoints R L (Matrix.GeneralLinearGroup.map σ γ))
    (F : AutomorphicForm.AdelicGL2 R L → X) :
    ∀ (g : Matrix.GeneralLinearGroup (Fin 2) L) (b : SigmaTwist σ) (x : AutomorphicForm.AdelicGL2 R L),
      F (x⁻¹ * AutomorphicForm.globalPoints R L ((SigmaTwist.mk σ).symm (g • b)) * σA x) =
        F ((g⁻¹ • x)⁻¹ * AutomorphicForm.globalPoints R L ((SigmaTwist.mk σ).symm b) * σA (g⁻¹ • x)) := by
  intro g b x
  congr 1
  simp only [SigmaTwist.mk_symm_smul, globalAction_smul_def, map_mul, map_inv, hσA,
    _root_.mul_inv_rev, _root_.inv_inv, mul_assoc]

end GlobalAction
p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist"

section Classes

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

theorem mem_orbit_mk_rep_iff {c : LT.TwistedNorm.SigmaConjClasses σ} {r : GL (Fin 2) L}
    (hr : LT.TwistedNorm.SigmaConjClasses.mk σ r = c) (δ : GL (Fin 2) L) :
    SigmaTwist.mk (σ : L →+* L) δ ∈
        MulAction.orbit (GL (Fin 2) L) (SigmaTwist.mk (σ : L →+* L) r) ↔
      LT.TwistedNorm.SigmaConjClasses.mk σ δ = c := by
  rw [SigmaTwist.mem_orbit_mk_iff, ← LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff, hr, eq_comm]

end Classes
p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist"

end R3TwGeo
p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo"

end
p2m_reactivate "P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo.SigmaTwist P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top.R3TwGeo"

open MeasureTheory R3TwGeo in

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (R : Type) [CommRing R] [IsDedekindDomain R] [Algebra R L] [IsFractionRing R L]
    [MeasurableSpace (AutomorphicForm.AdelicGL2 R L)] [BorelSpace (AutomorphicForm.AdelicGL2 R L)]
    (σ : L ≃ₐ[K] L)
    (σA : AutomorphicForm.AdelicGL2 R L →* AutomorphicForm.AdelicGL2 R L) (hσAc : Continuous σA)
    (hσA : ∀ γ : GL (Fin 2) L,
      σA (AutomorphicForm.globalPoints R L γ) =
        AutomorphicForm.globalPoints R L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ))
    (μ : MeasureTheory.Measure (AutomorphicForm.AdelicGL2 R L))
    [MeasureTheory.SMulInvariantMeasure (AutomorphicForm.globalPoints R L).range
      (AutomorphicForm.AdelicGL2 R L) μ]
    (Φ : Set (AutomorphicForm.AdelicGL2 R L))
    (hΦ : MeasureTheory.IsFundamentalDomain (AutomorphicForm.globalPoints R L).range Φ μ)
    (C : Set (LT.TwistedNorm.SigmaConjClasses σ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c ∈ C, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 R L))
    (hΨ : ∀ c ∈ C, MeasureTheory.IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
        (AutomorphicForm.globalPoints R L)) (Ψ c) μ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutomorphicForm.AdelicGL2 R L → E) (hF : MeasureTheory.StronglyMeasurable F)
    (habs : ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
        ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ < ⊤) :
    (∑' c : C, ∫⁻ x in Ψ c, ‖F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)‖ₑ ∂μ =
        ∫⁻ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ ∂μ) ∧
    (∀ c ∈ C, MeasureTheory.IntegrableOn
        (fun x => F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x)) (Ψ c) μ) ∧
      HasSum (fun c : C => ∫ x in Ψ c, F (x⁻¹ * AutomorphicForm.globalPoints R L (rep c) * σA x) ∂μ)
        (∫ x in Φ, ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
          F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x) ∂μ) := by
  letI := globalAction R L
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (GL (Fin 2) L) := SigmaTwist.instCountable (RingHom.id L)
  haveI := measurableConstSMul_globalAction R L
  haveI := smulInvariantMeasure_globalAction R L μ
  set σ' : L →+* L := (σ : L →+* L) with hσ'

  have hΦ' : IsFundamentalDomain (GL (Fin 2) L) Φ μ := isFundamentalDomain_globalAction R L μ Φ hΦ
  set rep' : C → SigmaTwist σ' := fun q => SigmaTwist.mk σ' (rep q) with hrep'
  have hmem : ∀ (q : C) (δ : GL (Fin 2) L),
      SigmaTwist.mk σ' δ ∈ MulAction.orbit (GL (Fin 2) L) (rep' q) ↔
        LT.TwistedNorm.SigmaConjClasses.mk σ δ = q := fun q δ =>
    mem_orbit_mk_rep_iff σ (hrep q q.2) δ
  have hdisj : Pairwise (Function.onFun Disjoint fun q => MulAction.orbit (GL (Fin 2) L) (rep' q)) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 fun b hb hb' => hqq' (Subtype.ext ?_)
    obtain ⟨δ, rfl⟩ := (SigmaTwist.mk σ').surjective b
    rw [← (hmem q δ).1 hb, ← (hmem q' δ).1 hb']
  have ht : ∀ q : C, IsFundamentalDomain (MulAction.stabilizer (GL (Fin 2) L) (rep' q)) (Ψ q) μ := by
    intro q
    rw [SigmaTwist.stabilizer_mk]
    exact isFundamentalDomain_subgroup_of_map R L μ _ _ (hΨ q q.2)

  set k : SigmaTwist σ' → AutomorphicForm.AdelicGL2 R L → E := fun b x =>
    F (x⁻¹ * AutomorphicForm.globalPoints R L ((SigmaTwist.mk σ').symm b) * σA x) with hk
  have hkeq : ∀ (g : GL (Fin 2) L) (b : SigmaTwist σ') (x : AutomorphicForm.AdelicGL2 R L),
      k (g • b) x = k b (g⁻¹ • x) := twistedIntegrand_equivariant R L σ' σA hσA F
  have hkm : ∀ b, AEStronglyMeasurable (k b) μ := fun b =>
    (hF.comp_measurable (((continuous_id.inv).mul continuous_const).mul hσAc).measurable).aestronglyMeasurable

  set U : Set (SigmaTwist σ') := ⋃ q : C, MulAction.orbit (GL (Fin 2) L) (rep' q) with hU
  have hmemU : ∀ δ : GL (Fin 2) L, SigmaTwist.mk σ' δ ∈ U ↔ LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C := by
    intro δ
    simp only [hU, Set.mem_iUnion, hmem]
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  let e : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C} ≃ U :=
    (SigmaTwist.mk σ').subtypeEquiv fun δ => (hmemU δ).symm
  have he : ∀ (x : AutomorphicForm.AdelicGL2 R L)
      (δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C}),
      k (e δ) x = F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x) := fun _ _ => rfl
  have htsumE : ∀ x, ∑' b : U, ‖k b x‖ₑ =
      ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
        ‖F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x)‖ₑ := fun x => by
    rw [← e.tsum_eq]; rfl
  have htsum : ∀ x, ∑' b : U, k b x =
      ∑' δ : {δ : GL (Fin 2) L // LT.TwistedNorm.SigmaConjClasses.mk σ δ ∈ C},
        F (x⁻¹ * AutomorphicForm.globalPoints R L δ * σA x) := fun x => by
    rw [← e.tsum_eq]; rfl
  haveI : Countable (LT.TwistedNorm.SigmaConjClasses σ) :=
    (LT.TwistedNorm.SigmaConjClasses.mk_surjective σ).countable
  have hfin : ∫⁻ x in Φ, ∑' b : U, ‖k b x‖ₑ ∂μ < ⊤ := by
    simp_rw [htsumE]; exact habs
  refine ⟨?_, fun c hc => ?_, ?_⟩
  · have key : ∑' q : C, ∫⁻ x in Ψ q, ‖k (rep' q) x‖ₑ ∂μ = ∫⁻ x in Φ, ∑' b : U, ‖k b x‖ₑ ∂μ :=
      tsum_setLIntegral_stabilizer_enorm_eq hΦ' rep' hdisj (fun q => Ψ q) ht k hkeq hkm
    simp_rw [htsumE] at key
    exact key
  · exact integrableOn_of_lintegral_tsum_lt_top hΦ' rep' hdisj (fun q => Ψ q) ht k hkeq hkm hfin ⟨c, hc⟩
  · have key : HasSum (fun q : C => ∫ x in Ψ q, k (rep' q) x ∂μ) (∫ x in Φ, ∑' b : U, k b x ∂μ) :=
      hasSum_setIntegral_stabilizer_family hΦ' rep' hdisj (fun q => Ψ q) ht k hkeq hkm hfin
    simp_rw [htsum] at key
    exact key

end S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top
end P2MW
export P2MW.S_AutomorphicForm_hasSum_setIntegral_sigmaCentralizer_of_lintegral_tsum_enorm_lt_top (solution)
