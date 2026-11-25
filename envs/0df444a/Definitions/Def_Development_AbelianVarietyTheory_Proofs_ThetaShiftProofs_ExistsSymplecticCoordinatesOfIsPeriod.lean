-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSymplecticCoordinatesOfIsPeriod
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSymplecticCoordinatesOfIsPeriod
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:18:39.02435+00:00
-- url     : https://prove2.me/theorems/78b0cdb4-37ba-40f1-a0b9-b526ef4cc5e0
-- title:
--   Exists Symplectic Coordinates Of Is Period
-- statement:
--   Definitions and structural lemmas for Exists Symplectic Coordinates Of Is Period, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSymplecticCoordinatesOfIsPeriod.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_precomp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_existsUnique_linear_ex
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isHolTo
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_ex
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_iff
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_RiemannRel_riemann_relations
import Theorems.Thm_GlobalTheory_ThetaSeparation_dense_ne_zero
import Theorems.Thm_GlobalTheory_alternating_eq_of_equivalent_factors
import Theorems.Thm_GlobalTheory_bijective_neg_bilinForm
import Theorems.Thm_GlobalTheory_bijective_of_image_range_eq
import Theorems.Thm_GlobalTheory_bijective_of_isometry_of_bijective_form
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_free_finite_finrank_of_lattice_embedding
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Filter Topology Matrix Complex
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FibreExp
section Frames
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {L : LB X}
theorem exists_frame_ratio (hL : L.IsLB) {c : V → (Sp ℂ ⟶ X)} (hc : IsHolTo Set.univ c) {fr fr' : L.ι → V → ℂ}
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ c z ⁻¹ᵁ L.U j}) (h0 : ∀ j z, ⊤ ≤ c z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hg : ∀ j j' z, ⊤ ≤ c z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (c z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z)
    (hd' : ∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ c z ⁻¹ᵁ L.U j}) (h0' : ∀ j z, ⊤ ≤ c z ⁻¹ᵁ L.U j → fr' j z ≠ 0)
    (hg' : ∀ j j' z, ⊤ ≤ c z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr' j z = valAt' (c z) (L.U j ⊓ L.U j') (L.g j j').val * fr' j' z) :
    (∀ z, ∃ j, ⊤ ≤ c z ⁻¹ᵁ L.U j) ∧ ∃ f : V → ℂ, Differentiable ℂ f ∧ (∀ z, f z ≠ 0) ∧
      ∀ j z, ⊤ ≤ c z ⁻¹ᵁ L.U j → fr j z = f z * fr' j z := by
  have hch : ∀ z, ∃ j, ⊤ ≤ c z ⁻¹ᵁ L.U j := fun z => by
    have : c z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (HolHom.le_preimage_iff _ _).2 hj⟩
  refine ⟨hch, ?_⟩
  choose J hJ using hch
  have key : ∀ j z, ⊤ ≤ c z ⁻¹ᵁ L.U j → fr j z = fr (J z) z / fr' (J z) z * fr' j z := fun j z hz => by
    have h : ⊤ ≤ c z ⁻¹ᵁ (L.U j ⊓ L.U (J z)) := le_inf hz (hJ z)
    rw [hg j _ z h, hg' j _ z h]
    field_simp [h0' _ z (hJ z)]
  refine ⟨fun z => fr (J z) z / fr' (J z) z, fun z => ?_, fun z => div_ne_zero (h0 _ z (hJ z)) (h0' _ z (hJ z)), key⟩
  have hn : {t | ⊤ ≤ c t ⁻¹ᵁ L.U (J z)} ∈ 𝓝 z := (HolHom.holAt_of_isHolTo hc (Set.mem_univ z) _ (hJ z)).1
  refine (((hd (J z)).differentiableAt hn).mul (((hd' (J z)).differentiableAt hn).inv
    (h0' _ z (hJ z)))).congr_of_eventuallyEq ?_
  filter_upwards [hn] with t ht
  rw [Pi.mul_apply, Pi.inv_apply, key _ t ht, mul_inv_cancel_right₀ (h0' _ t ht)]
theorem frame_law_of_periodic [FiniteDimensional ℂ V] {c : V → (Sp ℂ ⟶ X)} (hc : IsHolTo Set.univ c) {U : X.Opens}
    {fr θ a : V → ℂ} {p : V} (hd : DifferentiableOn ℂ fr {z | ⊤ ≤ c z ⁻¹ᵁ U}) (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (ha : Continuous a) (hp : ∀ z, c (z + p) = c z) (hlaw : ∀ z, θ (z + p) = a z * θ z)
    (hper : ∀ z, ⊤ ≤ c z ⁻¹ᵁ U → θ (z + p) * fr (z + p) = θ z * fr z) (z : V) (hz : ⊤ ≤ c z ⁻¹ᵁ U) :
    fr z = a z * fr (z + p) := by
  have hn : ∀ z, ⊤ ≤ c z ⁻¹ᵁ U → {t | ⊤ ≤ c t ⁻¹ᵁ U} ∈ 𝓝 z := fun z hz =>
    (HolHom.holAt_of_isHolTo hc (Set.mem_univ z) _ hz).1
  have hcont : ∀ z, ⊤ ≤ c z ⁻¹ᵁ U → ContinuousAt fr z := fun z hz => hd.continuousOn.continuousAt (hn z hz)
  have hdense := ThetaSeparation.dense_ne_zero hθ (Function.ne_iff.1 h0)
  have h1 : ContinuousAt (fun z => a z * fr (z + p)) z :=
    ha.continuousAt.mul (ContinuousAt.comp (f := fun z => z + p) (hcont _ (by rw [hp]; exact hz)) (by fun_prop))
  refine tendsto_nhds_unique_of_frequently_eq (hcont z hz) h1 ?_
  refine ((mem_closure_iff_frequently.1 (hdense z)).and_eventually (hn z hz)).mono fun y hy => ?_
  have h3 := hper y hy.2
  rw [hlaw] at h3
  apply mul_left_cancel₀ hy.1
  rw [← h3]; ring
end Frames
section Theta
open ReciprocityTheory.PTheta
variable {g : ℕ}
theorem thetaChar_eq_theta_re (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b = fun z => theta (fun i => (a i).re) (fun i => (b i).re) z τ := by
  have hre : ∀ {a : Fin g → ℂ}, (∀ i, a i = 0 ∨ a i = 1 / 2) → ofRealVec (fun i => (a i).re) = a := fun {a} ha => by
    funext i
    rcases ha i with h | h <;> simp [ofRealVec, h]
  have key : ∀ a b : Fin g → ℝ, thetaChar τ (ofRealVec a) (ofRealVec b) = fun z => theta a b z τ := fun a b => by
    funext z
    unfold thetaChar theta thetaTerm eC
    refine tsum_congr fun n => ?_
    have e1 : ((fun i => (n i : ℂ)) + ofRealVec a) = shiftVec a n := rfl
    rw [e1]
    congr 1
    ring
  rw [← key, hre ha, hre hb]
theorem apply_eq_of_period_matrix (Q : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (hQ : ∀ k, Q (Pi.single (.inl k) 1) = Pi.single k 1 ∧ Q (Pi.single (.inr k) 1) = τ *ᵥ Pi.single k 1)
    (u : Fin g ⊕ Fin g → ℤ) : Q u = τ *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k)) := by
  let Q' : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ) :=
    AddMonoidHom.mk' (fun u => τ *ᵥ ofIntVec (fun k => u (.inr k)) + ofIntVec (fun k => u (.inl k))) fun u v => by
      have h1 : ∀ s : Fin g → Fin g ⊕ Fin g, ofIntVec (fun k => (u + v) (s k)) =
          ofIntVec (fun k => u (s k)) + ofIntVec (fun k => v (s k)) := fun s => ofIntVec_add _ _
      rw [h1, h1, mulVec_add]; abel
  have : Q.toIntLinearMap = Q'.toIntLinearMap := by
    refine (Pi.basisFun ℤ _).ext fun k => ?_
    rw [Pi.basisFun_apply]
    change Q _ = τ *ᵥ _ + _
    rcases k with k | k
    · rw [(hQ k).1]
      funext i
      simp [ofIntVec, Pi.single_apply, mulVec, dotProduct]
    · rw [(hQ k).2]
      funext i
      simp [ofIntVec, Pi.single_apply, mulVec, dotProduct]
  exact LinearMap.congr_fun this u
end Theta
section Family
open ReciprocityTheory.PTheta
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
theorem free_finite_finrank_of_isPeriod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧ Module.finrank ℤ D.La = 2 * g := by
  obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_lattice_embedding P hP.2.1 hP.2.2.1 hP.2.2.2.1
  refine ⟨h1, h2, ?_⟩
  rw [h3, ← Module.finrank_mul_finrank ℝ ℂ (Fin g → ℂ), Complex.finrank_real_complex, Module.finrank_fin_fun]
theorem exists_symplectic_coordinates_of_isPeriod {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La, ∀ a b, D.EF (bas a) (bas b) = -omegaStd a b := by
  obtain ⟨_, _, h3⟩ := free_finite_finrank_of_isPeriod hP
  have hB : (-D.EF).IsAlt := fun x => by simp [D.alt]
  obtain ⟨c, hc⟩ := exists_isSymplecticBasis_of_finrank hB (bijective_neg_bilinForm D.unimod) h3
  refine ⟨c.equivFun.symm, fun a b => ?_⟩
  have := hc.apply_eq_sum hB (c.equivFun.symm a) (c.equivFun.symm b)
  simp only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearMap.neg_apply] at this
  rw [omegaStd, ← this, neg_neg]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (Fu : FamilyUnif Xo σ ty)
theorem exists_frame_ex (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) :
    ∃ (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (lin : (Fu.Di i).La → (Fin g → ℂ) →ₗ[ℂ] ℂ) (c : (Fu.Di i).La → ℂ),
      (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (Fu.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
      (∀ j z, ⊤ ≤ (Fu.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (Fu.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
        fr j z = valAt' (Fu.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val *
          fr j' z) ∧
      (∀ a j z, ⊤ ≤ (Fu.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z = cexp (lin a z + c a) * fr j (z + P a)) ∧
      ∀ a b, lin a (P b) - lin b (P a) = -(2 * Real.pi * I) * ((Fu.Di i).EF a b : ℂ) := by
  obtain ⟨bas, hbas⟩ := exists_symplectic_coordinates_of_isPeriod hP
  obtain ⟨h, τ, hh, hdet, hs, hpos, -⟩ := (RiemannRel.riemann_relations E H (Fu.Di i) g ty bas hbas).1 P hP
  obtain ⟨c₁, c₂, hc₁, hc₂, fr, hd, h0, hg, -, hsec⟩ := Fu.theta i 0 Set.univ (fun _ => P) bas (-1) (fun _ => h)
    (fun _ => τ) isOpen_univ isPreconnected_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
    (fun a b => by simpa using hbas a b) (fun _ _ => ⟨hpos, hh⟩)
  obtain ⟨s, hsec⟩ := hsec 0 trivial
  let m : (Fu.Di i).La → Fin g → ℤ := fun a k => bas.symm a (.inl k)
  let n : (Fu.Di i).La → Fin g → ℤ := fun a k => bas.symm a (.inr k)
  have hmn : ∀ a, h *ᵥ P a = τ *ᵥ ofIntVec (n a) + ofIntVec (m a) := fun a => by
    have := apply_eq_of_period_matrix ((h.mulVecLin.toAddMonoidHom.comp P).comp bas.toAddMonoidHom) τ hh (bas.symm a)
    simpa using this
  set a₁ : Fin g → ℝ := fun k => (c₁ k).re
  set a₂ : Fin g → ℝ := fun k => (c₂ k).re
  let lin : (Fu.Di i).La → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun a =>
    { toFun := fun z => -(2 * Real.pi * I) * (ofIntVec (n a) ⬝ᵥ h *ᵥ z)
      map_add' := fun z w => by rw [mulVec_add, dotProduct_add, mul_add]
      map_smul' := fun t z => by rw [mulVec_smul, dotProduct_smul]; simp only [smul_eq_mul, RingHom.id_apply]; ring }
  have hlin : ∀ a z, lin a z = -(2 * Real.pi * I) * (ofIntVec (n a) ⬝ᵥ h *ᵥ z) := fun _ _ => rfl
  have hd' : ∀ j, DifferentiableOn ℂ (fun z => fr j (0, z)) {z | ⊤ ≤ (Fu.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
    fun j => (hd j).comp (f := fun z => (0, z)) (by fun_prop) fun z hz => ⟨trivial, hz⟩
  refine ⟨fun j z => fr j (0, z), lin, fun a => 2 * Real.pi * I *
    (ofRealVec a₁ ⬝ᵥ ofIntVec (m a) - ofRealVec a₂ ⬝ᵥ ofIntVec (n a) - ofIntVec (n a) ⬝ᵥ (τ *ᵥ ofIntVec (n a)) / 2),
    hd', fun j z => h0 j 0 z trivial, fun j j' z => hg j j' 0 z trivial, fun a j => ?_, fun a b => ?_⟩
  · have hp : ∀ z, Fu.ex i P (z + P a) = Fu.ex i P z := fun z => by
      rw [Fu.ex_add i P hP, (Fu.ex_ker i P hP _).2 ⟨a, rfl⟩, _root_.mul_one]
    refine frame_law_of_periodic (θ := fun z => theta a₁ a₂ (h *ᵥ z) τ) (HolHom.isHolTo_ex Fu i hP) (hd' j)
      ((differentiable_theta ⟨hs, hpos⟩ a₁ a₂).comp (h.mulVecLin.toContinuousLinearMap.differentiable)) ?_
      (((lin a).continuous_of_finiteDimensional.add continuous_const).cexp) (fun z => by rw [hp]) (fun z => ?_)
      fun z hz => ?_
    · intro h1
      refine theta_ne_zero ⟨hs, hpos⟩ a₁ a₂ (funext fun w => ?_)
      have := congrFun h1 (h⁻¹ *ᵥ w)
      simpa [mulVec_mulVec, mul_nonsing_inv h hdet] using this
    · rw [mulVec_add, hmn, ← add_assoc, thetaQuasiPeriod_holds _ _ _ _ _ _ _ hs, autFactor, eC, eC, ← Complex.exp_add,
        hlin]
      congr 2
      ring
    · have hw : (Fu.ex i P z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ Fu.u i P := by simpa using Over.w (Fu.ex i P z)
      have h1 := hsec j z (pullback.lift _ _ hw) (pullback.lift_fst ..) (pullback.lift_snd ..) hz
      have h2 := hsec j (z + P a) (pullback.lift _ _ hw) (by beta_reduce; rw [hp]; exact pullback.lift_fst ..)
        (pullback.lift_snd ..) (by beta_reduce; rw [hp]; exact hz)
      simp only [thetaChar_eq_theta_re τ hc₁ hc₂] at h1 h2
      exact h2.symm.trans h1
  · have hE := hbas (bas.symm a) (bas.symm b)
    rw [bas.apply_symm_apply, bas.apply_symm_apply] at hE
    have hsym : ofIntVec (n a) ⬝ᵥ τ *ᵥ ofIntVec (n b) = ofIntVec (n b) ⬝ᵥ τ *ᵥ ofIntVec (n a) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    have hω : ((omegaStd (bas.symm a) (bas.symm b) : ℤ) : ℂ) =
        ofIntVec (n b) ⬝ᵥ ofIntVec (m a) - ofIntVec (n a) ⬝ᵥ ofIntVec (m b) := by
      simp [omegaStd, dotProduct, ofIntVec, m, n, mul_comm]
    rw [hlin, hlin, hmn, hmn, dotProduct_add, dotProduct_add, hsym, hE, Int.cast_neg, hω]
    ring
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
theorem alternating_eq (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (h : V →ₗ[ℂ] (Fin g → ℂ)) {A : Type} (p : A → V) (gam : A → (Fu.Di i).La) (hgam : ∀ a, h (p a) = P (gam a))
    {fr : Xo.univ.t.PP.L.ι → V → ℂ} (lin : A → V →ₗ[ℂ] ℂ) (c : A → ℂ)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {v | ⊤ ≤ (Fu.ex i P (h v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (h0 : ∀ j v, ⊤ ≤ (Fu.ex i P (h v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0)
    (hg : ∀ j j' v, ⊤ ≤ (Fu.ex i P (h v)).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j v = valAt' (Fu.ex i P (h v)).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' v)
    (hlaw : ∀ a j v, ⊤ ≤ (Fu.ex i P (h v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j v = cexp (lin a v + c a) * fr j (v + p a)) (a b : A) :
    lin a (p b) - lin b (p a) = -(2 * Real.pi * I) * ((Fu.Di i).EF (gam a) (gam b) : ℂ) := by
  obtain ⟨fr₀, lin₀, c₀, hd₀, h0₀, hg₀, hlaw₀, halt⟩ := exists_frame_ex Fu i hP
  have hh : Differentiable ℂ h := h.toContinuousLinearMap.differentiable
  have hol : IsHolTo Set.univ (fun v => (Fu.ex i P (h v)).left) :=
    HolHom.isHolTo_of_holAt isOpen_univ fun v _ =>
      (HolHom.holAt_of_isHolTo (HolHom.isHolTo_ex Fu i hP) (Set.mem_univ (h v))).precomp (hh v)
  obtain ⟨hch, f, hf, hf0, hfr⟩ := exists_frame_ratio Xo.univ.t.PP.isLB hol (fr' := fun j v => fr₀ j (h v)) hd h0 hg
    (fun j => (hd₀ j).comp hh.differentiableOn fun _ hv => hv) (fun j v => h0₀ j (h v)) (fun j j' v => hg₀ j j' (h v))
  have key := alternating_eq_of_equivalent_factors p (fun a => (lin₀ (gam a)).comp h) lin (fun a => c₀ (gam a)) c
    hf.continuous hf0 (fun a v => by
      obtain ⟨j, hj⟩ := hch v
      have hp : Fu.ex i P (h (v + p a)) = Fu.ex i P (h v) := by
        rw [map_add, hgam, Fu.ex_add i P hP, (Fu.ex_ker i P hP _).2 ⟨gam a, rfl⟩, _root_.mul_one]
      have hj' : ⊤ ≤ (Fu.ex i P (h (v + p a))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hp]; exact hj
      have h1 := hlaw a j v hj
      rw [hfr j v hj, hfr j _ hj', hlaw₀ (gam a) j _ hj, ← hgam, ← map_add] at h1
      apply mul_right_cancel₀ (h0₀ j _ hj')
      rw [LinearMap.comp_apply]
      linear_combination h1) a b
  rw [← key, LinearMap.comp_apply, LinearMap.comp_apply, hgam, hgam, halt]
theorem intertwines (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (h : V →ₗ[ℂ] (Fin g → ℂ)) (x : 𝓞 E) (φ : V →ₗ[ℂ] V)
    (hφ : ∀ v, Fu.ex i P (h (φ v)) = Fu.ex i P (h v) ≫ Xo.univ.t.act.act x) (v : V) (k : Fin g) :
    h (φ v) k = ty k (x : E) * h v k := by
  have hh : Differentiable ℂ (h.comp φ) := (h.comp φ).toContinuousLinearMap.differentiable
  have hol : IsHolTo Set.univ (fun v => (Fu.ex i P (h (φ v))).left) :=
    HolHom.isHolTo_of_holAt isOpen_univ fun v _ =>
      (HolHom.holAt_of_isHolTo (HolHom.isHolTo_ex Fu i hP) (Set.mem_univ (h (φ v)))).precomp (k := h.comp φ) (hh v)
  have hu := HolHom.existsUnique_linear_ex Fu i hP (e := fun v => Fu.ex i P (h (φ v)))
    (fun z w => by rw [map_add, map_add, Fu.ex_add i P hP]) hol
  have := hu.unique (y₁ := h.comp φ) (y₂ := LinearMap.pi fun k => ty k (x : E) • (LinearMap.proj k).comp h)
    (fun _ => rfl) (fun z => by rw [hφ, ← Fu.ex_lin i P hP]; rfl)
  exact congrFun (LinearMap.congr_fun this v) k
end Family
end GlobalTheory.FibreExp
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
theorem fibre_hom_eq_exponential (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (Fu.Di i) ty P) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (hdim : Module.finrank ℂ V = g) {La' : Type} [AddCommGroup La'] [Module.Free ℤ La'] [Module.Finite ℤ La']
    (hrk : Module.finrank ℤ La' = 2 * g) (EF' : LinearMap.BilinForm ℤ La') (hEF : Function.Bijective EF')
    (P' : La' →+ V) (pi : V → (Over.mk (Fu.u i P) ⟶ Xo.univ.t.G))
    (hadd : ∀ v w, pi (v + w) = pi v * pi w) (hol : IsHolTo Set.univ (fun v => (pi v).left))
    (hker : ∀ a, pi (P' a) = 1) (fr : Xo.univ.t.PP.L.ι → V → ℂ)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {v | ⊤ ≤ (pi v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (h0 : ∀ j v, ⊤ ≤ (pi v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0)
    (hg : ∀ j j' v, ⊤ ≤ (pi v).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j v = valAt' (pi v).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' v)
    (lin : La' → V →ₗ[ℂ] ℂ) (c : La' → ℂ)
    (hlaw : ∀ a j v, ⊤ ≤ (pi v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v = cexp (lin a v + c a) * fr j (v + P' a))
    (halt : ∀ a b, lin a (P' b) - lin b (P' a) = -(2 * Real.pi * I) * (EF' a b : ℂ)) :
    ∃ (h : V ≃ₗ[ℂ] (Fin g → ℂ)) (gam : La' ≃ₗ[ℤ] (Fu.Di i).La),
      (∀ v, pi v = Fu.ex i P (h v)) ∧ (∀ a, h (P' a) = P (gam a)) ∧
      (∀ a b, (Fu.Di i).EF (gam a) (gam b) = EF' a b) ∧
      (∀ (x : 𝓞 E) (φ : V →ₗ[ℂ] V), (∀ v, pi (φ v) = pi v ≫ Xo.univ.t.act.act x) →
        (∀ v k, h (φ v) k = ty k (x : E) * h v k) ∧ ∀ a a', P' a' = φ (P' a) → gam a' = x • gam a) ∧
      ∀ [Module (𝓞 E) La'] (ρ : 𝓞 E → V →ₗ[ℂ] V), (∀ x v, pi (ρ x v) = pi v ≫ Xo.univ.t.act.act x) →
        (∀ x a, P' (x • a) = ρ x (P' a)) → (∀ x v k, h (ρ x v) k = ty k (x : E) * h v k) ∧
          ∃ gamO : La' ≃ₗ[𝓞 E] (Fu.Di i).La, ∀ a, gamO a = gam a := by
  obtain ⟨h, hh, -⟩ := HolHom.existsUnique_linear_ex Fu i hP hadd hol
  obtain rfl : pi = fun v => Fu.ex i P (h v) := funext hh
  choose gam hgam using fun a => (Fu.ex_ker i P hP _).1 (hker a)
  have hEq : ∀ a b, (Fu.Di i).EF (gam a) (gam b) = EF' a b := fun a b => by
    have := FibreExp.alternating_eq Fu i hP h P' gam (fun a => (hgam a).symm) lin c hd h0 hg hlaw a b
    rw [halt] at this
    exact_mod_cast (mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero) this).symm
  obtain ⟨_, _, h3⟩ := FibreExp.free_finite_finrank_of_isPeriod hP
  let gam₀ : La' →ₗ[ℤ] (Fu.Di i).La :=
    (AddMonoidHom.mk' gam fun a b => hP.2.1 (by simp only [hgam, map_add])).toIntLinearMap
  have hb : Function.Bijective gam₀ :=
    bijective_of_isometry_of_bijective_form (hrk.trans h3.symm) EF' (Fu.Di i).EF hEF gam₀ hEq
  have hbh : Function.Bijective h :=
    bijective_of_image_range_eq (hdim.trans (Module.finrank_fin_fun ℂ).symm) h hP.2.2.2.1 (by
      rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hb.2 b
      exact ⟨P' a, (hgam a).symm⟩)
  have hO : ∀ (x : 𝓞 E) (φ : V →ₗ[ℂ] V), (∀ v, Fu.ex i P (h (φ v)) = Fu.ex i P (h v) ≫ Xo.univ.t.act.act x) →
      (∀ v k, h (φ v) k = ty k (x : E) * h v k) ∧ ∀ a a', P' a' = φ (P' a) → gam a' = x • gam a := fun x φ hφ => by
    have h1 := FibreExp.intertwines Fu i hP h x φ hφ
    refine ⟨h1, fun a a' ha => hP.2.1 (funext fun k => ?_)⟩
    rw [hP.1, hgam, hgam, ha, h1]
  refine ⟨LinearEquiv.ofBijective h hbh, LinearEquiv.ofBijective gam₀ hb, fun _ => rfl, fun a => (hgam a).symm, hEq,
    hO, fun ρ hρ hP' => ⟨fun x => (hO x _ (hρ x)).1, ?_⟩⟩
  let gam₁ : La' →ₗ[𝓞 E] (Fu.Di i).La :=
    { toFun := gam₀
      map_add' := gam₀.map_add
      map_smul' := fun x a => (hO x _ (hρ x)).2 a _ (hP' x a) }
  exact ⟨LinearEquiv.ofBijective gam₁ hb, fun _ => rfl⟩
example (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[ℤ] (Fu.Di i).La),
      (∀ v, Fu.ex i P v = Fu.ex i P (h v)) ∧ ∀ a, h (P a) = P (gam a) := by
  obtain ⟨fr, lin, c, hd, h0, hg, hlaw, halt⟩ := FibreExp.exists_frame_ex Fu i hP
  obtain ⟨_, _, h3⟩ := FibreExp.free_finite_finrank_of_isPeriod hP
  obtain ⟨h, gam, h1, h2, -⟩ := fibre_hom_eq_exponential Fu i hP (Module.finrank_fin_fun ℂ) h3 _ (Fu.Di i).unimod P
    (Fu.ex i P) (Fu.ex_add i P hP) (HolHom.isHolTo_ex Fu i hP) (fun a => (Fu.ex_ker i P hP _).2 ⟨a, rfl⟩) fr hd h0 hg
    lin c hlaw halt
  exact ⟨h, gam, h1, h2⟩
end GlobalTheory


