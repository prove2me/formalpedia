-- Prove2me | Definitions.Def_RPLib_S3_EllipticTermB
-- name    : RPLib_S3_EllipticTermB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:03:42.621597+00:00
-- url     : https://prove2.me/theorems/640436be-ffa9-4857-8283-cf06070fc0f3
-- title:
--   The Eichler-Selberg trace formula, elliptic term part B: conjugation invariance and orbit unfolding
-- statement:
--   Invariance of the kernel terms $\varphi_g$ under conjugation by $SL_2(\mathbb{Z})$ and the unfolding of the elliptic part of the kernel diagonal over $\Gamma_1(M)$-conjugacy classes into orbital integrals over $\mathbb{H}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTermA
import Definitions.Def_RPLib_S3_KernelA2
import Definitions.Def_RPLib_S3_KernelB1
import Definitions.Def_RPLib_S3_ConjClassesC
import Definitions.Def_RPLib_S3_ConjClassesD

/-!
# S3-EllCentralTerms, part B: conjugation invariance and orbit unfolding (library file, from units/S3-EllCentralTerms/EllB_v4.lean)
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal Manifold MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllTerm

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

/-! ## Part 1: `phiG (h g h⁻¹) (h z) = phiG g z` -/

lemma Q_conj_alg (a b c d p q r s z zb X Xb a' b' c' d' : ℂ) (hdet : p * s - q * r = 1)
    (ha : a' = (p * a + q * c) * s - (p * b + q * d) * r) (hb : b' = (p * b + q * d) * p - (p * a + q * c) * q)
    (hc : c' = (r * a + s * c) * s - (r * b + s * d) * r) (hd : d' = (r * b + s * d) * p - (r * a + s * c) * q)
    (hX : X * (r * z + s) = p * z + q) (hXb : Xb * (r * zb + s) = p * zb + q) :
    (a' * X + b' - Xb * (c' * X + d')) * ((r * z + s) * (r * zb + s)) = a * z + b - zb * (c * z + d) := by
  subst ha hb hc hd
  linear_combination
    (((p * a + q * c) * s - (p * b + q * d) * r) * (r * zb + s) - (p * zb + q) *
        ((r * a + s * c) * s - (r * b + s * d) * r)) * hX -
      (((r * a + s * c) * s - (r * b + s * d) * r) * X * (r * z + s) +
        ((r * b + s * d) * p - (r * a + s * c) * q) * (r * z + s)) * hXb +
      (p * s - q * r + 1) * (a * z + b - zb * (c * z + d)) * hdet

lemma conj_entries (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    S3.Conj.conj h g 0 0 = (h 0 0 * g 0 0 + h 0 1 * g 1 0) * h 1 1 - (h 0 0 * g 0 1 + h 0 1 * g 1 1) * h 1 0 ∧
    S3.Conj.conj h g 0 1 = (h 0 0 * g 0 1 + h 0 1 * g 1 1) * h 0 0 - (h 0 0 * g 0 0 + h 0 1 * g 1 0) * h 0 1 ∧
    S3.Conj.conj h g 1 0 = (h 1 0 * g 0 0 + h 1 1 * g 1 0) * h 1 1 - (h 1 0 * g 0 1 + h 1 1 * g 1 1) * h 1 0 ∧
    S3.Conj.conj h g 1 1 = (h 1 0 * g 0 1 + h 1 1 * g 1 1) * h 0 0 - (h 1 0 * g 0 0 + h 1 1 * g 1 0) * h 0 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [S3.Conj.conj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two] <;> ring

/-- **Conjugation invariance** of the diagonal integrand. -/
theorem phiG_conj (k : ℕ) (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    phiG k (S3.Conj.conj h g) (h • z) = phiG k g z := by
  rw [phiG_eq_div, phiG_eq_div]
  congr 1
  have hj : ((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ) ≠ 0 := by
    have hd := denom_ne_zero (h : GL (Fin 2) ℝ) z
    rwa [denom_SL] at hd
  have hX : ((h • z : ℍ) : ℂ) * (((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) =
      ((h 0 0 : ℤ) : ℂ) * z + ((h 0 1 : ℤ) : ℂ) := by
    rw [coe_smul_SL]; exact div_mul_cancel₀ _ hj
  have hXb : conj ((h • z : ℍ) : ℂ) * (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)) =
      ((h 0 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 0 1 : ℤ) : ℂ) := by
    have := congrArg conj hX
    simpa only [map_mul, map_add, map_intCast] using this
  have hdet : ((h 0 0 : ℤ) : ℂ) * ((h 1 1 : ℤ) : ℂ) - ((h 0 1 : ℤ) : ℂ) * ((h 1 0 : ℤ) : ℂ) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe h
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  obtain ⟨e0, e1, e2, e3⟩ := conj_entries h g
  have hQ : Q (S3.Conj.conj h g) ((h • z : ℍ) : ℂ) (-conj ((h • z : ℍ) : ℂ)) *
      ((((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) * (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)))
      = Q g z (-conj (z : ℂ)) := by
    rw [Q_neg_conj, Q_neg_conj]
    exact Q_conj_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdet (by rw [e0]; push_cast; ring)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) (by rw [e3]; push_cast; ring) hX hXb
  have hy : (((h • z : ℍ).im : ℝ) : ℂ) *
      ((((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) * (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)))
      = ((z.im : ℝ) : ℂ) := by
    have e4 : ∀ w : ℂ, ((w.im : ℝ) : ℂ) = (w - conj w) / (2 * Complex.I) := by
      intro w; rw [Complex.sub_conj]; field_simp [Complex.I_ne_zero]; push_cast; ring
    rw [show (h • z : ℍ).im = ((h • z : ℍ) : ℂ).im from rfl, show z.im = (z : ℂ).im from rfl, e4, e4,
      div_mul_eq_mul_div, div_left_inj' (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
    linear_combination (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)) * hX -
      (((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) * hXb + ((z : ℂ) - conj (z : ℂ)) * hdet
  have hN : (((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) *
      (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)) ≠ 0 := by
    refine mul_ne_zero hj ?_
    intro h0; apply hj
    have := congrArg conj h0
    simpa only [map_mul, map_add, map_intCast, conj_conj, map_zero] using this
  have hNr : conj ((((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) *
      (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ))) =
      (((h 1 0 : ℤ) : ℂ) * z + ((h 1 1 : ℤ) : ℂ)) * (((h 1 0 : ℤ) : ℂ) * conj (z : ℂ) + ((h 1 1 : ℤ) : ℂ)) := by
    simp only [map_mul, map_add, map_intCast, conj_conj]; ring
  rw [← mul_div_mul_right _ _ hN, hy, ← hNr, ← map_mul, hQ]

/-! ## Part 2: sums over an orbit -/

/-- `Σ_{γ ∈ G} F(γ x) = #Stab(x) · Σ_{y ∈ G x} F(y)` for a finite stabiliser. -/
theorem tsum_orbit {G X : Type*} [Group G] [MulAction G X] (x : X)
    [Finite (MulAction.stabilizer G x)] {F : X → ℂ}
    (hF : Summable fun y : MulAction.orbit G x => F y) :
    Summable (fun γ : G => F (γ • x)) ∧
      ∑' γ : G, F (γ • x) = (Nat.card (MulAction.stabilizer G x) : ℂ) *
        ∑' y : MulAction.orbit G x, F y := by
  classical
  let pr : G → MulAction.orbit G x := fun γ => ⟨γ • x, MulAction.mem_orbit x γ⟩
  have hfib : ∀ y : MulAction.orbit G x, {γ // pr γ = y} ≃ MulAction.stabilizer G x := by
    intro y
    have hy := MulAction.mem_orbit_iff.1 y.2
    have h0 : (Classical.choose hy) • x = y := Classical.choose_spec hy
    exact
      { toFun := fun γ => ⟨(Classical.choose hy)⁻¹ * γ.1, by
          rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, h0]
          exact congrArg Subtype.val γ.2⟩
        invFun := fun s => ⟨Classical.choose hy * s.1, by
          apply Subtype.ext
          show (Classical.choose hy * s.1) • x = y
          rw [mul_smul, MulAction.mem_stabilizer_iff.1 s.2, h0]⟩
        left_inv := fun γ => Subtype.ext (mul_inv_cancel_left _ γ.1)
        right_inv := fun s => Subtype.ext (inv_mul_cancel_left _ s.1) }
  have hfin : ∀ y, Finite {γ // pr γ = y} := fun y => Finite.of_equiv _ (hfib y).symm
  have hcard : ∀ y, Nat.card {γ // pr γ = y} = Nat.card (MulAction.stabilizer G x) :=
    fun y => Nat.card_congr (hfib y)
  let e := Equiv.sigmaFiberEquiv pr
  have he : ∀ p : (Σ y, {γ // pr γ = y}), F ((e p) • x) = F p.1 := by
    rintro ⟨y, γ, hγ⟩
    subst hγ
    rfl
  have hnorm : Summable fun y : MulAction.orbit G x => ‖F y‖ := summable_norm_iff.2 hF
  have hsig : Summable fun p : (Σ y, {γ // pr γ = y}) => F p.1 := by
    refine Summable.of_norm ?_
    refine (summable_sigma_of_nonneg (fun p => norm_nonneg _)).2 ⟨fun y => Summable.of_finite, ?_⟩
    simp only [tsum_const, hcard, nsmul_eq_mul]
    exact hnorm.mul_left _
  have hS : Summable fun γ : G => F (γ • x) := by
    rw [← e.summable_iff]
    exact hsig.congr fun p => (he p).symm
  refine ⟨hS, ?_⟩
  rw [← e.tsum_eq, show (fun p => F (e p • x)) = fun p : (Σ y, {γ // pr γ = y}) => F p.1 from funext he,
    hsig.tsum_sigma]
  simp only [tsum_const, hcard, nsmul_eq_mul]
  exact tsum_mul_left

/-! ## Part 3: integrability of `Σ_γ Φ(γ z)` on the fundamental domain -/

theorem integrable_tsum_of_lintegral {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    {f : ι → α → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hlin : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ⊤) : Integrable (fun a => ∑' i, f i a) μ := by
  refine ⟨(AEMeasurable.tsum fun i => (hf i).aemeasurable).aestronglyMeasurable, ?_⟩
  show ∫⁻ a, ‖∑' i, f i a‖ₑ ∂μ < ⊤
  calc ∫⁻ a, ‖∑' i, f i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖f i a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ := lintegral_tsum fun i => (hf i).enorm
    _ < ⊤ := lt_top_iff_ne_top.2 hlin

theorem integrableOn_fdom_tsum {M : ℕ} (hM : 3 ≤ M) {Φ : ℍ → ℂ} (hΦ : Integrable Φ) :
    IntegrableOn (fun z => ∑' γ : Gamma1 M, Φ ((γ : SL(2, ℤ)) • z)) (fdom (Gamma1 M)) := by
  have := countable_SL2Z
  have hc := countable_pglImage_coe (Gamma1 M)
  have hF := isFundamentalDomain_fdom (Gamma1 M)
  have hmeas : ∀ γ : Gamma1 M, AEStronglyMeasurable (fun z => Φ ((γ : SL(2, ℤ)) • z))
      (volume.restrict (fdom (Gamma1 M))) := by
    intro γ
    have h1 : (fun z : ℍ => Φ ((γ : SL(2, ℤ)) • z)) = fun z => Φ (toPGLR (γ : SL(2, ℤ)) • z) := by
      funext z; rw [toPGLR_smul]
    rw [h1]
    exact (hΦ.1.comp_measurePreserving (measurePreserving_smul (toPGLR (γ : SL(2, ℤ))) volume)).restrict
  have h3 : ∑' γ : Gamma1 M, ∫⁻ z in fdom (Gamma1 M), ‖Φ ((γ : SL(2, ℤ)) • z)‖ₑ =
      ∑' g : pglImage ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
        ∫⁻ z in fdom (Gamma1 M), ‖Φ (g • z)‖ₑ := by
    rw [← (gammaPGL M hM).tsum_eq (fun g => ∫⁻ z in fdom (Gamma1 M), ‖Φ (g • z)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [gammaPGL_smul]
  have hlin : ∑' γ : Gamma1 M, ∫⁻ z in fdom (Gamma1 M), ‖Φ ((γ : SL(2, ℤ)) • z)‖ₑ ≠ ⊤ := by
    rw [h3, ← hF.lintegral_eq_tsum'' (fun z => ‖Φ z‖ₑ)]
    exact ne_of_lt hΦ.2
  exact integrable_tsum_of_lintegral hmeas hlin

/-! ## Part 4: unfolding one `Γ₁(M)`-class -/

/-- `Σ_{classes C} orbit(C.out) ≃ X`, forward map `⟨C, y⟩ ↦ y`. -/
def sigmaOrbits (G X : Type*) [Group G] [MulAction G X] :
    (Σ C : MulAction.orbitRel.Quotient G X, MulAction.orbit G C.out) ≃ X where
  toFun p := p.2.1
  invFun x := ⟨Quotient.mk (MulAction.orbitRel G X) x, ⟨x, MulAction.orbitRel_apply.1
    (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm)⟩⟩
  left_inv := by
    rintro ⟨C, y, hy⟩
    have h : Quotient.mk (MulAction.orbitRel G X) y = C :=
      (Quotient.sound (MulAction.orbitRel_apply.2 hy)).trans (Quotient.out_eq C)
    subst h
    rfl
  right_inv x := rfl

/-- One orbit: `Σ_{y ∈ Γ₁ x₀} φ(y, z) = #Stab(x₀)⁻¹ Σ_γ φ(x₀, γ z)`. -/
theorem tsum_orbit_phiG {M : ℕ} (k : ℕ) {X : Type*} [MulAction (Gamma1 M) X] (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    (x0 : X) [Finite (MulAction.stabilizer (Gamma1 M) x0)] (z : ℍ)
    (hs : Summable fun y : MulAction.orbit (Gamma1 M) x0 => phiG k (val y) z) :
    ∑' y : MulAction.orbit (Gamma1 M) x0, phiG k (val y) z =
      (Nat.card (MulAction.stabilizer (Gamma1 M) x0) : ℂ)⁻¹ *
        ∑' γ : Gamma1 M, phiG k (val x0) ((γ : SL(2, ℤ)) • z) := by
  obtain ⟨-, h⟩ := tsum_orbit (G := Gamma1 M) x0 (F := fun y => phiG k (val y) z) hs
  have hN : (Nat.card (MulAction.stabilizer (Gamma1 M) x0) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have h2 : ∑' γ : Gamma1 M, phiG k (val (γ • x0)) z =
      ∑' γ : Gamma1 M, phiG k (val x0) ((γ : SL(2, ℤ)) • z) := by
    rw [← (Equiv.inv (Gamma1 M)).tsum_eq]
    refine tsum_congr fun γ => ?_
    have e1 : ((γ⁻¹ : Gamma1 M) : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • z) = z := by
      rw [Subgroup.coe_inv, inv_smul_smul]
    simp only [Equiv.inv_apply]
    rw [hval, ← phiG_conj k ((γ⁻¹ : Gamma1 M) : SL(2, ℤ)) (val x0) ((γ : SL(2, ℤ)) • z), e1]
  rw [h2] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **Unfolding** of a `Γ₁(M)`-stable family of matrices with finitely many classes. -/
theorem class_unfold {M : ℕ} (hM : 3 ≤ M) (k : ℕ) {X : Type*} [MulAction (Gamma1 M) X]
    (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    [Finite (MulAction.orbitRel.Quotient (Gamma1 M) X)]
    (hstab : ∀ x : X, Finite (MulAction.stabilizer (Gamma1 M) x))
    (hsum : ∀ z : ℍ, Summable fun x : X => phiG k (val x) z)
    (hint : ∀ x : X, Integrable (phiG k (val x))) :
    IntegrableOn (fun z => ∑' x : X, phiG k (val x) z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : X, phiG k (val x) z =
        ∑ᶠ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
          (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ * ∫ z, phiG k (val C.out) z := by
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient (Gamma1 M) X)
  have hpt : ∀ z : ℍ, ∑' x : X, phiG k (val x) z =
      ∑ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
        (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ *
          ∑' γ : Gamma1 M, phiG k (val C.out) ((γ : SL(2, ℤ)) • z) := by
    intro z
    have hs : Summable fun c : (Σ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
        MulAction.orbit (Gamma1 M) C.out) => phiG k (val c.2.1) z :=
      ((sigmaOrbits (Gamma1 M) X).summable_iff (f := fun x => phiG k (val x) z)).2 (hsum z)
    rw [← (sigmaOrbits (Gamma1 M) X).tsum_eq (fun x => phiG k (val x) z)]
    show ∑' c : (Σ C : MulAction.orbitRel.Quotient (Gamma1 M) X, MulAction.orbit (Gamma1 M) C.out),
      phiG k (val c.2.1) z = _
    rw [hs.tsum_sigma, tsum_fintype]
    refine Finset.sum_congr rfl fun C _ => ?_
    have := hstab C.out
    exact tsum_orbit_phiG k val hval C.out z ((hsum z).subtype _)
  have hI : ∀ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
      IntegrableOn (fun z => (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ *
        ∑' γ : Gamma1 M, phiG k (val C.out) ((γ : SL(2, ℤ)) • z)) (fdom (Gamma1 M)) :=
    fun C => (integrableOn_fdom_tsum hM (hint C.out)).const_mul _
  rw [show (fun z => ∑' x : X, phiG k (val x) z) = _ from funext hpt]
  refine ⟨integrable_finsetSum Finset.univ fun C _ => hI C, ?_⟩
  rw [integral_finsetSum Finset.univ fun C _ => hI C, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [integral_const_mul, integral_fdom_tsum hM (hint C.out)]

/-- Unfolding when every orbital integral has the same value `I`: the result is `classSum · I`. -/
theorem class_unfold_const {M : ℕ} (hM : 3 ≤ M) (k : ℕ) {X : Type*} [MulAction (Gamma1 M) X]
    (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    [Finite (MulAction.orbitRel.Quotient (Gamma1 M) X)]
    (hstab : ∀ x : X, Finite (MulAction.stabilizer (Gamma1 M) x))
    (hsum : ∀ z : ℍ, Summable fun x : X => phiG k (val x) z)
    (hint : ∀ x : X, Integrable (phiG k (val x))) (I : ℂ) (hI : ∀ x : X, ∫ z, phiG k (val x) z = I) :
    IntegrableOn (fun z => ∑' x : X, phiG k (val x) z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : X, phiG k (val x) z =
        ((S3.Conj.classSum (Gamma1 M) X : ℚ) : ℂ) * I := by
  obtain ⟨h1, h2⟩ := class_unfold hM k val hval hstab hsum hint
  refine ⟨h1, ?_⟩
  rw [h2]
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient (Gamma1 M) X)
  rw [S3.Conj.classSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [hI]
  push_cast
  ring

/-! ## Part 5: the elliptic families `EllPos`, `EllNeg` -/

theorem finite_stab_EllPos {M : ℕ} [NeZero M] {δ' : ZMod M} {t : ℤ} {n : ℕ}
    (x : S3.Conj.EllPos M δ' t n) : Finite (MulAction.stabilizer (Gamma1 M) x) := by
  obtain ⟨i, hi⟩ := S3.Conj.psi_surjective δ' t n (Quotient.mk _ x)
  apply Nat.finite_of_card_ne_zero
  rw [← S3.Conj.card_stab_out (G := Gamma1 M) x, ← hi, S3.Conj.psi, S3.Conj.card_stab_out,
    S3.Conj.card_stab_xpt]
  obtain ⟨hQ, -, -⟩ := (S3.Conj.mem_pairSet δ' t n).1 i.2
  have h := S3.Conj.card_stab_mul_ncard_orbit (M := M) (S3.Conj.mem_redForms.1 hQ).2 i.1.2
  intro h0
  rw [h0, zero_mul] at h
  have : S3.stabOrd i.1.1 ≠ 0 := by unfold S3.stabOrd; split_ifs <;> omega
  exact this h.symm

theorem finite_stab_EllNeg {M : ℕ} [NeZero M] {δ' : ZMod M} {t : ℤ} {n : ℕ}
    (x : S3.Conj.EllNeg M δ' t n) : Finite (MulAction.stabilizer (Gamma1 M) x) := by
  have hφ : ∀ (g : Gamma1 M) (y : S3.Conj.EllNeg M δ' t n),
      S3.Conj.negEquiv M δ' t n (g • y) = S3.Conj.flipG1 M g • S3.Conj.negEquiv M δ' t n y :=
    fun h γ => Subtype.ext (S3.Conj.flip_conj (h : SL(2, ℤ)) γ.1)
  have := finite_stab_EllPos (S3.Conj.negEquiv M δ' t n x)
  have hc : Nat.card (MulAction.stabilizer (Gamma1 M) x) =
      Nat.card (MulAction.stabilizer (Gamma1 M) (S3.Conj.negEquiv M δ' t n x)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv (S3.Conj.flipG1 M).toEquiv fun g => ?_)
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    show g • x = x ↔ S3.Conj.flipG1 M g • S3.Conj.negEquiv M δ' t n x = S3.Conj.negEquiv M δ' t n x
    rw [← hφ, (S3.Conj.negEquiv M δ' t n).injective.eq_iff]
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact Nat.card_pos.ne'

/-- `x ↦ φ(x, z)` is summable over any family of matrices inside `Δ^{(δ')}_n(M)`. -/
theorem summable_phiG_sub {M : ℕ} (k : ℕ) (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    {X : Type*} (val : X → S3.Conj.Mat) (hinj : Function.Injective val)
    (hmem : ∀ x, val x ∈ DeltaSet M n δ') (z : ℍ) :
    Summable fun x : X => phiG k (val x) z := by
  have hv : 0 < (-conj (z : ℂ)).im := by
    rw [Complex.neg_im, Complex.conj_im, neg_neg]; exact z.im_pos
  have h1 : Summable fun g : DeltaSet M n δ' => (Q g.1 (z : ℂ) (-conj (z : ℂ)) ^ k)⁻¹ :=
    summable_omega M k hn δ' hk z.im_pos hv
  have h2 : Summable fun g : DeltaSet M n δ' => phiG k g.1 z := by
    have h3 := (Complex.summable_conj.2 h1).mul_right ((z.im : ℂ) ^ k)
    refine h3.congr fun g => ?_
    rw [phiG]
  let i : X → DeltaSet M n δ' := fun x => ⟨val x, hmem x⟩
  have hi : Function.Injective i := fun a b h => hinj (congrArg Subtype.val h)
  have h := h2.comp_injective hi
  exact h

lemma ell_of_EllPos {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} (x : S3.Conj.EllPos M δ' t n) :
    ((x : S3.Conj.Mat) 0 0 + (x : S3.Conj.Mat) 1 1) ^ 2 < 4 * (x : S3.Conj.Mat).det := by
  obtain ⟨h1, h2, -, h4, -, -⟩ := S3.Conj.mem_EllPos_iff'.1 x.2
  rw [h1, ← Matrix.trace_fin_two, h2]
  exact h4

lemma ell_of_EllNeg {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} (x : S3.Conj.EllNeg M δ' t n) :
    ((x : S3.Conj.Mat) 0 0 + (x : S3.Conj.Mat) 1 1) ^ 2 < 4 * (x : S3.Conj.Mat).det := by
  obtain ⟨h1, h2, -, h4, -, -⟩ := S3.Conj.mem_EllNeg_iff'.1 x.2
  rw [h1, ← Matrix.trace_fin_two, h2]
  exact h4

/-- **Elliptic classes with `c > 0`:** `∫_{Γ₁\ℍ} Σ_{γ ∈ EllPos} φ_γ = ellCount · I(ρ)`. -/
theorem ellPos_unfold {M : ℕ} [NeZero M] (hM : 3 ≤ M) (m : ℕ) (hm : 1 ≤ m) (δ' : ZMod M) (t : ℤ)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun z => ∑' x : S3.Conj.EllPos M δ' t n, phiG (m + 2) x z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : S3.Conj.EllPos M δ' t n, phiG (m + 2) x z =
        ((S3.ellCount M δ' t n : ℚ) : ℂ) * orbI m (ellRho t n) := by
  have := S3.Conj.finite_EllPos_quot (M := M) δ' t n
  have hI : ∀ x : S3.Conj.EllPos M δ' t n, ∫ z, phiG (m + 2) (x : S3.Conj.Mat) z = orbI m (ellRho t n) := by
    intro x
    obtain ⟨h1, h2, h3, -, -, -⟩ := S3.Conj.mem_EllPos_iff'.1 x.2
    rw [integral_phiG_ell _ (ell_of_EllPos x), sgnRho, if_pos h3, h1, ← Matrix.trace_fin_two, h2]
  have hsum := summable_phiG_sub (M := M) (m + 2) (by omega) (n := (n : ℤ)) (by exact_mod_cast hn) δ'
    (X := S3.Conj.EllPos M δ' t n) Subtype.val Subtype.val_injective (fun x => by
      obtain ⟨h1, -, -, -, h5, h6⟩ := S3.Conj.mem_EllPos_iff'.1 x.2
      exact ⟨h1, h6, h5⟩)
  obtain ⟨h1, h2⟩ := class_unfold_const hM (m + 2) (X := S3.Conj.EllPos M δ' t n) Subtype.val
    (fun h γ => rfl) finite_stab_EllPos hsum (fun x => integrable_phiG_ell _ (ell_of_EllPos x) m) _ hI
  rw [S3.Conj.classSum_EllPos] at h2
  exact ⟨h1, h2⟩

/-- **Elliptic classes with `c < 0`:** `∫_{Γ₁\ℍ} Σ_{γ ∈ EllNeg} φ_γ = ellCount · I(conj ρ)`. -/
theorem ellNeg_unfold {M : ℕ} [NeZero M] (hM : 3 ≤ M) (m : ℕ) (hm : 1 ≤ m) (δ' : ZMod M) (t : ℤ)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun z => ∑' x : S3.Conj.EllNeg M δ' t n, phiG (m + 2) x z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : S3.Conj.EllNeg M δ' t n, phiG (m + 2) x z =
        ((S3.ellCount M δ' t n : ℚ) : ℂ) * orbI m (conj (ellRho t n)) := by
  have := S3.Conj.finite_EllNeg_quot M δ' t n
  have hI : ∀ x : S3.Conj.EllNeg M δ' t n,
      ∫ z, phiG (m + 2) (x : S3.Conj.Mat) z = orbI m (conj (ellRho t n)) := by
    intro x
    obtain ⟨h1, h2, h3, -, -, -⟩ := S3.Conj.mem_EllNeg_iff'.1 x.2
    rw [integral_phiG_ell _ (ell_of_EllNeg x), sgnRho, if_neg (lt_asymm h3), h1, ← Matrix.trace_fin_two, h2]
  have hsum := summable_phiG_sub (M := M) (m + 2) (by omega) (n := (n : ℤ)) (by exact_mod_cast hn) δ'
    (X := S3.Conj.EllNeg M δ' t n) Subtype.val Subtype.val_injective (fun x => by
      obtain ⟨h1, -, -, -, h5, h6⟩ := S3.Conj.mem_EllNeg_iff'.1 x.2
      exact ⟨h1, h6, h5⟩)
  obtain ⟨h1, h2⟩ := class_unfold_const hM (m + 2) (X := S3.Conj.EllNeg M δ' t n) Subtype.val
    (fun h γ => rfl) finite_stab_EllNeg hsum (fun x => integrable_phiG_ell _ (ell_of_EllNeg x) m) _ hI
  rw [S3.Conj.classSum_EllNeg] at h2
  exact ⟨h1, h2⟩

end RamanujanPetersson.EllTerm


