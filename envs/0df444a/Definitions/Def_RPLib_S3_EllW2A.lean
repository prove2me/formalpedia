-- Prove2me | Definitions.Def_RPLib_S3_EllW2A
-- name    : RPLib_S3_EllW2A
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:26:07.288411+00:00
-- url     : https://prove2.me/theorems/41158c95-5a71-4093-b9f0-1231edbc4b23
-- title:
--   The Eichler-Selberg trace formula in weight two: elliptic and scalar terms at weight two
-- statement:
--   Elliptic and scalar terms at weight two.
--
--   At `k = 2` the elliptic class sums `Σ_γ φ(γ z)` are Poincaré series of exponent one and need not converge at every
--   `z`; they converge for almost every `z ∈ Γ₁(M)\ℍ` (Tonelli), which is all the unfolding needs.
--
--   * `ae_summable_norm_orbit`, `class_unfold_ae`, `class_unfold_const_ae`: unfolding of a `Γ₁(M)`-stable family with
--     finitely many classes for any conjugation-invariant `Φ`, assuming only integrability of each orbital integrand.
--   * `ellPos_unfold'`, `ellNeg_unfold'` (every `m`), `ellPos_norm_int`, `ellNeg_norm_int`.
--   * `tsum_ell_split`: partition of an elliptic sum over `Δ` by trace and sign of `c`.
--   * `ellPart_eq_ae`, `ellPart_integral'`, `ell_trace_term'` (`2 ≤ k`), `scal_trace_term'` (`2 ≤ k`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTermD

/-!
# S3-ES-Wt2 (O5, part A): elliptic and scalar terms at weight two

At `k = 2` the elliptic class sums `Σ_γ φ(γ z)` are Poincaré series of exponent one and need not converge at every
`z`; they converge for almost every `z ∈ Γ₁(M)\ℍ` (Tonelli), which is all the unfolding needs.

* `ae_summable_norm_orbit`, `class_unfold_ae`, `class_unfold_const_ae`: unfolding of a `Γ₁(M)`-stable family with
  finitely many classes for any conjugation-invariant `Φ`, assuming only integrability of each orbital integrand.
* `ellPos_unfold'`, `ellNeg_unfold'` (every `m`), `ellPos_norm_int`, `ellNeg_norm_int`.
* `tsum_ell_split`: partition of an elliptic sum over `Δ` by trace and sign of `c`.
* `ellPart_eq_ae`, `ellPart_integral'`, `ell_trace_term'` (`2 ≤ k`), `scal_trace_term'` (`2 ≤ k`).
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

variable {M : ℕ}

/-! ## Part 1: a.e. convergence of orbit sums -/

theorem ae_summable_norm_orbit (hM : 3 ≤ M) {Φ : ℍ → ℂ} (hΦ : Integrable Φ) :
    ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
      Summable fun γ : Gamma1 M => ‖Φ ((γ : SL(2, ℤ)) • z)‖ := by
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
  have hae : ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
      ∑' γ : Gamma1 M, ‖Φ ((γ : SL(2, ℤ)) • z)‖ₑ < ⊤ := by
    refine ae_lt_top' (AEMeasurable.ennreal_tsum fun γ => (hmeas γ).enorm) ?_
    rw [lintegral_tsum fun γ => (hmeas γ).enorm]
    exact hlin
  filter_upwards [hae] with z hz
  have h1 : Summable fun γ : Gamma1 M => ‖Φ ((γ : SL(2, ℤ)) • z)‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [enorm_eq_nnnorm] using hz.ne
  simpa only [coe_nnnorm] using NNReal.summable_coe.2 h1

/-! ## Part 2: unfolding without pointwise convergence -/

lemma summable_orbit_of_group {G X : Type*} [Group G] [MulAction G X] (x0 : X) {F : X → ℝ}
    (hF : Summable fun γ : G => F (γ⁻¹ • x0)) : Summable fun y : MulAction.orbit G x0 => F y := by
  let pr : G → MulAction.orbit G x0 := fun γ => ⟨γ⁻¹ • x0, MulAction.mem_orbit x0 γ⁻¹⟩
  have hpr : Function.Surjective pr := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    refine ⟨γ⁻¹, Subtype.ext ?_⟩
    show γ⁻¹⁻¹ • x0 = γ • x0
    rw [inv_inv]
  refine (hF.comp_injective (Function.injective_surjInv hpr)).congr fun y => ?_
  have h := congrArg Subtype.val (Function.surjInv_eq hpr y)
  exact congrArg F h

lemma Phi_orbit {X : Type*} [MulAction (Gamma1 M) X] (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    (Φ : S3.Conj.Mat → ℍ → ℂ)
    (hΦ : ∀ (h : SL(2, ℤ)) (g : S3.Conj.Mat) (z : ℍ), Φ (S3.Conj.conj h g) (h • z) = Φ g z)
    (x0 : X) (γ : Gamma1 M) (z : ℍ) :
    Φ (val (γ • x0)) z = Φ (val x0) (((γ⁻¹ : Gamma1 M) : SL(2, ℤ)) • z) := by
  rw [hval, ← hΦ (γ : SL(2, ℤ)) (val x0) (((γ⁻¹ : Gamma1 M) : SL(2, ℤ)) • z), Subgroup.coe_inv,
    smul_inv_smul]

lemma tsum_orbit_Phi {X : Type*} [MulAction (Gamma1 M) X] (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    (Φ : S3.Conj.Mat → ℍ → ℂ)
    (hΦ : ∀ (h : SL(2, ℤ)) (g : S3.Conj.Mat) (z : ℍ), Φ (S3.Conj.conj h g) (h • z) = Φ g z)
    (x0 : X) [Finite (MulAction.stabilizer (Gamma1 M) x0)] (z : ℍ)
    (hs : Summable fun y : MulAction.orbit (Gamma1 M) x0 => Φ (val y) z) :
    ∑' y : MulAction.orbit (Gamma1 M) x0, Φ (val y) z =
      (Nat.card (MulAction.stabilizer (Gamma1 M) x0) : ℂ)⁻¹ *
        ∑' γ : Gamma1 M, Φ (val x0) ((γ : SL(2, ℤ)) • z) := by
  obtain ⟨-, h⟩ := tsum_orbit (G := Gamma1 M) x0 (F := fun y => Φ (val y) z) hs
  have hN : (Nat.card (MulAction.stabilizer (Gamma1 M) x0) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have h2 : ∑' γ : Gamma1 M, Φ (val (γ • x0)) z =
      ∑' γ : Gamma1 M, Φ (val x0) ((γ : SL(2, ℤ)) • z) := by
    rw [← (Equiv.inv (Gamma1 M)).tsum_eq]
    refine tsum_congr fun γ => ?_
    simp only [Equiv.inv_apply]
    rw [Phi_orbit val hval Φ hΦ x0 γ⁻¹ z, inv_inv]
  rw [h2] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **Unfolding, a.e. form**: no pointwise summability hypothesis. -/
theorem class_unfold_ae (hM : 3 ≤ M) {X : Type*} [MulAction (Gamma1 M) X] (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    (Φ : S3.Conj.Mat → ℍ → ℂ)
    (hΦ : ∀ (h : SL(2, ℤ)) (g : S3.Conj.Mat) (z : ℍ), Φ (S3.Conj.conj h g) (h • z) = Φ g z)
    [Finite (MulAction.orbitRel.Quotient (Gamma1 M) X)]
    (hstab : ∀ x : X, Finite (MulAction.stabilizer (Gamma1 M) x))
    (hint : ∀ x : X, Integrable (Φ (val x))) :
    (∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), Summable fun x : X => ‖Φ (val x) z‖) ∧
      IntegrableOn (fun z => ∑' x : X, Φ (val x) z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : X, Φ (val x) z =
        ∑ᶠ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
          (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ * ∫ z, Φ (val C.out) z := by
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient (Gamma1 M) X)
  have hae : ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), ∀ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
      Summable fun γ : Gamma1 M => ‖Φ (val C.out) ((γ : SL(2, ℤ)) • z)‖ :=
    ae_all_iff.2 fun C => ae_summable_norm_orbit hM (hint C.out)
  have hsumN : ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), Summable fun x : X => ‖Φ (val x) z‖ := by
    filter_upwards [hae] with z hz
    rw [← (sigmaOrbits (Gamma1 M) X).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun C => ?_, Summable.of_finite⟩
    show Summable fun y : MulAction.orbit (Gamma1 M) C.out => ‖Φ (val (y : X)) z‖
    refine summable_orbit_of_group C.out (F := fun y => ‖Φ (val y) z‖) ((hz C).congr fun γ => ?_)
    show ‖Φ (val C.out) ((γ : SL(2, ℤ)) • z)‖ = ‖Φ (val (γ⁻¹ • C.out)) z‖
    rw [Phi_orbit val hval Φ hΦ C.out γ⁻¹ z, inv_inv]
  have hpt : (fun z => ∑' x : X, Φ (val x) z) =ᵐ[volume.restrict (fdom (Gamma1 M))] fun z =>
      ∑ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
        (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ *
          ∑' γ : Gamma1 M, Φ (val C.out) ((γ : SL(2, ℤ)) • z) := by
    filter_upwards [hsumN] with z hzN
    have hz : Summable fun x : X => Φ (val x) z := hzN.of_norm
    have hs : Summable fun c : (Σ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
        MulAction.orbit (Gamma1 M) C.out) => Φ (val c.2.1) z :=
      ((sigmaOrbits (Gamma1 M) X).summable_iff (f := fun x => Φ (val x) z)).2 hz
    rw [← (sigmaOrbits (Gamma1 M) X).tsum_eq (fun x => Φ (val x) z)]
    show ∑' c : (Σ C : MulAction.orbitRel.Quotient (Gamma1 M) X, MulAction.orbit (Gamma1 M) C.out),
      Φ (val c.2.1) z = _
    rw [hs.tsum_sigma, tsum_fintype]
    refine Finset.sum_congr rfl fun C _ => ?_
    have := hstab C.out
    exact tsum_orbit_Phi val hval Φ hΦ C.out z (hz.subtype _)
  have hI : ∀ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
      IntegrableOn (fun z => (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ *
        ∑' γ : Gamma1 M, Φ (val C.out) ((γ : SL(2, ℤ)) • z)) (fdom (Gamma1 M)) :=
    fun C => (integrableOn_fdom_tsum hM (hint C.out)).const_mul _
  have hIs : IntegrableOn (fun z => ∑ C : MulAction.orbitRel.Quotient (Gamma1 M) X,
      (Nat.card (MulAction.stabilizer (Gamma1 M) C.out) : ℂ)⁻¹ *
        ∑' γ : Gamma1 M, Φ (val C.out) ((γ : SL(2, ℤ)) • z)) (fdom (Gamma1 M)) :=
    integrable_finsetSum Finset.univ fun C _ => hI C
  refine ⟨hsumN, Integrable.congr hIs hpt.symm, ?_⟩
  rw [integral_congr_ae hpt, integral_finsetSum Finset.univ fun C _ => hI C, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [integral_const_mul, integral_fdom_tsum hM (hint C.out)]

theorem class_unfold_const_ae (hM : 3 ≤ M) {X : Type*} [MulAction (Gamma1 M) X] (val : X → S3.Conj.Mat)
    (hval : ∀ (h : Gamma1 M) (x : X), val (h • x) = S3.Conj.conj (h : SL(2, ℤ)) (val x))
    (Φ : S3.Conj.Mat → ℍ → ℂ)
    (hΦ : ∀ (h : SL(2, ℤ)) (g : S3.Conj.Mat) (z : ℍ), Φ (S3.Conj.conj h g) (h • z) = Φ g z)
    [Finite (MulAction.orbitRel.Quotient (Gamma1 M) X)]
    (hstab : ∀ x : X, Finite (MulAction.stabilizer (Gamma1 M) x))
    (hint : ∀ x : X, Integrable (Φ (val x))) (I : ℂ) (hI : ∀ x : X, ∫ z, Φ (val x) z = I) :
    (∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), Summable fun x : X => ‖Φ (val x) z‖) ∧
      IntegrableOn (fun z => ∑' x : X, Φ (val x) z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : X, Φ (val x) z = ((S3.Conj.classSum (Gamma1 M) X : ℚ) : ℂ) * I := by
  obtain ⟨h0, h1, h2⟩ := class_unfold_ae hM val hval Φ hΦ hstab hint
  refine ⟨h0, h1, ?_⟩
  rw [h2]
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient (Gamma1 M) X)
  rw [S3.Conj.classSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [hI]
  push_cast
  ring

/-! ## Part 3: the elliptic families for every `m` -/

theorem ellPos_unfold' [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    (∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
        Summable fun x : S3.Conj.EllPos M δ' t n => ‖phiG (m + 2) x z‖) ∧
      IntegrableOn (fun z => ∑' x : S3.Conj.EllPos M δ' t n, phiG (m + 2) x z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : S3.Conj.EllPos M δ' t n, phiG (m + 2) x z =
        ((S3.ellCount M δ' t n : ℚ) : ℂ) * orbI m (ellRho t n) := by
  have := S3.Conj.finite_EllPos_quot (M := M) δ' t n
  have hI : ∀ x : S3.Conj.EllPos M δ' t n, ∫ z, phiG (m + 2) (x : S3.Conj.Mat) z = orbI m (ellRho t n) := by
    intro x
    obtain ⟨h1, h2, h3, -, -, -⟩ := S3.Conj.mem_EllPos_iff'.1 x.2
    rw [integral_phiG_ell _ (ell_of_EllPos x), sgnRho, if_pos h3, h1, ← Matrix.trace_fin_two, h2]
  obtain ⟨h0, h1, h2⟩ := class_unfold_const_ae hM (X := S3.Conj.EllPos M δ' t n) Subtype.val
    (fun h γ => rfl) (phiG (m + 2)) (phiG_conj (m + 2)) finite_stab_EllPos
    (fun x => integrable_phiG_ell _ (ell_of_EllPos x) m) _ hI
  rw [S3.Conj.classSum_EllPos] at h2
  exact ⟨h0, h1, h2⟩

theorem ellNeg_unfold' [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    (∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
        Summable fun x : S3.Conj.EllNeg M δ' t n => ‖phiG (m + 2) x z‖) ∧
      IntegrableOn (fun z => ∑' x : S3.Conj.EllNeg M δ' t n, phiG (m + 2) x z) (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ∑' x : S3.Conj.EllNeg M δ' t n, phiG (m + 2) x z =
        ((S3.ellCount M δ' t n : ℚ) : ℂ) * orbI m (conj (ellRho t n)) := by
  have := S3.Conj.finite_EllNeg_quot M δ' t n
  have hI : ∀ x : S3.Conj.EllNeg M δ' t n,
      ∫ z, phiG (m + 2) (x : S3.Conj.Mat) z = orbI m (conj (ellRho t n)) := by
    intro x
    obtain ⟨h1, h2, h3, -, -, -⟩ := S3.Conj.mem_EllNeg_iff'.1 x.2
    rw [integral_phiG_ell _ (ell_of_EllNeg x), sgnRho, if_neg (lt_asymm h3), h1, ← Matrix.trace_fin_two, h2]
  obtain ⟨h0, h1, h2⟩ := class_unfold_const_ae hM (X := S3.Conj.EllNeg M δ' t n) Subtype.val
    (fun h γ => rfl) (phiG (m + 2)) (phiG_conj (m + 2)) finite_stab_EllNeg
    (fun x => integrable_phiG_ell _ (ell_of_EllNeg x) m) _ hI
  rw [S3.Conj.classSum_EllNeg] at h2
  exact ⟨h0, h1, h2⟩

/-- The norm sums over an elliptic family are integrable on `Γ₁(M)\ℍ` (domination for `s → 0`). -/
theorem ellPos_norm_int [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    IntegrableOn (fun z => ∑' x : S3.Conj.EllPos M δ' t n, ‖phiG (m + 2) x z‖) (fdom (Gamma1 M)) := by
  have := S3.Conj.finite_EllPos_quot (M := M) δ' t n
  obtain ⟨-, h1, -⟩ := class_unfold_ae hM (X := S3.Conj.EllPos M δ' t n) Subtype.val (fun h γ => rfl)
    (fun g z => ((‖phiG (m + 2) g z‖ : ℝ) : ℂ)) (fun h g z => by simp only [phiG_conj])
    finite_stab_EllPos (fun x => (integrable_phiG_ell _ (ell_of_EllPos x) m).norm.ofReal)
  have h2 := Integrable.re h1
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

theorem ellNeg_norm_int [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    IntegrableOn (fun z => ∑' x : S3.Conj.EllNeg M δ' t n, ‖phiG (m + 2) x z‖) (fdom (Gamma1 M)) := by
  have := S3.Conj.finite_EllNeg_quot M δ' t n
  obtain ⟨-, h1, -⟩ := class_unfold_ae hM (X := S3.Conj.EllNeg M δ' t n) Subtype.val (fun h γ => rfl)
    (fun g z => ((‖phiG (m + 2) g z‖ : ℝ) : ℂ)) (fun h g z => by simp only [phiG_conj])
    finite_stab_EllNeg (fun x => (integrable_phiG_ell _ (ell_of_EllNeg x) m).norm.ofReal)
  have h2 := Integrable.re h1
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

/-! ## Part 4: the elliptic part at every weight `k ≥ 2` -/

/-- Partition of an elliptic sum over `Δ` by trace and sign of `c`, given summability on each family. -/
theorem tsum_ell_split (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (f : S3.Conj.Mat → ℂ)
    (hsP : ∀ i : ℕ, Summable fun x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n => f x)
    (hsN : ∀ i : ℕ, Summable fun x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n => f x) :
    ∑' g : DeltaSet M n δ', (if ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 <
        4 * (g : S3.Conj.Mat).det then f g else 0) =
      ∑ i ∈ Finset.range (4 * n + 1),
        (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, f x +
          ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, f x) := by
  have hsP' : ∀ i : ℕ, Summable ((S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n).indicator f) :=
    fun i => summable_subtype_iff_indicator.1 (hsP i)
  have hsN' : ∀ i : ℕ, Summable ((S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n).indicator f) :=
    fun i => summable_subtype_iff_indicator.1 (hsN i)
  rw [tsum_subtype (DeltaSet M n δ') (fun g : S3.Conj.Mat =>
      if (g 0 0 + g 1 1) ^ 2 < 4 * g.det then f g else 0),
    tsum_congr (ind_eq δ' hn f),
    Summable.tsum_finsetSum (fun (i : ℕ) _ => (hsP' i).add (hsN' i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_add (hsP' i) (hsN' i), ← tsum_subtype, ← tsum_subtype]

theorem ellPart_eq_ae [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) :
    ellPart (m + 2) M n δ' =ᵐ[volume.restrict (fdom (Gamma1 M))] fun z => ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z) := by
  have hP := ae_all_iff.2 fun i : ℕ => (ellPos_unfold' hM m δ' ((i : ℤ) - 2 * n) n).1
  have hN := ae_all_iff.2 fun i : ℕ => (ellNeg_unfold' hM m δ' ((i : ℤ) - 2 * n) n).1
  filter_upwards [hP, hN] with z hzP hzN
  rw [ellPart]
  exact tsum_ell_split δ' hn (fun g => phiG (m + 2) g z) (fun i => (hzP i).of_norm)
    (fun i => (hzN i).of_norm)

/-- **Elliptic unfolding at every `m` (`k = m + 2 ≥ 2`).** -/
theorem ellPart_integral' [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (ellPart (m + 2) M n δ') (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ellPart (m + 2) M n δ' z =
        ∑ i ∈ Finset.range (4 * n + 1), ((S3.ellCount M δ' ((i : ℤ) - 2 * n) n : ℚ) : ℂ) *
          (orbI m (ellRho ((i : ℤ) - 2 * n) n) + orbI m (conj (ellRho ((i : ℤ) - 2 * n) n))) := by
  have hae := ellPart_eq_ae hM m δ' hn
  have hint : ∀ i ∈ Finset.range (4 * n + 1), Integrable (fun z =>
      ∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z)
      (volume.restrict (fdom (Gamma1 M))) := fun i _ =>
    (ellPos_unfold' hM m δ' _ n).2.1.add (ellNeg_unfold' hM m δ' _ n).2.1
  refine ⟨Integrable.congr (integrable_finsetSum _ hint) hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add (ellPos_unfold' hM m δ' ((i : ℤ) - 2 * n) n).2.1
      (ellNeg_unfold' hM m δ' ((i : ℤ) - 2 * n) n).2.1,
    (ellPos_unfold' hM m δ' ((i : ℤ) - 2 * n) n).2.2, (ellNeg_unfold' hM m δ' ((i : ℤ) - 2 * n) n).2.2,
    mul_add]

/-- **Elliptic term, `k ≥ 2`:** with `δ' = n δ`, `n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} ellPart = ellG1 M k n δ`. -/
theorem ell_trace_term' {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 2 ≤ k) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (ellPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M)) (fdom (Gamma1 M)) ∧
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
          ∫ z in fdom (Gamma1 M), ellPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z =
        ((S3.ellG1 M k n (δ : ZMod M) : ℚ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨hI, hval⟩ := ellPart_integral' hM m ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn
  refine ⟨hI, ?_⟩
  have hu : IsUnit ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) := Units.isUnit _
  have hv : IsUnit ((δ : ZMod M)⁻¹) := by rw [ZMod.inv_coe_unit]; exact Units.isUnit _
  have he : ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) * (δ : ZMod M)⁻¹ = n := by
    rw [ZMod.inv_coe_unit, Units.val_mul, coe_unitOf hnM, mul_assoc, Units.mul_inv, mul_one]
  rw [hval, S3.ellG1, Finset.mul_sum, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases ht : ((i : ℤ) - 2 * n) ^ 2 < 4 * (n : ℤ)
  · rw [ellCount_adj _ _ _ n hu hv he]
    have hN := ell_norm m (t := (i : ℤ) - 2 * n) (n := (n : ℤ)) (by exact_mod_cast hn) ht
    push_cast at hN
    rw [mul_left_comm, hN]
    ring
  · have h4 : 4 * (n : ℤ) ≤ ((i : ℤ) - 2 * n) ^ 2 := not_lt.1 ht
    rw [ellCount_eq_zero _ h4, ellCount_eq_zero _ h4]
    simp

/-- **Scalar term, `k ≥ 2`.** -/
theorem scal_trace_term' {M : ℕ} [NeZero M] {k : ℕ} (hk : 2 ≤ k) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (scalPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M)) (fdom (Gamma1 M)) ∧
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
          ∫ z in fdom (Gamma1 M), scalPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z =
        ((pmSL (Gamma1 M)).index : ℂ) * scalTrace M k n (δ : ZMod M) := by
  obtain ⟨hint, hval⟩ := scal_integral (M := M) k ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn
  refine ⟨hint, ?_⟩
  rw [hval, scalVal, add_mul, mul_add, scalTrace]
  set s := Nat.sqrt n with hs
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast (Nat.sqrt_pos.2 hn).ne'
  by_cases hsq : s * s = n
  · rw [if_pos hsq]
    have h1 : (s : ℤ) * s = n := by exact_mod_cast hsq
    have h2 : (-(s : ℤ)) * (-(s : ℤ)) = n := by rw [neg_mul_neg]; exact h1
    rw [scalTerm_val hk hs0 h1, scalTerm_val hk (neg_ne_zero.2 hs0) h2]
    have hu : IsUnit (s : ZMod M) :=
      (ZMod.isUnit_iff_coprime s M).2 (Nat.Coprime.coprime_dvd_left (Dvd.intro s hsq) hnM)
    have hδ' : ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) = (s : ZMod M) * s * δ := by
      rw [Units.val_mul, coe_unitOf hnM, ← hsq]; push_cast; ring
    have c1 : (((s : ℤ) : ZMod M) = (s : ZMod M) * s * δ) ↔ (s : ZMod M) * δ = 1 := by
      push_cast
      constructor
      · intro h; apply hu.mul_left_cancel; rw [mul_one, ← mul_assoc]; exact h.symm
      · intro h; rw [mul_assoc, h, mul_one]
    have c2 : (((-(s : ℤ) : ℤ)) : ZMod M) = (s : ZMod M) * s * δ ↔ (s : ZMod M) * δ = -1 := by
      push_cast
      constructor
      · intro h; apply hu.mul_left_cancel; rw [mul_neg_one, ← mul_assoc]; exact h.symm
      · intro h; rw [mul_assoc, h, mul_neg_one]
    rw [hδ']
    simp only [c1, c2]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    split_ifs <;> push_cast <;> ring
  · rw [if_neg hsq, mul_zero]
    have h1 : ¬ ((s : ℤ) * s = n) := fun h => hsq (by exact_mod_cast h)
    have h2 : ¬ ((-(s : ℤ)) * (-(s : ℤ)) = n) := by rw [neg_mul_neg]; exact h1
    rw [scalTerm, if_neg (fun h => h1 h.1), scalTerm, if_neg (fun h => h2 h.1)]
    simp

end RamanujanPetersson.EllW2


