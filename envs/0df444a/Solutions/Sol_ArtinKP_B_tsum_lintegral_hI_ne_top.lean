-- Prove2me | solution 1 for ArtinKP.B.tsum_lintegral_hI_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:18.817143+00:00
-- url     : https://prove2.me/submissions/bb169cc3-453d-4e5e-aa46-39103f4509a5

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_S2_cubicExt_eq_zero_iff

section
-- module Solutions.Artin.T12.L2B_Quot
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `I R ∩ 𝓞 = I` for an ideal `I` coprime to `𝔪`. -/
lemma mem_of_map_mem (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) : a ∈ I := by
  set φ := algebraMap (𝓞 F) (SInt 𝔪)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hxy
    simp only [φ, C3I.coe_alg] at this
    exact IsFractionRing.injective (𝓞 F) F this
  -- the predicate
  have hQ : ∀ x ∈ I.map φ, ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ i ∈ I, φ w * x = φ i := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i0, hi0, rfl⟩ := hx
      exact ⟨0, fun w _ => ⟨w * i0, I.mul_mem_left _ hi0, by rw [map_mul]⟩⟩
    | zero => exact ⟨0, fun w _ => ⟨0, I.zero_mem, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨max N1 N2, fun w hw => ?_⟩
      obtain ⟨i1, hi1, e1⟩ := h1 w (Ideal.pow_le_pow_right (le_max_left _ _) hw)
      obtain ⟨i2, hi2, e2⟩ := h2 w (Ideal.pow_le_pow_right (le_max_right _ _) hw)
      exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [mul_add, e1, e2, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Nr, hNr⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
      refine ⟨Nr + Nx, fun w hw => ?_⟩
      rw [pow_add] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro w1 hw1 w2 hw2
        obtain ⟨c, hc⟩ := hNr w1 hw1
        obtain ⟨i, hi, ei⟩ := hNx w2 hw2
        refine ⟨c * i, I.mul_mem_left _ hi, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← hc, ← ei]; ring
      · rintro w1 w2 ⟨i1, hi1, e1⟩ ⟨i2, hi2, e2⟩
        exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [map_add, add_mul, e1, e2, map_add]⟩
  obtain ⟨N, hN⟩ := hQ _ ha
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨i, hi, ei⟩ := hN w hw
  have : w * a = i := hinj (by rw [map_mul, ei])
  have ha' : a = u * a + w * a := by rw [← add_mul, huw, one_mul]
  rw [ha', this]
  exact I.add_mem (I.mul_mem_right _ hu) hi

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B7_Link
/-! # B7_Link: the Gauss sums over `R = SInt 𝔪` and the normalization of the frozen statement

* `sAdd 𝔪 h𝔪 : AddData (SInt 𝔪) F` is `sAddChar 𝔪` (additive on all of `F`: `sAddChar_add_all`;
  trivial on `R`), so `gauss S (sAdd 𝔪 h𝔪) ν c = ∑_{d mod c} (d/c)⁻¹ sAddChar 𝔪 (ν d / c)`
  (`gauss_sAdd`).
* `finite_quot_span`: `R ⧸ (c)` is finite for `c ≠ 0`.
* At a good exterior prime `P` (`C3I.Good 𝔪 v`, automatic for `SmallPrimesDvd N₀ 𝔪`,
  `N₀ ≥ C3I.cutN F`) with `π = g.gen P` and a symbol with `(d/π) = χ_P(d)²`:
  `gaussP_one_eq_tau : g₁(π) = tau P 2 = conj (√q γ₂(P))`,
  `gaussP_two_eq_tau : g₂(π) = tau P 4 = √q γ₂(P)`, `γ₂(P) = gaussPhase g 2 P`,
  `gaussP_one_mul_two : g₁ g₂ = N P`, and the complete table `gauss_gen_table` in the form of
  `B7_System.tab` with `G = (ν₀/π) tau P 2`, `G' = (ν₀/π)² tau P 4`, `G G' = N P`, `conj G = G'`.
* `theta_ratio`: the solution of the formal system at `x₀ = q^{-4/3}` gives
  `q^{-1/3} C₁ = (ν₀/π)² · Wv P 1 · C₀` with `Wv P 1 = q^{-1/2} gaussPhase g 2 P` exactly as in the
  frozen statement (and `Wv P 0 = 1`, `Wv P 2 = 0 ↔ Ψ₂ = 0`).
-/

open NumberField IsDedekindDomain

namespace ArtinKP.B7

open ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The additive character -/

/-- `R ⧸ (c)` is finite for `c ≠ 0`. -/
theorem finite_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Finite (SInt 𝔪 ⧸ Ideal.span {c}) := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h; exact hb0 (by simpa using h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hcF hab.symm
  have hI : Ideal.span ({a} : Set (𝓞 F)) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
  have hle : 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Ideal.span {c} := by
    rw [← hmap, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton]
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) b, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, ← hab]
    show algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b
    field_simp
  have := L2B.finite_quot_map (𝔪 := 𝔪) 𝔄 hE.1 hE.2
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B_Def
/-!
# WP-B0, part 1: the Eisenstein series of a twisted section

`eis Ψ s Q = ∑_{p ∈ Row 𝔪 / U_S} Ψ_s(p) · I_p(Q)^s` for a twisted section `Ψ : TSection ι 𝔪`,
`s : ℂ`, `Q : X F`.

* Indexing type: `RowClass 𝔪 = MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪)`; the summand is
  evaluated at `Quotient.out` and shown independent of the representative (`term_smul`,
  `term_out_mk`) by the product formula for `S`-units (`Ninf_mul_absS`).
* `sPl 𝔪 : Finset (FinitePlace F)` is the set `S_f` in the form B1 uses; `X.sNorm (sPl 𝔪) = normS 𝔪`,
  `IsSInt (sPl 𝔪) = membership in SInt 𝔪`, `IsSUnit (sPl 𝔪) = units of SInt 𝔪`.
* `RowClass.ht q Q = ht_q(Q) = I_q(Q)/‖q‖`; `eis_eq_tsum_ht : eis Ψ s Q = ∑ Ψ̃_s(q) ht_q(Q)^s`.
* Convergence for `Re s > 2` from `B1.summable_sHt_rpow` / `B1.exists_summable_majorant_sHt`.
* Automorphy: `eis Ψ s (γ • Q) = eis (translate γ⁻¹ Ψ) s Q` for `γ ∈ SL₂(R)` (note the inverse).
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The places of `S_f` as finite places; `S`-integers and `S`-units -/

lemma mk_apply_eq (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    FinitePlace.mk v x = NumberField.HeightOneSpectrum.adicAbv F v x := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding]

lemma prod_sPl (f : FinitePlace F → ℝ) :
    ∏ v ∈ sPl 𝔪, f v = ∏ v ∈ CubicPkg.sFin 𝔪, f (FinitePlace.mk v) := by
  classical
  unfold sPl
  exact Finset.prod_image fun v _ v' _ h => FinitePlace.mk_eq_iff.mp h

theorem prod_sPl_eq_absS (x : F) : ∏ v ∈ sPl 𝔪, v x = absS 𝔪 x := by
  unfold absS
  rw [prod_sPl]
  simp only [mk_apply_eq]

lemma coe_sFin (h𝔪 : 𝔪 ≠ ⊥) :
    ((CubicPkg.sFin 𝔪 : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F)))
      = placesOf 𝔪 := by
  ext v
  simp [CubicPkg.mem_sFin h𝔪 v, placesOf]

/-- B1's `IsSInt (sPl 𝔪)` is membership in `R = SInt 𝔪`. -/
theorem isSInt_iff (h𝔪 : 𝔪 ≠ ⊥) (a : F) :
    IsSInt (sPl 𝔪) a ↔ a ∈ (placesOf 𝔪).integer F := by
  have h := isSInt_image_iff (CubicPkg.sFin 𝔪) a
  rw [coe_sFin h𝔪] at h
  exact h

theorem isSInt_coe (h𝔪 : 𝔪 ≠ ⊥) (a : SInt 𝔪) : IsSInt (sPl 𝔪) (a : F) :=
  (isSInt_iff h𝔪 _).mpr a.2

/-- Units of `R` are `S`-units in B1's sense. -/
theorem isSUnit_coe (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) : IsSUnit (sPl 𝔪) ((ε : SInt 𝔪) : F) := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  refine ⟨left_ne_zero_of_mul_eq_one h3, fun v hv => ?_⟩
  have h1 := isSInt_coe h𝔪 (ε : SInt 𝔪) v hv
  have h2 := isSInt_coe h𝔪 ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) v hv
  have h4 : v ((ε : SInt 𝔪) : F) * v (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, h3, map_one]
  have h5 : 0 ≤ v ((ε : SInt 𝔪) : F) := apply_nonneg v _
  nlinarith

/-! ### The product formula for `S`-units -/

theorem Ninf_pos {x : F} (hx : x ≠ 0) : 0 < Ninf x :=
  Finset.prod_pos fun _ _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)

theorem Ninf_mul (x y : F) : Ninf (x * y) = Ninf x * Ninf y := by
  simp only [Ninf, map_mul, Finset.prod_mul_distrib]

/-- Product formula for an `S`-unit in B1's sense, any finite set `T` of finite places. -/
theorem Ninf_mul_prod_of_isSUnit [IsTotallyComplex F] (T : Finset (FinitePlace F)) {u : F}
    (hu : IsSUnit T u) : Ninf u * ∏ v ∈ T, v u = 1 := by
  have h2 : ∏ᶠ v : FinitePlace F, v u = ∏ v ∈ T, v u := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    exact hv (hu.2 v hvT)
  rw [← h2, X.finprod_finitePlace hu.1]
  exact mul_inv_cancel₀ (Ninf_pos hu.1).ne'

/-- **Product formula for `S`-units**: `N_∞(ε) · |ε|_{S_f} = 1` for `ε ∈ (SInt 𝔪)ˣ`
(WP-S open issue 7). -/
theorem Ninf_mul_absS [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) :
    Ninf ((ε : SInt 𝔪) : F) * absS 𝔪 ((ε : SInt 𝔪) : F) = 1 := by
  rw [← prod_sPl_eq_absS]
  exact Ninf_mul_prod_of_isSUnit _ (isSUnit_coe h𝔪 ε)

/-! ### Rows modulo `S`-units -/

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

/-! ### Height form (MATH2 §0.2) -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.K_Jacquet
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

lemma continuous_hyperbolicKernel (s : ℂ) : Continuous (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  apply Continuous.cpow
  · fun_prop
  · exact continuous_const
  · intro z
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z * archChar (-freq*z)) := by
  apply (hyperbolicKernel_integrable s hs).norm.mono'
  · have hchar : Continuous (fun z : ℂ => archChar (-freq*z)) := by
      unfold archChar; fun_prop
    exact ((continuous_hyperbolicKernel s).mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp only [norm_mul, archChar_norm, mul_one, le_refl])

/-! ## The Bessel form (ours, for `besselK`) -/

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_integrable (s ν : ℂ) (hs : 1 < s.re) {v : ℝ} (hv : 0 < v) :
    Integrable fun x : ℂ => ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s * archChar (-ν * x) := by
  simp_rw [height_cpow s hv, mul_assoc]
  refine Integrable.const_mul ?_ _
  have h := (sourceFourierKernel_integrable s (ν * v) hs).comp_smul
    (inv_ne_zero hv.ne' : (v⁻¹ : ℝ) ≠ 0)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Complex.real_smul, Complex.ofReal_inv]
  congr 2
  · ring
  · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_Jacquet
/-!
# WP-S, part 7: finite Jacquet functionals

`F_{S_f}/𝔩` is the discrete countable group `F/𝔩_M`, `𝔩_M = {x : Small M x}` (strong
approximation is not needed to *define* the functional).  For `f : F → ℂ` invariant under `𝔩_M`:

`jac ψ M f ν = vol(𝔩_M) · Σ_{u ∈ F/𝔩_M} f(u) · conj ψ(ν u)`   (`= ∫_{F_{S_f}} f(u) conj ψ(νu) du`),

`J_Φ(c; ν, s) = jac ψ M (u ↦ Φ_s(c, cu)) ν`, `λ_η(Φ_s; ν) = |η|^s J_Φ(η; ν, s)` (`lam`).

* `lam_bigCell`: `λ_η(Φ^{big}_{η,L}; ν) = vol(𝔩) conj ψ(ν t₀)` for `ν ∈ 𝔩^⊥`.
* `jac_eq_zero`: the functional vanishes when `ψ(ν ·)` is non-trivial on a lattice of periods.
* `norm_lam_le`: the uniform bound `|c|^σ |J_Φ(c; ν, s)| ≤ B·K_σ` (MATH2 §0.2), `K_σ = vol·Σ_u
  ∏_v max(1,|u|_v)^{-σ}`.
* `kir`, `xi_bound`: the bound for the Kirillov function (MATH2 §6.3 (K2), (K3)).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem out_spec {M : ℤ} (x : F) :
    ∃ h : F, Small 𝔪 M h ∧ (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out = x + h := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (lat 𝔪 M) x
  exact ⟨h.1, h.2, hh⟩

/-! ### The Kirillov function -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem kerA_pos {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    0 < kerA v x :=
  Finset.prod_pos fun w _ => div_pos (hv w) (by positivity [hv w])

/-! ### Shifted kernels -/

theorem integrable_kerA_rpow {σ : ℝ} (hσ : 1 < σ) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) : Integrable fun y : InfinitePlace F → ℂ => kerA v y ^ σ := by
  have h1 : ∀ w : InfinitePlace F,
      Integrable fun y : ℂ => (v w / (‖y‖ ^ 2 + v w ^ 2)) ^ σ := by
    intro w
    have h := (jacquet_integrable (σ : ℂ) 0 (by simpa using hσ) (hv w)).norm
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    have hp : 0 < v w / (‖y‖ ^ 2 + v w ^ 2) := by have := hv w; positivity
    simp only [norm_mul, archChar_norm, mul_one]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.ofReal_re]
  have h2 := Integrable.fintype_prod (μ := fun _ : InfinitePlace F => (volume : Measure ℂ)) h1
  rw [← volume_pi] at h2
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [kerA]
  rw [Real.finsetProd_rpow _ _ fun w _ => by have := hv w; positivity]

theorem kerInt_nonneg (σ : ℝ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) : 0 ≤ kerInt σ v :=
  integral_nonneg fun y => Real.rpow_nonneg (kerA_pos hv y).le _

theorem norm_hKer (A : ℂ) {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    ‖hKer A N e s v x‖ = ‖A‖ * N⁻¹ ^ s.re * kerA v (x + e) ^ s.re := by
  rw [hKer, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
    (mul_pos (inv_pos.mpr hN) (kerA_pos hv _)),
    Real.mul_rpow (inv_pos.mpr hN).le (kerA_pos hv _).le, mul_assoc]

/-- The `L¹` norm of a shifted kernel. -/
theorem lintegral_hKer (A : ℂ) {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) {s : ℂ}
    (hs : 1 < s.re) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ∫⁻ x : InfinitePlace F → ℂ, ‖hKer A N e s v x‖ₑ
      = ENNReal.ofReal (‖A‖ * N⁻¹ ^ s.re * kerInt s.re v) := by
  have hc : 0 ≤ ‖A‖ * N⁻¹ ^ s.re :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (inv_pos.mpr hN).le _)
  have h : ∀ x : InfinitePlace F → ℂ, ‖hKer A N e s v x‖ₑ
      = ENNReal.ofReal (‖A‖ * N⁻¹ ^ s.re)
        * (fun y : InfinitePlace F → ℂ => ENNReal.ofReal (kerA v y ^ s.re)) (x + e) := by
    intro x
    rw [← ofReal_norm, norm_hKer A hN e s hv, ENNReal.ofReal_mul hc]
  simp only [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right_eq_self (fun y : InfinitePlace F → ℂ => ENNReal.ofReal (kerA v y ^ s.re)) e,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_kerA_rpow hs hv)
      (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (kerA_pos hv y).le _),
    ← ENNReal.ofReal_mul hc]
  rfl

end ArtinKP.B
end
end

section
-- module Solutions.Artin.T12.T12B_Euler
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

theorem fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  haveI _iFF := ArtinPrimitiveRoots.T12B.fiber_finite (F := F)
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2B_Orth
/-!
# L2B_Orth: `#(R/𝔰R) = q_𝔰`, primitivity and orthogonality of `j ↦ e(j k / s)`

* `natCard_quot_eq`: `#(R/𝔰R) = N 𝔰` for exterior `𝔰`;
* `exists_primePow_not_mem`: `k ∉ 𝔰R` ⇒ `k ∉ P^a R` for a prime power `P^a ∣ 𝔰`;
* `exists_sAddChar_ne_one_gen`: primitivity of `j ↦ e(j k / s)` for `k ∉ 𝔰R`;
* `finsum_sAddChar`: `∑_{j mod 𝔰} e(j k / s) = q_𝔰 [k ∈ 𝔰R]`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

theorem natCard_quot_eq {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm 𝔞 := by
  have hbij : Function.Bijective (C3I.quotHom 𝔪 𝔞) := by
    refine ⟨?_, quotHom_surjective 𝔞 h𝔞.2⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [C3I.quotHom_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact mem_of_map_mem 𝔞 h𝔞.2 a hy
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Ideal.absNorm_apply, Submodule.cardQuot_apply]

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B_Norm
/-!
# WP-B, part 3: the norm of an `S`-integer

* `extOf h𝔪 hc`: the exterior ideal `𝔠 ⊂ 𝓞` with `𝔠R = cR`, for `c ∈ R ∖ 0`.
* `natCard_quot_span`: `#(R/cR) = N𝔠`.
* **Product formula** `Ninf_mul_absS_eq`: `N_∞(c) · |c|_{S_f} = #(R/cR)` for `c ∈ R ∖ 0`
  (class-number trick: `𝔠^h` is principal in `𝓞`).
* `summable_nrm_rpow`: `∑_{c ∈ (R∖0)/Rˣ} #(R/cR)^{-t} < ∞` for `t > 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem extOf_isExterior (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    IsExterior 𝔪 (extOf h𝔪 hc) := (exists_ext h𝔪 hc).choose_spec.1

theorem map_extOf (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    (extOf h𝔪 hc).map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c} :=
  (exists_ext h𝔪 hc).choose_spec.2

/-- `#(R/cR) = N𝔠`. -/
theorem natCard_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) = Ideal.absNorm (extOf h𝔪 hc) := by
  rw [← map_extOf h𝔪 hc]
  exact L2B.natCard_quot_eq (extOf_isExterior h𝔪 hc)

theorem natCard_quot_span_pos (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    0 < Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) := by
  rw [natCard_quot_span h𝔪 hc]
  exact Nat.pos_of_ne_zero fun h =>
    (extOf_isExterior h𝔪 hc).1 (Ideal.absNorm_eq_zero_iff.mp h)

theorem isExterior_pow {𝔄 : Ideal (𝓞 F)} (h : IsExterior 𝔪 𝔄) (n : ℕ) : IsExterior 𝔪 (𝔄 ^ n) :=
  ⟨pow_ne_zero n h.1,
    Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 h.2).pow_left)⟩

/-- A generator of an exterior ideal has `|a|_{S_f} = 1`. -/
theorem absS_of_span_exterior (h𝔪 : 𝔪 ≠ ⊥) {a : 𝓞 F} (h : IsExterior 𝔪 (Ideal.span {a})) :
    absS 𝔪 (a : F) = 1 := by
  refine absS_eq_one_of_val h𝔪 fun v hv => ?_
  rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro ha
  have h1 : Ideal.span {a} ⊔ 𝔪 ≤ v.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ha) hv
  rw [h.2] at h1
  exact v.isPrime.ne_top (top_le_iff.mp h1)

/-- **Product formula for `S`-integers**: `N_∞(c) · |c|_{S_f} = #(R/cR)`. -/
theorem Ninf_mul_absS_eq [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Ninf (c : F) * absS 𝔪 (c : F) = (Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) : ℝ) := by
  classical
  set 𝔄 := extOf h𝔪 hc with h𝔄
  have hE := extOf_isExterior h𝔪 hc
  have hmap := map_extOf h𝔪 hc
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hh0 : h ≠ 0 := Fintype.card_ne_zero
  -- `𝔄 ^ h` is principal
  have hmem : 𝔄 ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hE.1
  have hmem' : 𝔄 ^ h ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hE.1)
  have hpr : (𝔄 ^ h).IsPrincipal := by
    have e : (⟨𝔄 ^ h, hmem'⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨𝔄, hmem⟩ ^ h :=
      Subtype.ext rfl
    have h1 : ClassGroup.mk0 (⟨𝔄 ^ h, hmem'⟩ : nonZeroDivisors (Ideal (𝓞 F))) = 1 := by
      rw [e, map_pow, hh, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff hmem').mp h1
  obtain ⟨a, ha⟩ := hpr
  have ha' : 𝔄 ^ h = Ideal.span {a} := ha
  have hEa : IsExterior 𝔪 (Ideal.span {a}) := ha' ▸ isExterior_pow hE h
  have ha0 : a ≠ 0 := fun h0 => hEa.1 (by rw [h0]; simp)
  -- `c ^ h` is associated to `a`
  have hspan : Ideal.span {c ^ h} = Ideal.span {algebraMap (𝓞 F) (SInt 𝔪) a} := by
    rw [← Ideal.span_singleton_pow, ← hmap, ← Ideal.map_pow, ha', Ideal.map_span,
      Set.image_singleton]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have huF : (c : F) ^ h * ((u : SInt 𝔪) : F) = (a : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hu
    simpa using this
  -- the value at `a`
  have hNa : Ninf (a : F) = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
    rw [Ninf, X.prod_normSq_embedding, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int,
      Nat.cast_natAbs]
    push_cast
    rfl
  have hfa : Ninf (a : F) * absS 𝔪 (a : F) = (Ideal.absNorm 𝔄 : ℝ) ^ h := by
    rw [absS_of_span_exterior h𝔪 hEa, mul_one, hNa, ← ha', map_pow]
    push_cast
    rfl
  have hfu := Ninf_mul_absS h𝔪 u
  have hpow : (Ninf (c : F) * absS 𝔪 (c : F)) ^ h = (Ideal.absNorm 𝔄 : ℝ) ^ h := by
    rw [← hfa, ← huF, Ninf_mul, absS_mul, mul_pow, absS_pow]
    have e : Ninf ((c : F) ^ h) = Ninf (c : F) ^ h := by
      simp only [Ninf, map_pow, Finset.prod_pow]
    rw [e]
    linear_combination (-(Ninf (c : F) ^ h * absS 𝔪 (c : F) ^ h)) * hfu
  rw [natCard_quot_span h𝔪 hc]
  exact (pow_left_inj₀ (mul_nonneg (Ninf_pos hcF).le (absS_pos hcF).le)
    (Nat.cast_nonneg _) hh0).mp hpow

/-- `∑_{c ∈ (R∖0)/Rˣ} #(R/cR)^{-t} < ∞` for `t > 1`. -/
theorem summable_nrm_rpow (h𝔪 : 𝔪 ≠ ⊥) {t : ℝ} (ht : 1 < t) :
    Summable fun a : Cls (SInt 𝔪) =>
      (Nat.card (SInt 𝔪 ⧸ Ideal.span {rp a.1}) : ℝ) ^ (-t) := by
  let g : Cls (SInt 𝔪) → Ideal (𝓞 F) := fun a => extOf h𝔪 (rp_ne_zero a.2)
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : Ideal.span {rp a.1} = Ideal.span {rp b.1} := by
      rw [← map_extOf h𝔪 (rp_ne_zero a.2), ← map_extOf h𝔪 (rp_ne_zero b.2)]
      exact congrArg _ hab
    have h2 := Ideal.span_singleton_eq_span_singleton.mp h1
    apply Subtype.ext
    rw [← mk_rp a.1, ← mk_rp b.1]
    exact Associates.mk_eq_mk_iff_associated.mpr h2
  have h := (T12B.summable_absNorm_rpow (F := F) ht).comp_injective hinj
  refine h.congr fun a => ?_
  simp only [Function.comp, g]
  rw [natCard_quot_span h𝔪 (rp_ne_zero a.2)]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RF_SNorm
/-!
# WP-RF, part 1: summability of the `S_f`-norm series (stub S-1 of WP-S)

`summable_normS_one`: for `σ > 1`, `Σ_{u ∈ F/𝔩_M} ∏_{v ∣ 𝔪} max(1, |u|_v)^{-σ} < ∞`.

Route (WP-S): a finite set of elements of `F` whose pairwise differences have `v(x-y) ≤ exp(k_v)`
for `v ∈ S` and which are pairwise incongruent modulo `{v(x) ≤ exp(k_v - n_v)}` has at most
`∏_v q_v^{n_v}` elements (`card_le_of_separated`; induction on `Σ n_v`, each step maps into the
residue field `𝓞/v`).  Grouping the cosets by the depth vector of their representative gives the
bound `∏_v q_v^{|M|} (1 - q_v^{1-σ})⁻¹` for every finite partial sum.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.RF

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F]

/-- A "residue" map at `v`: integral elements with the same residue are congruent. -/
theorem exists_residue (v : HeightOneSpectrum (𝓞 F)) :
    ∃ r : F → 𝓞 F ⧸ v.asIdeal, ∀ x y : F, v.valuation F x ≤ 1 → v.valuation F y ≤ 1 →
      r x = r y → v.valuation F (x - y) < 1 := by
  classical
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  have key : ∀ x : F, v.valuation F x ≤ 1 →
      ∃ p : 𝓞 F × 𝓞 F, p.2 ∉ v.asIdeal ∧ x * algebraMap (𝓞 F) F p.2 = algebraMap (𝓞 F) F p.1 := by
    intro x hx
    obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨(n, d.1), d.2, h⟩
  refine ⟨fun x => if h : v.valuation F x ≤ 1 then
      Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).1
        / Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).2 else 0, ?_⟩
  intro x y hx hy hxy
  simp only [dif_pos hx, dif_pos hy] at hxy
  obtain ⟨hdx, ex⟩ := Classical.choose_spec (key x hx)
  obtain ⟨hdy, ey⟩ := Classical.choose_spec (key y hy)
  set nx := (Classical.choose (key x hx)).1
  set dx := (Classical.choose (key x hx)).2
  set ny := (Classical.choose (key y hy)).1
  set dy := (Classical.choose (key y hy)).2
  have hdx0 : Ideal.Quotient.mk v.asIdeal dx ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hdy0 : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [div_eq_div_iff hdx0 hdy0, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem] at hxy
  have h1 : v.valuation F (algebraMap (𝓞 F) F (nx * dy - ny * dx)) < 1 :=
    (v.valuation_lt_one_iff_mem _).mpr hxy
  have vdx : v.valuation F (algebraMap (𝓞 F) F dx) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdx
  have vdy : v.valuation F (algebraMap (𝓞 F) F dy) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdy
  have e : (x - y) * (algebraMap (𝓞 F) F dx * algebraMap (𝓞 F) F dy)
      = algebraMap (𝓞 F) F (nx * dy - ny * dx) := by
    rw [map_sub, map_mul, map_mul, ← ex, ← ey]; ring
  have := congrArg (v.valuation F) e
  rw [map_mul, map_mul, vdx, vdy, mul_one, mul_one] at this
  rw [this]; exact h1

theorem natCard_quot (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **Counting.**  A finite set whose differences are `exp k`-bounded on `S` and which is
separated modulo depth `k - n` has at most `∏_{v ∈ S} q_v^{n_v}` elements. -/
theorem card_le_of_separated (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (N : ℕ) (n : HeightOneSpectrum (𝓞 F) → ℕ) (k : HeightOneSpectrum (𝓞 F) → ℤ) (T : Finset F),
      ∑ v ∈ S, n v = N →
      (∀ x ∈ T, ∀ y ∈ T, ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v)) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        ¬ ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v - n v)) →
      T.card ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
  classical
  intro N
  induction N with
  | zero =>
    intro n k T hN h1 h2
    have hn : ∀ v ∈ S, n v = 0 := fun v hv => (Finset.sum_eq_zero_iff.mp hN) v hv
    rw [Finset.prod_eq_one fun v hv => by rw [hn v hv, pow_zero]]
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    by_contra hxy
    refine h2 x hx y hy hxy fun v hv => ?_
    rw [hn v hv]; simpa using h1 x hx y hy v hv
  | succ N ih =>
    intro n k T hN h1 h2
    obtain ⟨v₀, hv₀, hpos⟩ : ∃ v ∈ S, 0 < n v := by
      by_contra hcon
      push Not at hcon
      have : ∑ v ∈ S, n v = 0 := Finset.sum_eq_zero fun v hv => by have := hcon v hv; omega
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    set n' := Function.update n v₀ (n v₀ - 1) with hn'
    set k' := Function.update k v₀ (k v₀ - 1) with hk'
    have hsum : ∑ v ∈ S, n' v = N := by
      have e1 := Finset.add_sum_erase S n hv₀
      have e2 := Finset.add_sum_erase S n' hv₀
      have e3 : ∑ v ∈ S.erase v₀, n' v = ∑ v ∈ S.erase v₀, n v :=
        Finset.sum_congr rfl fun v hv => by
          rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
      have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
      omega
    obtain ⟨r, hr⟩ := exists_residue v₀
    obtain ⟨π, hπ⟩ := v₀.valuation_surjective F (WithZero.exp (-(k v₀)))
    have : Finite (𝓞 F ⧸ v₀.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [natCard_quot]; exact (NumberField.HeightOneSpectrum.one_lt_absNorm v₀).ne_bot)
    let _ := Fintype.ofFinite (𝓞 F ⧸ v₀.asIdeal)
    set c : F → 𝓞 F ⧸ v₀.asIdeal := fun x => r (π * (x - x₀)) with hc
    have hint : ∀ x ∈ T, v₀.valuation F (π * (x - x₀)) ≤ 1 := by
      intro x hx
      rw [map_mul, hπ]
      calc WithZero.exp (-(k v₀)) * v₀.valuation F (x - x₀)
          ≤ WithZero.exp (-(k v₀)) * WithZero.exp (k v₀) :=
            mul_le_mul' le_rfl (h1 x hx x₀ hx₀ v₀ hv₀)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    have hfib : ∀ a ∈ T.image c, (T.filter fun x => c x = a).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v := by
      intro a _
      refine ih n' k' _ hsum ?_ ?_
      · intro x hx y hy v hv
        rw [Finset.mem_filter] at hx hy
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', Function.update_self]
          by_cases hxy : x = y
          · simp [hxy]
          have hlt := hr _ _ (hint x hx.1) (hint y hy.1) (hx.2.trans hy.2.symm)
          have e : π * (x - x₀) - π * (y - x₀) = π * (x - y) := by ring
          rw [e, map_mul, hπ, val_eq_exp_ordv v (sub_ne_zero.mpr hxy), ← WithZero.exp_add,
            ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
          rw [val_eq_exp_ordv v (sub_ne_zero.mpr hxy), WithZero.exp_le_exp]
          omega
        · rw [hk', Function.update_of_ne hvv]
          exact h1 x hx.1 y hy.1 v hv
      · intro x hx y hy hxy hall
        rw [Finset.mem_filter] at hx hy
        refine h2 x hx.1 y hy.1 hxy fun v hv => ?_
        have := hall v hv
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', hn', Function.update_self, Function.update_self] at this
          have e : k v - 1 - ((n v - 1 : ℕ) : ℤ) = k v - (n v : ℤ) := by omega
          rwa [e] at this
        · rwa [hk', hn', Function.update_of_ne hvv, Function.update_of_ne hvv] at this
    have hcard := Finset.card_le_mul_card_image (f := c) T _ hfib
    have himg : (T.image c).card ≤ Ideal.absNorm v₀.asIdeal := by
      rw [← natCard_quot, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    calc T.card ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * (T.image c).card := hcard
      _ ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * Ideal.absNorm v₀.asIdeal :=
          Nat.mul_le_mul_left _ himg
      _ = ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
          rw [← Finset.mul_prod_erase S _ hv₀, ← Finset.mul_prod_erase S
            (fun v => Ideal.absNorm v.asIdeal ^ n v) hv₀]
          have e3 : ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n' v
              = ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n v :=
            Finset.prod_congr rfl fun v hv => by
              rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
          have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
          rw [e3, e4]
          have e5 : n v₀ = (n v₀ - 1) + 1 := by omega
          conv_rhs => rw [e5, pow_succ]
          ring

/-! ### Depth -/

theorem val_le_dep (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    v.valuation F x ≤ WithZero.exp ((dep v x : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [dep, if_neg hx, val_eq_exp_ordv v hx, WithZero.exp_le_exp]
  omega

open NumberField.HeightOneSpectrum in
theorem adicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) := by
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).pos
  have h1 : adicAbv F v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) :=
    abv_le_of_val_le v (val_eq_exp_ordv v hx).le
  have h2 : adicAbv F v x⁻¹ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(-ordv v x)) := by
    refine abv_le_of_val_le v ?_
    rw [map_inv₀, val_eq_exp_ordv v hx, ← WithZero.exp_neg]
  rw [map_inv₀, zpow_neg] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx
  refine le_antisymm h1 ?_
  have h3 := (inv_le_inv₀ hpos (zpow_pos hq _)).mp h2
  exact h3

open NumberField.HeightOneSpectrum in
theorem max_one_adicAbv (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    max 1 (adicAbv F v x) = (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases hx : x = 0
  · simp [hx, dep]
  rw [dep, if_neg hx, adicAbv_eq_zpow v hx]
  rcases le_or_gt 0 (ordv v x) with h | h
  · have e : (-ordv v x).toNat = 0 := by omega
    rw [e, pow_zero]
    exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le (by omega))
  · have e : -ordv v x = ((-ordv v x).toNat : ℤ) := by omega
    rw [e, zpow_natCast]
    simp only [Int.toNat_natCast]
    exact max_eq_right (one_le_pow₀ hq.le)

theorem normS_one_eq (𝔪 : Ideal (𝓞 F)) (x : F) :
    normS 𝔪 1 x = ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  rw [normS]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_one, max_one_adicAbv]

theorem rpow_factor {a : ℝ} (ha : 0 < a) (κ m : ℕ) (σ : ℝ) :
    a ^ (κ + m) * (a ^ κ) ^ (-σ) = a ^ m * (a ^ (1 - σ)) ^ κ := by
  rw [← Real.rpow_natCast a (κ + m), ← Real.rpow_natCast a κ, ← Real.rpow_natCast a m,
    ← Real.rpow_natCast (a ^ (1 - σ)) κ, ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le,
    ← Real.rpow_add ha, ← Real.rpow_add ha]
  congr 1
  push_cast
  ring

/-- **Stub S-1 of WP-S, proved** (identical statement to `S.summable_normS_one`). -/
theorem summable_normS_one {𝔪 : Ideal (𝓞 F)} (hG : Good 𝔪) (M : ℤ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) := by
  classical
  set S := CubicPkg.sFin 𝔪 with hS
  set m : ℕ := M.natAbs with hm
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq1 : ∀ v, 1 < q v := fun v => by
    show (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : ∀ v, 0 < q v := fun v => zero_lt_one.trans (hq1 v)
  set ρ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => q v ^ (1 - σ) with hρ
  have hρ0 : ∀ v, 0 ≤ ρ v := fun v => Real.rpow_nonneg (hq0 v).le _
  have hρ1 : ∀ v, ρ v < 1 := fun v => Real.rpow_lt_one_of_one_lt_of_neg (hq1 v) (by linarith)
  refine summable_of_sum_le (c := (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, (1 - ρ v.1)⁻¹)
    (fun u => Real.rpow_nonneg (normS_nonneg _ _) _) fun T => ?_
  -- depth vector
  set d : (F ⧸ lat 𝔪 M) → ({v // v ∈ S} → ℕ) := fun u v => dep v.1 u.out with hd
  set Kmax : ℕ := T.sup fun u => S.sup fun v => dep v u.out with hK
  set P : Finset ({v // v ∈ S} → ℕ) := Fintype.piFinset fun _ => Finset.range (Kmax + 1) with hP
  have hmaps : ∀ u ∈ T, d u ∈ P := by
    intro u hu
    rw [hP, Fintype.mem_piFinset]
    intro v
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := fun v => dep v u.out) v.2).trans
      (Finset.le_sup (f := fun u : F ⧸ lat 𝔪 M => S.sup fun v => dep v u.out) hu)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ κ ∈ P, ∑ u ∈ T with d u = κ, normS 𝔪 1 u.out ^ (-σ)
      ≤ (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
    intro κ _
    have hval : ∀ u ∈ T.filter (fun u => d u = κ), normS 𝔪 1 u.out ^ (-σ)
        = ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [normS_one_eq, ← hS, ← Finset.prod_attach S,
        ← Real.finsetProd_rpow _ _ (fun v _ => pow_nonneg (hq0 v.1).le _)]
      refine Finset.prod_congr rfl fun v _ => ?_
      have : dep v.1 u.out = κ v := congrFun hu.2 v
      rw [this]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    -- count the fibre
    set k : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if h : v ∈ S then (κ ⟨v, h⟩ : ℤ) else 0
      with hk
    set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (if h : v ∈ S then κ ⟨v, h⟩ else 0) + m
      with hn
    have hcount : (T.filter fun u => d u = κ).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
      rw [← Finset.card_image_of_injective _ (Quotient.out_injective)]
      refine card_le_of_separated S _ n k _ rfl ?_ ?_
      · intro x hx y hy v hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_filter] at hu hu'
        have e1 : dep v u.out = κ ⟨v, hv⟩ := congrFun hu.2 ⟨v, hv⟩
        have e2 : dep v u'.out = κ ⟨v, hv⟩ := congrFun hu'.2 ⟨v, hv⟩
        have b1 := val_le_dep v u.out
        have b2 := val_le_dep v u'.out
        rw [e1] at b1; rw [e2] at b2
        rw [hk]; simp only [dif_pos hv]
        exact (Valuation.map_sub _ _ _).trans (max_le b1 b2)
      · intro x hx y hy hxy hall
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        apply hxy
        have hmem : u.out - u'.out ∈ lat 𝔪 M := by
          intro v hv
          have hvS : v ∈ S := (CubicPkg.mem_sFin hG.ne_bot v).mpr hv
          refine (hall v hvS).trans ?_
          rw [WithZero.exp_le_exp, hk, hn]
          simp only [dif_pos hvS]
          push_cast
          omega
        have : (QuotientAddGroup.mk u.out : F ⧸ lat 𝔪 M) = QuotientAddGroup.mk u'.out := by
          rw [QuotientAddGroup.eq]
          have := (lat 𝔪 M).neg_mem hmem
          rwa [neg_sub, sub_eq_neg_add] at this
        rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
        rw [this]
    have hcountR : ((T.filter fun u => d u = κ).card : ℝ) ≤ ∏ v ∈ S.attach, q v.1 ^ (κ v + m) := by
      have : ((T.filter fun u => d u = κ).card : ℝ)
          ≤ ((∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v : ℕ) : ℝ) := by exact_mod_cast hcount
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [← Finset.prod_attach S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hn, hq]; simp only [dif_pos v.2, Subtype.coe_eta]
    calc ((T.filter fun u => d u = κ).card : ℝ) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ)
        ≤ (∏ v ∈ S.attach, q v.1 ^ (κ v + m)) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hcountR
            (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (pow_nonneg (hq0 v.1).le _) _)
      _ = (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun v _ => rpow_factor (hq0 v.1) _ _ _
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hq0 v.1).le _)
  have hprod : ∑ κ ∈ P, ∏ v ∈ S.attach, ρ v.1 ^ κ v
      = ∏ v ∈ S.attach, ∑ j ∈ Finset.range (Kmax + 1), ρ v.1 ^ j := by
    rw [hP, ← Finset.univ_eq_attach]
    exact (Finset.prod_univ_sum (fun _ : {v // v ∈ S} => Finset.range (Kmax + 1))
      (fun v j => ρ v.1 ^ j)).symm
  rw [hprod]
  refine Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun j _ => pow_nonneg (hρ0 v.1) _)
    fun v _ => ?_
  rw [← tsum_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)]
  exact (summable_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)).sum_le_tsum _
    fun j _ => pow_nonneg (hρ0 v.1) _

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.B_FourMain
/-!
# WP-B, part 6: the unfolded family and its integrals

For a genuine section `Φ`, a depth `M` valid for `(Φ, ν)` (`ValidDepth`), and `i = ((a, α), u)`
in `IdxI 𝔪 M`, with `c = rp a`, `σ = sec(α, u)`:

`hI i x = (σ/c)⁻¹ Φ_s(c, σ) · (N_∞(c)⁻¹ kerA v (x + σ/c))^s`.

* `tsum_hI_eq`: `∑_{(i, b) ∈ IdxI × Λ_M} hI i (b + x) = ∑_{(a, d)} Tfun Φ s (x, v) c_a d`.
* `tsum_lintegral_hI_ne_top`: `∑ᵢ ∫ |hI i| < ∞` for `Re s > 2` (S-1, `∑ N(c)^{1-σ} < ∞`).
* `integral_hI`: `∫ hI i · conj e_∞(ν ·) = gTerm · jTerm · (N_∞(c)⁻¹)^s · W_s(ν; v)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

theorem cI_ne_zero (i : IdxI 𝔪 M) : cI M i ≠ 0 := rp_ne_zero i.1.1.2

theorem cI_coe_ne_zero (i : IdxI 𝔪 M) : ((cI M i : SInt 𝔪) : F) ≠ 0 :=
  fun h => cI_ne_zero M i (Subtype.ext h)

include P hG hz6 in
theorem norm_cubicExt_inv_le (d c : SInt 𝔪) (hc : c ≠ 0) : ‖(cubicExt ι 𝔪 d c)⁻¹‖ ≤ 1 := by
  by_cases h : IsCoprime d c
  · have h3 := (S2.cubicSymbol ι P hG hz6).sym_pow_three d c hc h
    have h3' : cubicExt ι 𝔪 d c ^ 3 = 1 := h3
    have hn : ‖cubicExt ι 𝔪 d c‖ = 1 := by
      have := congrArg norm h3'
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
    rw [norm_inv, hn, inv_one]
  · rw [(S2.cubicExt_eq_zero_iff ι P hG hz6 d c hc).mpr h]
    simp

include hz6 in
theorem AI_eq_out {ν : F} (hV : ValidDepth hG Φ ν M) (i : IdxI 𝔪 M) :
    Φ s (cI M i : F) (sI hG M i : F) = Φ s (cI M i : F) ((cI M i : F) * i.2.out) := by
  have hcF := cI_coe_ne_zero M i
  obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) ((sI hG M i : F) / (cI M i : F))
  have hmk : (QuotientAddGroup.mk ((sI hG M i : F) / (cI M i : F)) : F ⧸ lat 𝔪 M) = i.2 :=
    mk_sec_div hG.ne_bot M (cI_ne_zero M i) i.1.2 i.2
  rw [hmk] at he
  rw [he, mul_add, mul_div_cancel₀ _ hcF, hV.unip h hh]

include hz6 in
theorem norm_AI_le {ν : F} (hV : ValidDepth hG Φ ν M) {B₀ : ℝ}
    (hB : ∀ c d : F, ‖Φ s c d‖ ≤ B₀ * normS 𝔪 c d ^ (-s.re)) (i : IdxI 𝔪 M) :
    ‖AI hG Φ s M i‖
      ≤ B₀ * absS 𝔪 (cI M i : F) ^ (-s.re) * normS 𝔪 1 i.2.out ^ (-s.re) := by
  have hcF := cI_coe_ne_zero M i
  rw [AI, norm_mul, AI_eq_out hG hz6 Φ s M hV i]
  have h1 := norm_cubicExt_inv_le (ι := ι) (P := P) hG hz6 (sI hG M i) (cI M i) (cI_ne_zero M i)
  have h2 := hB (cI M i : F) ((cI M i : F) * i.2.out)
  have e : normS 𝔪 (cI M i : F) ((cI M i : F) * i.2.out)
      = absS 𝔪 (cI M i : F) * normS 𝔪 1 i.2.out := by
    rw [← normS_mul_left, mul_one]
  rw [e, Real.mul_rpow (absS_pos hcF).le (normS_nonneg _ _), ← mul_assoc] at h2
  calc ‖(cubicExt ι 𝔪 (sI hG M i) (cI M i))⁻¹‖ * ‖Φ s (cI M i : F) ((cI M i : F) * i.2.out)‖
      ≤ 1 * ‖Φ s (cI M i : F) ((cI M i : F) * i.2.out)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h2

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourCoeff
/-!
# WP-B, part 7: the Fourier coefficients of the Eisenstein series at the cusp `∞`

`fourier_coeff`: for a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
and a fundamental cell `D` of `Λ_M = emb (R ∩ 𝔩_M)`:

`∫_D E(x, v) · conj e_∞(νx) dx = Φ_s(0,1) ht(v)^s ∫_D conj e_∞(νx) dx
    + vol(𝔩_M)⁻¹ · W_s(ν; v) · ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · λ(c; ν, s) · N(c)^{-s}`,

`λ(c; ν, s) = lam ψ_{S_f} M Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)`, `N(c) = #(R/cR)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

include hG in
theorem nrmR_pos {c : SInt 𝔪} (hc : c ≠ 0) : 0 < nrmR c :=
  Nat.cast_pos.mpr (natCard_quot_span_pos hG.ne_bot hc)

include hG in
theorem inv_Ninf_eq {c : SInt 𝔪} (hc : c ≠ 0) :
    (Ninf (c : F))⁻¹ = absS 𝔪 (c : F) * (nrmR c)⁻¹ := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have h := Ninf_mul_absS_eq hG.ne_bot hc
  have h1 := (Ninf_pos hcF).ne'
  have h2 := (nrmR_pos hG hc).ne'
  unfold nrmR at *
  field_simp
  linarith

include hz6 hv in
/-- `∑ᵢ ∫ |hI i| < ∞`. -/
theorem tsum_lintegral_hI_ne_top_oai {ν : F} (hV : ValidDepth hG Φ ν M) (hs : 2 < s.re) :
    ∑' i : IdxI 𝔪 M, ∫⁻ x : InfinitePlace F → ℂ, ‖hI hG Φ s v M i x‖ₑ ≠ ⊤ := by
  obtain ⟨B₁, hB₁⟩ := Φ.bound ‖s‖
  have hB : ∀ c d : F, ‖Φ s c d‖ ≤ |B₁| * normS 𝔪 c d ^ (-s.re) := fun c d =>
    (hB₁ s le_rfl c d).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg (normS_nonneg _ _) _))
  set C := kerInt s.re v with hC
  have hC0 : 0 ≤ C := kerInt_nonneg _ hv
  let f : (Σ a : Cls (SInt 𝔪), SInt 𝔪 ⧸ Ideal.span {rp a.1}) → ℝ := fun x =>
    |B₁| * C * nrmR (rp x.1.1) ^ (-s.re)
  let w : F ⧸ lat 𝔪 M → ℝ := fun u => normS 𝔪 1 u.out ^ (-s.re)
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    mul_nonneg (mul_nonneg (abs_nonneg _) hC0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hw0 : ∀ u, 0 ≤ w u := fun u => Real.rpow_nonneg (normS_nonneg _ _) _
  have hw : Summable w := RF.summable_normS_one hG M (by linarith)
  have hf : Summable f := by
    rw [summable_sigma_of_nonneg hf0]
    refine ⟨fun a => ?_, ?_⟩
    · have := B7.finite_quot_span hG.ne_bot (rp_ne_zero a.2)
      exact Summable.of_finite
    · have h1 := (summable_nrm_rpow hG.ne_bot (t := s.re - 1) (by linarith)).mul_left (|B₁| * C)
      refine h1.congr fun a => ?_
      simp only [f]
      rw [tsum_const, nsmul_eq_mul]
      have hp := nrmR_pos hG (rp_ne_zero a.2)
      have e : nrmR (rp a.1) ^ (-(s.re - 1)) = nrmR (rp a.1) * nrmR (rp a.1) ^ (-s.re) := by
        rw [neg_sub, sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
      change |B₁| * C * nrmR (rp a.1) ^ (-(s.re - 1)) = nrmR (rp a.1) * _
      rw [e]
      ring
  have hg : Summable fun i : IdxI 𝔪 M => f i.1 * w i.2 :=
    hf.mul_of_nonneg hw hf0 hw0
  have hle : ∀ i : IdxI 𝔪 M, ∫⁻ x : InfinitePlace F → ℂ, ‖hI hG Φ s v M i x‖ₑ
      ≤ ENNReal.ofReal (f i.1 * w i.2) := by
    intro i
    have hcF := cI_coe_ne_zero M i
    have hN := Ninf_pos hcF
    unfold hI
    rw [lintegral_hKer _ hN _ (by linarith) hv]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := norm_AI_le hG hz6 Φ s M hV hB i
    have e : absS 𝔪 (cI M i : F) ^ (-s.re) * (Ninf (cI M i : F))⁻¹ ^ s.re
        = nrmR (cI M i) ^ (-s.re) := by
      rw [inv_Ninf_eq hG (cI_ne_zero M i), Real.mul_rpow (absS_pos hcF).le
        (inv_nonneg.mpr (nrmR_pos hG (cI_ne_zero M i)).le), ← mul_assoc,
        ← Real.rpow_add (absS_pos hcF), neg_add_cancel, Real.rpow_zero, one_mul,
        Real.inv_rpow (nrmR_pos hG (cI_ne_zero M i)).le, Real.rpow_neg
        (nrmR_pos hG (cI_ne_zero M i)).le]
    calc ‖AI hG Φ s M i‖ * (Ninf (cI M i : F))⁻¹ ^ s.re * C
        ≤ (|B₁| * absS 𝔪 (cI M i : F) ^ (-s.re) * normS 𝔪 1 i.2.out ^ (-s.re))
            * (Ninf (cI M i : F))⁻¹ ^ s.re * C := by
          gcongr
      _ = |B₁| * C * (absS 𝔪 (cI M i : F) ^ (-s.re) * (Ninf (cI M i : F))⁻¹ ^ s.re)
            * normS 𝔪 1 i.2.out ^ (-s.re) := by ring
      _ = f i.1 * w i.2 := by rw [e]; rfl
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hf0 _) (hw0 _)) hg]
  exact ENNReal.ofReal_ne_top

/-! ### The integral of one member of the family -/

/-! ### Summation -/

end ArtinKP.B
end
end

theorem solution.{u_1} : type_of% @ArtinKP.B.tsum_lintegral_hI_ne_top_oai.{u_1} := @ArtinKP.B.tsum_lintegral_hI_ne_top_oai.{u_1}
