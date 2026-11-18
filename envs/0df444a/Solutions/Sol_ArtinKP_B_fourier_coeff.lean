-- Prove2me | solution 1 for ArtinKP.B.fourier_coeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:14.219268+00:00
-- url     : https://prove2.me/submissions/f195ccad-df5b-4dbf-9422-9a444a85aefb

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
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_B_eis_eq_add_tsum_Tfun
import Theorems.Thm_ArtinKP_B_tsum_lintegral_hI_ne_top

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace X

lemma pairHt_eq_prod (c d : F) (P : X F) :
    pairHt c d P = ∏ w, P.v w / H3.rowDen (w.embedding c) (w.embedding d) (P w) := by
  unfold pairHt ht pairDen
  rw [Finset.prod_div_distrib]

end X

/-! ### Topology and measure -/

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Const
/-! # WP-B1, file 6: the constant term of `Tinf` (Lemma K) by unfolding and scaling

`constTerm S σ v = ∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx` (integral over the fundamental cell `fundD`).
Unfolding over the free action of the translations `n(β)`, `β ∈ 𝓞_F`, on the classes `≠ ∞`
(`orbEquiv`) turns it into a sum of integrals over all of `ℂ^r`, each of which scales exactly like
`ht(v)^{2-σ}` (`lintegral_sHt_scale`).  Hence `constTerm S σ v = ht(v)^{2-σ} · constTerm S σ 1`
(`constTerm_scale`), and `constTerm S σ 1 < ∞` by the locally uniform convergence (`constTerm_one_lt_top`).
No zeta function and no strong approximation are needed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem instCountableField : Countable F := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  have : Function.Surjective (fun p : 𝓞 F × 𝓞 F => ((p.1 : F) / (p.2 : F))) := by
    intro z
    obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
    exact ⟨(x, y), h⟩
  exact this.countable

instance instCountableSPair {S : Finset (FinitePlace F)} : Countable (SPair S) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Function.Injective (fun q : SPair S => (q.c, q.d)) := by
    intro q q' h
    exact SPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact this.countable

instance instCountablePairClass {S : Finset (FinitePlace F)} : Countable (PairClass S) :=
  Quotient.countable

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B7_Sum
/-! # B7_Sum: sums over residues modulo a principal ideal

For a commutative ring `R`, `c : R` and `f : R → ℂ`, `rsum c f` is the sum of `f` over chosen
representatives of `R ⧸ (c)` (the same `Function.surjInv` choice as `ArtinPrimitiveRoots.quotLift`).
For `f` periodic modulo `c` (`Per c f`) it does not depend on the choice, and we prove the
reindexing lemmas used for Gauss sums: translation, multiplication by a unit modulo `c`, the
Chinese remainder theorem, and the fibre formula for a function periodic modulo a divisor.
-/

namespace ArtinKP.B7

variable {R : Type*} [CommRing R]

lemma mk_rep (c : R) (x : R ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (rep c x) = x :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective x

lemma mk_eq_mk_iff {c a b : R} :
    Ideal.Quotient.mk (Ideal.span {c}) a = Ideal.Quotient.mk (Ideal.span {c}) b ↔ c ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma Per.mul {c : R} {f g : R → ℂ} (hf : Per c f) (hg : Per c g) : Per c (fun d => f d * g d) :=
  fun a b hab => by simp only [hf a b hab, hg a b hab]

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_Gauss
/-! # B7_Gauss: the cubic Gauss sum `g(ν, c)` over a ring of `S`-integers, abstractly

`R` is a domain with fraction-type field `K` (in the application `R = SInt 𝔪`, `K = F`).

* `CubicSymbol R` is the interface to WP-A: the cubic exterior symbol `(d/c)`, with exactly the
  properties used here.
* `AddData R K` is an additive character of `K` trivial on `R` (in the application `sAddChar 𝔪`,
  see `B7_Link`).
* `gauss S A ν c = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)` (terms with `(d, c) ≠ 1` vanish since
  `(d/c) = 0` there and `0⁻¹ = 0`).

Main results (MATH.md (B7)): `gauss_mul` (twisted multiplicativity), `gauss_mul_left`
(`g(μν, c) = (μ/c) g(ν, c)`), the prime-power table `gauss_prime_pow_le`,
`gauss_prime_pow_succ`, `gauss_prime_pow_eq_zero`, and the constant-term sums `csum_eq_phi`,
`csum_eq_zero`, `csum_of_cube`, `csum_eq_zero_of_val`, `csum_prime_pow`, `phi_prime_pow`.
-/

set_option linter.unusedSectionVars false

namespace ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

namespace AddData

variable (A : AddData R K)

omit A in
lemma map_ne_zero (A : AddData R K) {c : R} (hc : c ≠ 0) : algebraMap R K c ≠ 0 := fun h =>
  hc (A.inj (h.trans (map_zero _).symm))

lemma ψ_add (a b c : R) : A.ψ (a + b) c = A.ψ a c * A.ψ b c := by
  unfold ψ; rw [map_add, add_div, A.e_add]

lemma ψ_mul_self {c : R} (hc : c ≠ 0) (r : R) : A.ψ (c * r) c = 1 := by
  unfold ψ
  rw [map_mul, mul_div_cancel_left₀ _ (A.map_ne_zero hc), A.e_int]

lemma ψ_per {c : R} (hc : c ≠ 0) {a b : R} (h : c ∣ a - b) : A.ψ a c = A.ψ b c := by
  obtain ⟨r, hr⟩ := h
  have : a = b + c * r := by rw [← hr]; ring
  rw [this, ψ_add, ψ_mul_self A hc, mul_one]

end AddData

/-! ### Elementary facts about the symbol -/

namespace CubicSymbol

variable (S : CubicSymbol R)

lemma sym_per {c : R} (hc : c ≠ 0) : Per c (fun d => (S.sym d c)⁻¹) :=
  fun a b hab => by simp only [S.sym_congr a b c hc hab]

end CubicSymbol

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-- The summand of `g(ν, c)` is periodic modulo `c` (well-definedness). -/
lemma gauss_per (ν : R) {c : R} (hc : c ≠ 0) :
    Per c (fun d => (S.sym d c)⁻¹ * A.ψ (ν * d) c) := by
  refine (S.sym_per hc).mul fun a b hab => A.ψ_per hc ?_
  rw [← mul_sub]; exact hab.mul_left ν

/-! ### Constant-term sums -/

/-! ### Prime powers -/

end ArtinKP.B7
end

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

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

/-- The summand of `jac` on the class of `x`, for periodic data. -/
theorem jac_term (hf : ∀ x h : F, Small 𝔪 M h → f (x + h) = f x)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) (x : F) :
    f (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out
        * (starRingEnd ℂ) (ψ (ν * (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out))
      = f x * (starRingEnd ℂ) (ψ (ν * x)) := by
  obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) x
  rw [he, hf x h hh, mul_add, ψ.map_add, hψ h hh, mul_one]

end jac

/-! ### The Kirillov function -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
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

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

theorem continuous_archChar : Continuous archChar := by
  unfold archChar
  fun_prop

theorem continuous_eInf : Continuous (eInf : (InfinitePlace F → ℂ) → ℂ) :=
  continuous_finsetProd _ fun w _ =>
    continuous_archChar.comp (continuous_apply w).neg

theorem emb_mul (a b : F) : emb (a * b) = emb a * emb b := by
  ext w
  simp

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `e_∞(x) = sAddChar(x) · conj ψ_{S_f}(x)` for `x ∈ F` (MATH2 §0.2). -/
theorem eInf_emb_eq [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    eInf (emb x) = sAddChar 𝔪 x * conj (psiS h𝔪 x) := by
  have h1 : sAddChar 𝔪 x * conj (sAddChar 𝔪 x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sAddChar h𝔪]
    simp
  rw [psiS_apply, map_mul, Complex.conj_conj, ← mul_assoc, h1, one_mul]

/-! ### The archimedean kernel -/

theorem kerA_pos {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    0 < kerA v x :=
  Finset.prod_pos fun w _ => div_pos (hv w) (by positivity [hv w])

theorem continuous_kerA {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    Continuous (kerA v) := by
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.div continuous_const (by fun_prop) fun x => ?_
  have := hv w
  positivity

/-- `I_{(c,d)}(x, v) = N_∞(c)⁻¹ ∏_w v_w / (|x_w + d/c|² + v_w²)` for `c ≠ 0`. -/
theorem pairHt_mk {c : F} (hc : c ≠ 0) (d : F) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    X.pairHt c d (X.mk x v hv) = (Ninf c)⁻¹ * kerA v (x + emb (d / c)) := by
  rw [X.pairHt_eq_prod, Ninf, kerA, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hcw : w.embedding c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : Complex.normSq (w.embedding c) ≠ 0 := Complex.normSq_pos.mpr hcw |>.ne'
  change v w / (Complex.normSq (w.embedding c * x w + w.embedding d)
    + Complex.normSq (w.embedding c) * v w ^ 2) = _
  have h1 : Complex.normSq (w.embedding c * x w + w.embedding d)
      = Complex.normSq (w.embedding c) * ‖x w + w.embedding (d / c)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_mul]
    congr 1
    rw [map_div₀]
    field_simp
  rw [h1, Pi.add_apply, emb_apply, ← mul_add, ← div_div, div_eq_inv_mul, ← div_eq_inv_mul,
    div_eq_inv_mul, ← mul_div_assoc, div_eq_inv_mul]
  field_simp

theorem cpow_prod_nonneg {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    (((∏ i ∈ t, f i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

theorem norm_chiInf (ν : F) (x : InfinitePlace F → ℂ) : ‖chiInf ν x‖ = 1 := by
  rw [chiInf, RCLike.norm_conj, norm_eInf]

theorem chiInf_add (ν : F) (x y : InfinitePlace F → ℂ) :
    chiInf ν (x + y) = chiInf ν x * chiInf ν y := by
  rw [chiInf, mul_add, eInf_add, map_mul]
  rfl

theorem chiInf_emb (ν a : F) : chiInf ν (emb a) = conj (eInf (emb (ν * a))) := by
  rw [chiInf, emb_mul]

theorem continuous_chiInf (ν : F) : Continuous (chiInf ν) :=
  Complex.continuous_conj.comp (continuous_eInf.comp (continuous_const.mul continuous_id))

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-- `∫ (kerA v)^s · conj e_∞(ν ·) = W_s(ν; v)`. -/
theorem integral_kerA (s : ℂ) (ν : F) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x : InfinitePlace F → ℂ, ((kerA v x : ℝ) : ℂ) ^ s * chiInf ν x = Winf s ν v := by
  let g : InfinitePlace F → ℂ → ℂ := fun w y =>
    ((v w / (‖y‖ ^ 2 + v w ^ 2) : ℝ) : ℂ) ^ s * archChar (-(-(w.embedding ν)) * y)
  have h : ∀ x : InfinitePlace F → ℂ, ((kerA v x : ℝ) : ℂ) ^ s * chiInf ν x
      = ∏ w, g w (x w) := by
    intro x
    rw [Finset.prod_mul_distrib, ← chiInf_eq_prod, kerA,
      cpow_prod_nonneg _ _ (fun w => by have := hv w; positivity)]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), volume_pi]
  exact integral_fintype_prod_eq_prod g

/-! ### Shifted kernels -/

theorem measurable_hKer (A : ℂ) (N : ℝ) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) : Measurable (hKer A N e s v) := by
  have h1 : Measurable fun x : InfinitePlace F → ℂ => N⁻¹ * kerA v (x + e) :=
    measurable_const.mul
      ((continuous_kerA hv).comp (continuous_id.add continuous_const)).measurable
  exact measurable_const.mul ((Complex.measurable_ofReal.comp h1).pow_const s)

theorem hKer_eq {A : ℂ} {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    hKer A N e s v x = A * ((N⁻¹ : ℝ) : ℂ) ^ s * ((kerA v (x + e) : ℝ) : ℂ) ^ s := by
  rw [hKer, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_pos.mpr hN).le (kerA_pos hv _).le, mul_assoc]

/-- The integral of a shifted kernel against `conj e_∞(ν ·)`. -/
theorem integral_hKer (A : ℂ) {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) (s : ℂ) (ν : F)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ∫ x : InfinitePlace F → ℂ, hKer A N e s v x * chiInf ν x
      = A * ((N⁻¹ : ℝ) : ℂ) ^ s * conj (chiInf ν e) * Winf s ν v := by
  have hunit : chiInf ν e * conj (chiInf ν e) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_chiInf]
    simp
  have h : ∀ x : InfinitePlace F → ℂ, hKer A N e s v x * chiInf ν x
      = (A * ((N⁻¹ : ℝ) : ℂ) ^ s * conj (chiInf ν e))
        * (fun y : InfinitePlace F → ℂ => ((kerA v y : ℝ) : ℂ) ^ s * chiInf ν y) (x + e) := by
    intro x
    simp only
    rw [hKer_eq hN e s hv, chiInf_add]
    linear_combination (-(A * ((N⁻¹ : ℝ) : ℂ) ^ s * ((kerA v (x + e) : ℝ) : ℂ) ^ s
      * chiInf ν x)) * hunit
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul,
    integral_add_right_eq_self (fun y : InfinitePlace F → ℂ =>
      ((kerA v y : ℝ) : ℂ) ^ s * chiInf ν y) e, integral_kerA s ν v hv]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourIndex
/-!
# WP-B, part 4: the index set of the unfolded sum

* `exists_sInt_sub_small`: strong approximation `F = R + 𝔩_M` (from `B7.hasWit_all`).
* `latR 𝔪 M = R ∩ 𝔩_M`, `transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r` (the translation lattice `Λ_M`).
* `sec`: for `c ≠ 0` a section of `R → R/cR × F/𝔩_M`, `d ↦ (d mod c, d/c mod 𝔩_M)`.
* `thetaEquiv`: `((Σ a, R/c_a R) × F/𝔩_M) × Λ_M ≃ (R∖0)/Rˣ × R`,
  `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)` — MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Strong approximation -/

/-! ### The translation lattice -/

instance instCountableSInt : Countable (SInt 𝔪) :=
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  (Subtype.val_injective : Function.Injective fun b : SInt 𝔪 => (b : F)).countable

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat (M : ℤ) : Countable (transLat 𝔪 M) := (latREquiv 𝔪 M).symm.injective.countable

/-! ### The section -/

/-! ### The index equivalence -/

/-! ### Rows with `c ≠ 0` modulo units -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourUnfold
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass
/-!
# WP-B, part 1: unfolding an integral over a fundamental cell (abstract measure theory)

For a countable subgroup `L` of `E` with fundamental domain `D`, a countable family `h i : E → ℂ`
with `∑ᵢ ∫ ‖h i‖ < ∞` and a bounded `L`-periodic `χ`:

`∫_D (∑_{(i,b) ∈ I × L} h i (b + x)) χ(x) dx = ∑ᵢ ∫_E h i · χ`.

No pointwise convergence is assumed (it holds almost everywhere by Tonelli).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ENNReal

noncomputable section

namespace ArtinKP.B

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] {μ : Measure E}
  (L : AddSubgroup E) [Countable L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
  {I : Type*} [Countable I] {D : Set E}

/-- Tonelli for the unfolded family. -/
theorem lintegral_unfold (hD : IsAddFundamentalDomain L D μ) (h : I → E → ℂ) :
    ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x)‖ₑ ∂μ = ∑' i, ∫⁻ x, ‖h i x‖ₑ ∂μ := by
  rw [ENNReal.tsum_prod (f := fun (i : I) (b : L) => ∫⁻ x in D, ‖h i ((b : E) + x)‖ₑ ∂μ)]
  refine tsum_congr fun i => ?_
  rw [hD.lintegral_eq_tsum' fun x => ‖h i x‖ₑ, ← (Equiv.neg L).tsum_eq]
  refine tsum_congr fun b => ?_
  simp only [Equiv.neg_apply, neg_neg]
  rfl

variable (hD : IsAddFundamentalDomain L D μ) (h : I → E → ℂ) (hm : ∀ i, Measurable (h i))
  (hfin : ∑' i, ∫⁻ x, ‖h i x‖ₑ ∂μ ≠ ⊤) (χ : E → ℂ) (hχm : Measurable χ)
  (hχ1 : ∀ x, ‖χ x‖ ≤ 1)

include hD hfin hχ1 in
theorem tsum_lintegral_unfold_ne_top :
    ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x) * χ x‖ₑ ∂μ ≠ ⊤ := by
  have h0 : ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x)‖ₑ ∂μ ≠ ⊤ := by
    rwa [lintegral_unfold L hD h]
  refine ne_top_of_le_ne_top h0 ?_
  refine ENNReal.tsum_le_tsum fun p => lintegral_mono fun x => ?_
  rw [enorm_mul]
  calc ‖h p.1 ((p.2 : E) + x)‖ₑ * ‖χ x‖ₑ ≤ ‖h p.1 ((p.2 : E) + x)‖ₑ * 1 := by
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_one.mpr (hχ1 x)
    _ = _ := mul_one _

variable [MeasurableAdd E]

include hm hχm in
theorem measurable_unfold_term (p : I × L) :
    Measurable fun x => h p.1 ((p.2 : E) + x) * χ x :=
  ((hm p.1).comp (measurable_const_add _)).mul hχm

include hD hfin hχ1 hm hχm in
/-- The unfolded sum is integrable over the cell (finiteness of the `L¹` norm). -/
theorem lintegral_tsum_unfold_ne_top :
    ∫⁻ x in D, ‖(∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x‖ₑ ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (tsum_lintegral_unfold_ne_top L hD h hfin χ hχ1) ?_
  rw [← lintegral_tsum fun p => (measurable_unfold_term L h hm χ hχm p).enorm.aemeasurable]
  refine lintegral_mono fun x => ?_
  rw [← tsum_mul_right]
  exact enorm_tsum_le_tsum_enorm

include hD hfin hχ1 hm hχm in
/-- **Unfolding.** -/
theorem integral_unfold (hχp : ∀ (b : L) (x : E), χ ((b : E) + x) = χ x) :
    Summable (fun i => ‖∫ x, h i x * χ x ∂μ‖) ∧
    ∫ x in D, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x ∂μ = ∑' i, ∫ x, h i x * χ x ∂μ := by
  have hT := tsum_lintegral_unfold_ne_top L hD h hfin χ hχ1
  -- each `h i χ` is integrable
  have hint : ∀ i, Integrable (fun x => h i x * χ x) μ := by
    intro i
    refine ⟨((hm i).mul hχm).aestronglyMeasurable, ?_⟩
    have hi : ∫⁻ x, ‖h i x‖ₑ ∂μ ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum i)
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hi.lt_top
    rw [enorm_mul]
    calc ‖h i x‖ₑ * ‖χ x‖ₑ ≤ ‖h i x‖ₑ * 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.mpr (hχ1 x)
      _ = _ := mul_one _
  -- the sum over `b` of the cell integrals
  have hcell : ∀ i, ∫ x, h i x * χ x ∂μ = ∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ := by
    intro i
    rw [hD.integral_eq_tsum' _ (hint i), ← (Equiv.neg L).tsum_eq]
    refine tsum_congr fun b => ?_
    simp only [Equiv.neg_apply, neg_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change h i ((b : E) + x) * χ ((b : E) + x) = _
    rw [hχp]
  -- summability of the double family
  have hsum : Summable fun p : I × L => ∫ x in D, h p.1 ((p.2 : E) + x) * χ x ∂μ := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hT) fun p => ?_
    have hle := enorm_integral_le_lintegral_enorm (μ := μ.restrict D)
      (fun x => h p.1 ((p.2 : E) + x) * χ x)
    have hp : ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x) * χ x‖ₑ ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hT (ENNReal.le_tsum p)
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hp hle
  have hmain : ∫ x in D, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x ∂μ
      = ∑' i, ∫ x, h i x * χ x ∂μ := by
    have h1 : ∀ x, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x
        = ∑' p : I × L, h p.1 ((p.2 : E) + x) * χ x := fun x => tsum_mul_right.symm
    simp only [h1]
    rw [integral_tsum (fun p => (measurable_unfold_term L h hm χ hχm p).aestronglyMeasurable) hT,
      hsum.tsum_prod]
    exact tsum_congr fun i => (hcell i).symm
  refine ⟨?_, hmain⟩
  have h2 : Summable fun i => ‖∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => norm_tsum_le_tsum_norm (hsum.norm.prod_factor i)) hsum.norm.prod
  have h3 : (fun i => ‖∫ x, h i x * χ x ∂μ‖)
      = fun i => ‖∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ‖ := funext fun i => by
    rw [hcell i]
  rw [h3]
  exact h2

end ArtinKP.B
end
end

section
-- module Solutions.Artin.T12.L2B_Orth
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
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
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
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

end ArtinKP.B
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

include hv in
theorem Tfun_mk {c : SInt 𝔪} (hc : c ≠ 0) (d : SInt 𝔪) (x : InfinitePlace F → ℂ) :
    Tfun Φ s (X.mk x v hv) c d
      = hKer ((cubicExt ι 𝔪 d c)⁻¹ * Φ s (c : F) (d : F)) (Ninf (c : F))
          (emb ((d : F) / (c : F))) s v x := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  rw [Tfun, pairHt_mk hcF]
  rfl

include hz6 hv in
theorem hI_shift {ν : F} (hV : ValidDepth hG Φ ν M) (i : IdxI 𝔪 M) (b : latR 𝔪 M)
    (x : InfinitePlace F → ℂ) :
    hI hG Φ s v M i (emb ((b : SInt 𝔪) : F) + x)
      = Tfun Φ s (X.mk x v hv) (cI M i) (sI hG M i + cI M i * (b : SInt 𝔪)) := by
  have hc := cI_ne_zero M i
  have hcF := cI_coe_ne_zero M i
  rw [Tfun_mk Φ s v hv hc]
  have e1 : cubicExt ι 𝔪 (sI hG M i + cI M i * (b : SInt 𝔪)) (cI M i)
      = cubicExt ι 𝔪 (sI hG M i) (cI M i) :=
    (S2.cubicSymbol ι P hG hz6).sym_congr _ _ _ hc ⟨b, by ring⟩
  have e2 : Φ s (cI M i : F) ((sI hG M i + cI M i * (b : SInt 𝔪) : SInt 𝔪) : F)
      = Φ s (cI M i : F) (sI hG M i : F) := by
    push_cast
    exact hV.unip _ b.2 s _ _
  have e3 : emb (((sI hG M i + cI M i * (b : SInt 𝔪) : SInt 𝔪) : F) / (cI M i : F))
      = emb ((sI hG M i : F) / (cI M i : F)) + emb ((b : SInt 𝔪) : F) := by
    rw [← map_add]
    congr 1
    push_cast
    field_simp
  rw [e1, e2, e3, hI, AI, hKer, hKer]
  congr 4
  abel

include hz6 hv in
/-- The double family sums to the sum over `(c mod units, d ∈ R)`. -/
theorem tsum_hI_eq {ν : F} (hV : ValidDepth hG Φ ν M) (x : InfinitePlace F → ℂ) :
    ∑' p : IdxI 𝔪 M × transLat 𝔪 M,
        hI hG Φ s v M p.1 ((p.2 : InfinitePlace F → ℂ) + x)
      = ∑' y : Cls (SInt 𝔪) × SInt 𝔪, Tfun Φ s (X.mk x v hv) (rp y.1.1) y.2 := by
  rw [← (thetaEquiv hG.ne_bot M).tsum_eq,
    ← (Equiv.prodCongr (Equiv.refl (IdxI 𝔪 M)) (latREquiv 𝔪 M)).tsum_eq]
  exact tsum_congr fun p => hI_shift hG hz6 Φ s v hv M hV p.1 p.2 x

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

/-! ### The integral of one member of the family -/

include hv in
theorem integral_hI (ν : SInt 𝔪) (hV : ValidDepth hG Φ (ν : F) M) (i : IdxI 𝔪 M) :
    ∫ x : InfinitePlace F → ℂ, hI hG Φ s v M i x * chiInf (ν : F) x
      = gTerm (ι := ι) (P := P) hG hz6 ν i.1 * jTerm hG Φ s M ν i.1.1 i.2
        * (((Ninf (cI M i : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v := by
  have hc := cI_ne_zero M i
  have hcF := cI_coe_ne_zero M i
  unfold hI
  rw [integral_hKer _ (Ninf_pos hcF) _ s (ν : F) hv]
  have e1 : conj (chiInf (ν : F) (emb ((sI hG M i : F) / (cI M i : F))))
      = sAddChar 𝔪 ((ν : F) * ((sI hG M i : F) / (cI M i : F)))
        * conj (psiS hG.ne_bot ((ν : F) * ((sI hG M i : F) / (cI M i : F)))) := by
    rw [chiInf_emb, Complex.conj_conj, eInf_emb_eq hG.ne_bot]
  have e2 : gTerm (ι := ι) (P := P) hG hz6 ν i.1
      = (cubicExt ι 𝔪 (sI hG M i) (cI M i))⁻¹
        * sAddChar 𝔪 ((ν : F) * ((sI hG M i : F) / (cI M i : F))) := by
    have hper := B7.gauss_per (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν hc
    have hdvd : cI M i ∣ B7.rep (cI M i) i.1.2 - sI hG M i :=
      B7.mk_eq_mk_iff.1 ((B7.mk_rep _ _).trans (mk_sec hG.ne_bot M hc i.1.2 i.2).symm)
    have h1 := hper (B7.rep (cI M i) i.1.2) (sI hG M i) hdvd
    refine h1.trans ?_
    change (cubicExt ι 𝔪 (sI hG M i) (cI M i))⁻¹
      * sAddChar 𝔪 (((ν * sI hG M i : SInt 𝔪) : F) / (cI M i : F)) = _
    rw [Subalgebra.coe_mul, mul_div_assoc]
  have e3 : jTerm hG Φ s M ν i.1.1 i.2
      = Φ s (cI M i : F) (sI hG M i : F)
        * conj (psiS hG.ne_bot ((ν : F) * ((sI hG M i : F) / (cI M i : F)))) := by
    have hmk : (QuotientAddGroup.mk ((sI hG M i : F) / (cI M i : F)) : F ⧸ lat 𝔪 M) = i.2 :=
      mk_sec_div hG.ne_bot M hc i.1.2 i.2
    have hjt := jac_term (psiS hG.ne_bot) (M := M)
      (f := fun u => Φ s (cI M i : F) ((cI M i : F) * u)) (ν := (ν : F))
      (fun x h hh => by
        rw [mul_add]
        exact hV.unip h hh s _ _)
      hV.char ((sI hG M i : F) / (cI M i : F))
    rw [hmk] at hjt
    have hjt' : Φ s (cI M i : F) ((cI M i : F) * i.2.out)
          * conj (psiS hG.ne_bot ((ν : F) * i.2.out))
        = Φ s (cI M i : F) ((cI M i : F) * ((sI hG M i : F) / (cI M i : F)))
          * conj (psiS hG.ne_bot ((ν : F) * ((sI hG M i : F) / (cI M i : F)))) := hjt
    rw [mul_div_cancel₀ _ hcF] at hjt'
    exact hjt'
  rw [e1, e2, e3, AI]
  ring

/-! ### Summation -/

theorem vol_pos (M : ℤ) : 0 < vol 𝔪 M :=
  Finset.prod_pos fun v _ => zpow_pos (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)) _

include hG in
theorem inv_Ninf_cpow {c : SInt 𝔪} (hc : c ≠ 0) (s : ℂ) :
    (((Ninf (c : F))⁻¹ : ℝ) : ℂ) ^ s = ((absS 𝔪 (c : F) : ℝ) : ℂ) ^ s * nrm c ^ (-s) := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hp := nrmR_pos hG hc
  have hn : nrm c = ((nrmR c : ℝ) : ℂ) := by
    rw [nrm, nrmR, Complex.ofReal_natCast]
  have harg : ((nrmR c : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hp.le]
    exact Real.pi_ne_zero.symm
  rw [inv_Ninf_eq hG hc, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (absS_pos hcF).le (inv_nonneg.mpr hp.le), hn,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

include hv in
/-- The sum of the integrals: Gauss sums times finite Jacquet functionals. -/
theorem tsum_integral_hI (ν : SInt 𝔪) (hV : ValidDepth hG Φ (ν : F) M)
    (hsum : Summable fun i : IdxI 𝔪 M =>
      ‖∫ x : InfinitePlace F → ℂ, hI hG Φ s v M i x * chiInf (ν : F) x‖) :
    ∑' i : IdxI 𝔪 M, ∫ x : InfinitePlace F → ℂ, hI hG Φ s v M i x * chiInf (ν : F) x
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
        * ∑' a : Cls (SInt 𝔪),
            B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
              * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) := by
  have hterm : (fun i : IdxI 𝔪 M =>
      ∫ x : InfinitePlace F → ℂ, hI hG Φ s v M i x * chiInf (ν : F) x)
      = fun i : IdxI 𝔪 M => gTerm (ι := ι) (P := P) hG hz6 ν i.1 * jTerm hG Φ s M ν i.1.1 i.2
        * (((Ninf ((rp i.1.1.1 : SInt 𝔪) : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v :=
    funext fun i => integral_hI hG hz6 Φ s v hv M ν hV i
  have hS : Summable fun i : IdxI 𝔪 M =>
      gTerm (ι := ι) (P := P) hG hz6 ν i.1 * jTerm hG Φ s M ν i.1.1 i.2
        * (((Ninf ((rp i.1.1.1 : SInt 𝔪) : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v := by
    have := hsum.of_norm
    rwa [hterm] at this
  rw [hterm, hS.tsum_prod]
  have hfin : ∀ a : Cls (SInt 𝔪), Finite (SInt 𝔪 ⧸ Ideal.span {rp a.1}) := fun a =>
    B7.finite_quot_span hG.ne_bot (rp_ne_zero a.2)
  have hS1 := hS.prod
  rw [hS1.tsum_sigma' fun a => by
    have := hfin a
    exact Summable.of_finite, ← tsum_mul_left]
  refine tsum_congr fun a => ?_
  have := hfin a
  have hvol : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos M).ne'
  have hu : ∀ α : SInt 𝔪 ⧸ Ideal.span {rp a.1},
      ∑' u : F ⧸ lat 𝔪 M, gTerm (ι := ι) (P := P) hG hz6 ν ⟨a, α⟩ * jTerm hG Φ s M ν a u
          * (((Ninf ((rp a.1 : SInt 𝔪) : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v
        = gTerm (ι := ι) (P := P) hG hz6 ν ⟨a, α⟩
          * ((((Ninf ((rp a.1 : SInt 𝔪) : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v
            * ∑' u : F ⧸ lat 𝔪 M, jTerm hG Φ s M ν a u) := by
    intro α
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun u => by ring
  have hg : ∑' α : SInt 𝔪 ⧸ Ideal.span {rp a.1}, gTerm (ι := ι) (P := P) hG hz6 ν ⟨a, α⟩
      = B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1) := by
    rw [tsum_eq_finsum (Set.toFinite _)]
    rfl
  have hj : ∑' u : F ⧸ lat 𝔪 M, jTerm hG Φ s M ν a u
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹
        * jac (psiS hG.ne_bot) M (fun u => Φ s ((rp a.1 : SInt 𝔪) : F) (((rp a.1 : SInt 𝔪) : F) * u)) (ν : F) := by
    rw [jac, ← mul_assoc, inv_mul_cancel₀ hvol, one_mul]
    rfl
  change ∑' α : SInt 𝔪 ⧸ Ideal.span {rp a.1}, ∑' u : F ⧸ lat 𝔪 M,
      gTerm (ι := ι) (P := P) hG hz6 ν ⟨a, α⟩ * jTerm hG Φ s M ν a u
        * (((Ninf ((rp a.1 : SInt 𝔪) : F))⁻¹ : ℝ) : ℂ) ^ s * Winf s (ν : F) v = _
  simp only [hu]
  rw [tsum_mul_right, hg, hj, lam, inv_Ninf_cpow hG (rp_ne_zero a.2)]
  ring

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-!
# WP-B, part 8: the Fourier expansion at `∞` — statements

For a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
(`ValidDepth hG Φ ν M`), and any fundamental cell `D` of finite volume of the translation
lattice `Λ_M = transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`:

* `fourier_coeff` (all `ν`), `fourier_coeff_ne_zero` (`ν ≠ 0`), `const_term` (`ν = 0`).

Normalizations: `chiInf ν x = conj e_∞(νx)`, `e_∞(x) = ∏_w archChar (-x_w)` (so
`e_∞ = exp(-2πi Tr)` on `F`); `dx` is Lebesgue measure on `ℂ^r = (ℝ²)^r`;
`Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; `vol 𝔪 M = ∏_{v ∣ 𝔪} q_v^{-M}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

instance instCountableIdxI (M : ℤ) : Countable (IdxI 𝔪 M) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Countable (Associates (SInt 𝔪)) := Associates.mk_surjective.countable
  have : ∀ c : SInt 𝔪, Countable (SInt 𝔪 ⧸ Ideal.span {c}) := fun c =>
    Ideal.Quotient.mk_surjective.countable
  have : Countable (F ⧸ lat 𝔪 M) := QuotientAddGroup.mk_surjective.countable
  infer_instance

theorem continuous_mk_x (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    Continuous fun x : InfinitePlace F → ℂ => X.mk x v hv := by
  refine continuous_pi fun w => ?_
  exact Continuous.subtype_mk ((continuous_apply w).prodMk continuous_const) _

/-! ### Characters on the cell -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

/-- `conj e_∞(ν ·)` is `Λ_M`-periodic when `M` is valid for `ν`. -/
theorem chiInf_transLat {ν : SInt 𝔪} (hV : ValidDepth hG Φ (ν : F) M) (b : transLat 𝔪 M)
    (x : InfinitePlace F → ℂ) :
    chiInf (ν : F) ((b : InfinitePlace F → ℂ) + x) = chiInf (ν : F) x := by
  obtain ⟨b₀, hb₀, hb⟩ := b.2
  have h1 : chiInf (ν : F) (b : InfinitePlace F → ℂ) = 1 := by
    rw [← hb, embR_apply, chiInf_emb, eInf_emb_eq hG.ne_bot,
      C3B.sAddChar_of_mem _ (mul_mem ν.2 b₀.2), hV.char _ hb₀]
    simp
  rw [chiInf_add, h1, one_mul]

include hz6 in
/-- **The Fourier coefficients of `E_Φ` at the cusp `∞`** (MATH2 §0.2, (B5)/(B6)), every
frequency `ν ∈ R` for which the depth `M` is valid. -/
theorem fourier_coeff_oai (ν : SInt 𝔪) (hV : ValidDepth hG Φ (ν : F) M) (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s * (∫ x in D, chiInf (ν : F) x)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) := by
  set c₀ : ℂ := Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s with hc₀
  set R : (InfinitePlace F → ℂ) → ℂ := fun x =>
    ∑' p : IdxI 𝔪 M × transLat 𝔪 M,
      hI hG Φ s v M p.1 ((p.2 : InfinitePlace F → ℂ) + x) with hR
  have hE : ∀ x : InfinitePlace F → ℂ,
      eis (Φ.twist hG hz6) s (X.mk x v hv) = c₀ + R x := by
    intro x
    rw [eis_eq_add_tsum_Tfun hG hz6 Φ hs, ← tsum_hI_eq hG hz6 Φ s v hv M hV x]
    rfl
  have hm : ∀ i, Measurable (hI hG Φ s v M i) := fun i => measurable_hKer _ _ _ s hv
  have hfin := tsum_lintegral_hI_ne_top hG hz6 Φ s v hv M hV hs
  have hχm : Measurable (chiInf (ν : F)) := (continuous_chiInf _).measurable
  have hχ1 : ∀ x, ‖chiInf (ν : F) x‖ ≤ 1 := fun x => (norm_chiInf _ x).le
  obtain ⟨hsum, hunf⟩ := integral_unfold (transLat 𝔪 M) hD (hI hG Φ s v M) hm hfin
    (chiInf (ν : F)) hχm hχ1 (chiInf_transLat hG Φ M hV)
  have hLfin := lintegral_tsum_unfold_ne_top (transLat 𝔪 M) hD (hI hG Φ s v M) hm hfin
    (chiInf (ν : F)) hχm hχ1
  have hcont : Continuous fun x : InfinitePlace F → ℂ =>
      eis (Φ.twist hG hz6) s (X.mk x v hv) :=
    (continuous_eis hG.ne_bot _ hs).comp (continuous_mk_x v hv)
  have hRm : Measurable R := by
    have e : R = fun x => eis (Φ.twist hG hz6) s (X.mk x v hv) - c₀ := funext fun x => by
      rw [hE]; ring
    rw [e]
    exact hcont.measurable.sub measurable_const
  have hint2 : Integrable (fun x => R x * chiInf (ν : F) x) (volume.restrict D) :=
    ⟨(hRm.mul hχm).aestronglyMeasurable, lt_top_iff_ne_top.mpr hLfin⟩
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hDfin⟩
  have hint1 : Integrable (fun x => c₀ * chiInf (ν : F) x) (volume.restrict D) :=
    (Integrable.of_bound hχm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hχ1)).const_mul c₀
  calc ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = ∫ x in D, (c₀ * chiInf (ν : F) x + R x * chiInf (ν : F) x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          change eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x = _
          rw [hE]; ring)
    _ = (∫ x in D, c₀ * chiInf (ν : F) x) + ∫ x in D, R x * chiInf (ν : F) x :=
        integral_add hint1 hint2
    _ = _ := by
        rw [integral_const_mul, hunf, tsum_integral_hI hG hz6 Φ s v hv M ν hV hsum]

end ArtinKP.B
end
end

theorem solution.{u_1} : type_of% @ArtinKP.B.fourier_coeff_oai.{u_1} := @ArtinKP.B.fourier_coeff_oai.{u_1}
