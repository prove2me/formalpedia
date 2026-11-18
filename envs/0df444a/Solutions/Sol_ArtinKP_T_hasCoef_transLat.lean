-- Prove2me | solution 1 for ArtinKP.T.hasCoef_transLat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:28.834852+00:00
-- url     : https://prove2.me/submissions/39804315-440a-4b18-83e6-7bcf022c68d6

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
import Theorems.Thm_ArtinKP_B_fourier_coeff

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
-- module Solutions.Artin.KP.B_FourArch
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

theorem chiInf_add (ν : F) (x y : InfinitePlace F → ℂ) :
    chiInf ν (x + y) = chiInf ν x * chiInf ν y := by
  rw [chiInf, mul_add, eInf_add, map_mul]
  rfl

theorem chiInf_emb (ν a : F) : chiInf ν (emb a) = conj (eInf (emb (ν * a))) := by
  rw [chiInf, emb_mul]

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-! ### Shifted kernels -/

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
-- module Solutions.Artin.KP.B_FourThm
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

/-! ### Characters on the cell -/

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

theorem exists_chiInf_ne_one {ν : F} (hν : ν ≠ 0) :
    ∃ y : InfinitePlace F → ℂ, chiInf ν y ≠ 1 := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha : w₀.embedding ν ≠ 0 := (map_ne_zero _).mpr hν
  refine ⟨Pi.single w₀ (1 / (4 * w₀.embedding ν)), ?_⟩
  rw [chiInf_eq_prod, Finset.prod_eq_single w₀ (fun w _ hw => by
    rw [Pi.single_eq_of_ne hw, mul_zero, archChar_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Pi.single_eq_same]
  have e : -(-(w₀.embedding ν)) * (1 / (4 * w₀.embedding ν)) = ((1 / 4 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [e, archChar_eq_re, Complex.ofReal_re]
  have e2 : 2 * (Real.pi : ℂ) * Complex.I * ((2 * (1 / 4 : ℝ) : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e2, Complex.exp_pi_mul_I]
  norm_num

/-- A non-trivial character integrates to `0` over a fundamental cell of a group of periods. -/
theorem setIntegral_chiInf_eq_zero {ν : F} (hν : ν ≠ 0)
    (L : AddSubgroup (InfinitePlace F → ℂ)) [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain L D volume)
    (hper : ∀ (b : L) (x : InfinitePlace F → ℂ),
      chiInf ν ((b : InfinitePlace F → ℂ) + x) = chiInf ν x) :
    ∫ x in D, chiInf ν x = 0 := by
  obtain ⟨y, hy⟩ := exists_chiInf_ne_one hν
  have : VAddCommClass (InfinitePlace F → ℂ) L (InfinitePlace F → ℂ) :=
    ⟨fun a b c => by
      change a + ((b : InfinitePlace F → ℂ) + c) = (b : InfinitePlace F → ℂ) + (a + c)
      abel⟩
  have hD' : IsAddFundamentalDomain L (y +ᵥ D) volume := hD.vadd_of_comm y
  have h1 : ∫ x in D, chiInf ν x = ∫ x in y +ᵥ D, chiInf ν x :=
    hD.setIntegral_eq hD' (fun g x => hper g x)
  have h2 : ∫ x in y +ᵥ D, chiInf ν x = ∫ x in D, chiInf ν (y + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℂ))
      y).setIntegral_image_emb (MeasurableEquiv.addLeft y).measurableEmbedding (chiInf ν) D
    exact this
  simp only [chiInf_add] at h2
  rw [integral_const_mul] at h2
  have h3 : (1 - chiInf ν y) * ∫ x in D, chiInf ν x = 0 := by
    rw [sub_mul, one_mul, ← h2, ← h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hy))

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
/-- **The `ν`-th Fourier coefficient, `ν ≠ 0`**: `vol(𝔩_M)⁻¹ · W_s(ν; v) · 𝔞_Φ(ν, s)`. -/
theorem fourier_coeff_ne_zero (ν : SInt 𝔪) (hν : ν ≠ 0) (hV : ValidDepth hG Φ (ν : F) M)
    (hs : 2 < s.re) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) := by
  have hνF : (ν : F) ≠ 0 := fun h => hν (Subtype.ext h)
  rw [fourier_coeff hG hz6 Φ s v hv M ν hV hs hD hDfin,
    setIntegral_chiInf_eq_zero hνF (transLat 𝔪 M) hD (chiInf_transLat hG Φ M hV), mul_zero,
    zero_add]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_Kub
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

theorem kubota_aSer (s : ℂ) : (kubota hG hz6).aSer Φ ν s = aCoeff hG hz6 Φ ν s := rfl

/-- `Lam` is `S.lam` at any valid depth. -/
theorem LamR_eq_lam {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (c : SInt 𝔪) (s : ℂ) :
    S2.LamR (psiS hG.ne_bot) hG Φ c ν s = lam (psiS hG.ne_bot) M Φ (c : F) (ν : F) s :=
  S2.Lam_eq_lam (psiS hG.ne_bot) hG Φ ⟨hV.unip, hV.char⟩ (c : F) s

theorem aCoeff_eq {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (s : ℂ) :
    aCoeff hG hz6 Φ ν s = ∑' a : Cls (SInt 𝔪),
      gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
        * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) :=
  tsum_congr fun a => by rw [kTerm, LamR_eq_lam hG Φ ν hV]

/-- **The `ν`-th Fourier coefficient of `E_Φ` at `∞`** (`ν ≠ 0`):
`∫_D E(x, v) conj e_∞(νx) dx = vol(𝔩_M)⁻¹ · W_s(ν; v) · D.aSer Φ ν s`. -/
theorem fourier_coeff_aSer (hν : ν ≠ 0) {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) {s : ℂ}
    (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v * (kubota hG hz6).aSer Φ ν s := by
  rw [kubota_aSer, aCoeff_eq hG hz6 Φ ν hV]
  exact fourier_coeff_ne_zero hG hz6 Φ s v hv M ν hν hV hs hD hDfin

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # WP-T, file 1: strict cells of commensurable lattices (Mathlib only)

`PCell L D`: `D` is a measurable *strict* fundamental set of the subgroup `L` of `E` (every point
has exactly one translate in `D`) — the `hfund` form of WP-X2/WP-RF.

* `PCell.union`: if `L ≤ L₁` and `rep : κ → L₁` is a finite system of representatives of `L₁/L`,
  then `⋃_k (rep k + D)` is a strict cell of `L`.
* `exists_reps`: representatives from `L.relIndex L₁ ≠ 0`.
* **`mean_eq`**: let `D₁`, `D₂` be strict cells of `L₁`, `L₂`, `L ≤ L₁ ⊓ L₂` of finite index in
  both, `f` an `L₁`-periodic function, and suppose `∫_{t + D₂} f = I` for the representatives `t`
  of `L₂/L`.  Then `vol(D₂)·∫_{D₁} f = vol(D₁)·I`.
-/

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]

variable {L L₁ L₂ : AddSubgroup E} {D D₁ D₂ : Set E}

theorem PCell.isAddFundamentalDomain (h : PCell L D) (μ : Measure E) :
    IsAddFundamentalDomain L D μ :=
  IsAddFundamentalDomain.mk' h.meas.nullMeasurableSet fun x => h.fund x

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
/-! # WP-T, file 3: the lattices `Λ_Γ` (translations of `Γ`) and `Λ_M` (`B.transLat 𝔪 M`)

Both sit in `latO F = emb(𝓞_F)` (for `M ≥ 0`) and contain the image of a nonzero ideal, hence are
commensurable: `relIndex_inf_left/right`.

* `pcell_of_hfund`: WP-X2/WP-RF's `hfund` is a strict cell `T.PCell (N.latN Γ) D`;
  `exists_pcell_latN`.
* `exists_pcell_transLat`: a bounded strict cell of `Λ_M` (`M ≥ 0`), as a union of translates of a
  cell of `emb(𝓞_F)`;  `cellM 𝔪 M` (a chosen one, bounded by `cellN 𝔪 M`).
* `kap 𝔪 M = (vol(cellM 𝔪 M) · vol(𝔩_M))⁻¹` — the constant of all coefficient formulas
  (`= covol(𝓞_F)⁻¹` by WP-B's stub B-2; independent of the chosen cell: `volume_eq_cellM`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

/-! ### Ideal lattices -/

/-! ### The two families of lattices -/

/-! ### Cells -/

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne


theorem pcell_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : PCell (transLat 𝔪 M) (cellM 𝔪 M) := by
  unfold cellM
  rw [dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.1

lemma vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M := by
  unfold vol
  refine Finset.prod_pos fun v _ => zpow_pos ?_ _
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)

lemma volume_toReal_pos {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (h : PCell L D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) :
    0 < (volume D).toReal :=
  ENNReal.toReal_pos ((h.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _))
    (volume_ne_top_of_bdd hb)

/-- All cells of `Λ_M` have the volume of `cellM`. -/
theorem volume_eq_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) : volume D = volume (cellM 𝔪 M) :=
  hD.measure_eq ((pcell_cellM h𝔪 hM).isAddFundamentalDomain volume)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {hG hz6 Φ ν}

theorem hasCoef_transLat_oai (hν : ν ≠ 0) {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ (ν : F) M)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : HasCoef hG hz6 Φ ν D (kap 𝔪 M) := by
  intro s hs v hv
  have h𝔪 := hG.ne_bot
  rw [fourier_coeff_aSer hG hz6 Φ ν hν hV hs v hv (hD.isAddFundamentalDomain volume)
    (volume_ne_top_of_bdd hb)]
  have hc := volume_toReal_pos hD hb
  rw [kap, ← volume_eq_cellM h𝔪 hM (hD.isAddFundamentalDomain volume)]
  have hc0 : (((volume D).toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hV0 : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos 𝔪 M).ne'
  push_cast
  field_simp

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

theorem solution.{u_1} : type_of% @ArtinKP.T.hasCoef_transLat_oai.{u_1} := @ArtinKP.T.hasCoef_transLat_oai.{u_1}
