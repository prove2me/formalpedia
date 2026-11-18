-- Prove2me | solution 1 for ArtinKP.F.zPsi_smul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:12:26.985216+00:00
-- url     : https://prove2.me/submissions/7e5c63bd-98fc-43f2-91f5-df33a1a63714

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
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_B1_summable_sHt_rpow
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_Acoef_cross
import Theorems.Thm_ArtinKP_N_Acoef_eq
import Theorems.Thm_ArtinKP_N_cf_eis
import Theorems.Thm_ArtinKP_N_differentiableOn_Acoef
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_N_tendsto_ray_Acoef
import Theorems.Thm_ArtinKP_N2_zRes_eq_zPsi

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

lemma pairDen_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairDen c d P :=
  Finset.prod_pos fun w _ => H3.rowDen_pos (by simpa using h) (P w)

lemma pairHt_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairHt c d P :=
  div_pos (ht_pos P) (pairDen_pos h P)

end X

/-! ### Topology and measure -/

lemma X.continuous_ht : Continuous (X.ht : X F → ℝ) :=
  continuous_finsetProd _ fun w _ => X.continuous_v w

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.isCompact_box {m M B : ℝ} (hm : 0 < m) : IsCompact (H3.box m M B) := by
  have hind : Topology.IsInducing (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) :=
    Topology.IsInducing.subtypeVal
  have himg : (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) '' (H3.box m M B) =
      Metric.closedBall (0 : ℂ) B ×ˢ Set.Icc m M := by
    ext ⟨z, t⟩
    constructor
    · rintro ⟨Q, ⟨h1, h2, h3⟩, hQ⟩
      have hz : H3.x Q = z := congrArg Prod.fst hQ
      have ht : H3.v Q = t := congrArg Prod.snd hQ
      rw [hz] at h1
      rw [ht] at h2 h3
      exact ⟨by simpa using h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : ‖z‖ ≤ B := by simpa using h1
      exact ⟨⟨(z, t), lt_of_lt_of_le hm h2⟩, ⟨h1', h2, h3⟩, rfl⟩
  exact hind.isCompact_iff.mpr (himg ▸ (isCompact_closedBall 0 B).prod isCompact_Icc)

omit [IsTotallyComplex F] in
theorem isCompact_siegelBox {m M B : ℝ} (hm : 0 < m) : IsCompact (siegelBox F m M B) := by
  have : siegelBox F m M B = Set.pi Set.univ fun _ : InfinitePlace F => H3.box m M B := by
    ext P; simp [siegelBox]
  rw [this]
  exact isCompact_univ_pi fun _ => H3.isCompact_box hm

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- `∏_{v ∈ S_f} max(|c|_v, |d|_v)`: B1's `X.sNorm` is WP-S's `normS`. -/
theorem sNorm_sPl (c d : F) : X.sNorm (sPl 𝔪) c d = normS 𝔪 c d := by
  unfold X.sNorm normS
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

/-- `S`-units in B1's sense are units of `R`. -/
theorem exists_unit_of_isSUnit (h𝔪 : 𝔪 ≠ ⊥) {u : F} (hu : IsSUnit (sPl 𝔪) u) :
    ∃ ε : (SInt 𝔪)ˣ, ((ε : SInt 𝔪) : F) = u :=
  ⟨⟨⟨u, (isSInt_iff h𝔪 u).mp hu.isSInt⟩, ⟨u⁻¹, (isSInt_iff h𝔪 _).mp hu.inv.isSInt⟩,
    Subtype.ext (mul_inv_cancel₀ hu.1), Subtype.ext (inv_mul_cancel₀ hu.1)⟩, rfl⟩

/-! ### The product formula for `S`-units -/

/-! ### Rows modulo `S`-units -/

/-- The `S`-normalized height of a row: `I_p(Q) / ‖p‖`. -/
theorem sHt_row (p : Row 𝔪) (Q : X F) :
    X.sHt (sPl 𝔪) (p.c : F) (p.d : F) Q = X.pairHt (p.c : F) (p.d : F) Q / p.norm := by
  unfold X.sHt Row.norm
  rw [sNorm_sPl]

/-! ### Convergence of the height series over row classes (from WP-B1) -/

lemma rowClass_family_inj (h𝔪 : 𝔪 ≠ ⊥) (i j : RowClass 𝔪)
    (h : ∃ u : F, IsSUnit (sPl 𝔪) u ∧
      ((j.out.c : F), (j.out.d : F)) = (u * (i.out.c : F), u * (i.out.d : F))) : i = j := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨ε, rfl⟩ := exists_unit_of_isSUnit h𝔪 hu
  have hj : j.out = ε • i.out := by
    refine Row.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [Row.smul_c]; exact congrArg Prod.fst he
    · rw [Row.smul_d]; exact congrArg Prod.snd he
  rw [← RowClass.mk_out i, ← RowClass.mk_out j, hj, RowClass.mk_smul]

/-- **(B1)** `∑_q ht_q(Q)^σ < ∞` for `σ > 2`, over row classes. -/
theorem RowClass.summable_ht_rpow [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (Q : X F) {σ : ℝ}
    (hσ : 2 < σ) : Summable fun q : RowClass 𝔪 => q.ht Q ^ σ :=
  summable_sHt_rpow (sPl 𝔪) (fun q : RowClass 𝔪 => ((q.out.c : F), (q.out.d : F)))
    (fun _ => ⟨isSInt_coe h𝔪 _, isSInt_coe h𝔪 _⟩) (fun q => q.out.ne_zero)
    (rowClass_family_inj h𝔪) Q hσ

/-! ### The summand and the series -/

/-! ### Height form (MATH2 §0.2) -/

section height

variable {ι : F →+* ℂ}

/-! ### Bounds and convergence -/

/-- `|Ψ_s(q) I_q(Q)^s| ≤ B · ht_q(Q)^{Re s}`, `B` uniform on `‖s‖ ≤ M` (and in `Q`, `q`). -/
theorem exists_norm_term_le (Ψ : TSection ι 𝔪) (M : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ (Q : X F) (q : RowClass 𝔪),
      ‖term (Ψ s) s Q q.out‖ ≤ B * q.ht Q ^ s.re := by
  obtain ⟨B, hB⟩ := Ψ.bound M
  refine ⟨max B 0, le_max_right _ _, fun s hs Q q => ?_⟩
  have hI := X.pairHt_pos q.out.ne_zero Q
  have hn := q.out.norm_pos
  have h1 := hB s hs q.out
  have e : q.ht Q ^ s.re
      = q.out.norm ^ (-s.re) * X.pairHt (q.out.c : F) (q.out.d : F) Q ^ s.re := by
    unfold RowClass.ht
    rw [sHt_row, Real.div_rpow hI.le hn.le, Real.rpow_neg hn.le]
    ring
  unfold term
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hI, e, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.rpow_nonneg hI.le _)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn.le _)

variable [IsTotallyComplex F]

/-- **Absolute convergence** for `Re s > 2`. -/
theorem summable_norm_term (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    Summable fun q : RowClass 𝔪 => ‖term (Ψ s) s Q q.out‖ := by
  obtain ⟨B, -, hB⟩ := exists_norm_term_le Ψ ‖s‖
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hB s le_rfl Q q)
    ((RowClass.summable_ht_rpow h𝔪 Q hs).mul_left B)

theorem summable_term (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    Summable fun q : RowClass 𝔪 => term (Ψ s) s Q q.out :=
  (summable_norm_term h𝔪 Ψ hs Q).of_norm

theorem hasSum_eis (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    HasSum (fun q : RowClass 𝔪 => term (Ψ s) s Q q.out) (eis Ψ s Q) :=
  (summable_term h𝔪 Ψ hs Q).hasSum

end height

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B0, part 2: regularity, automorphy, the term at `(0, 1)`

* `continuousOn_eis`: joint continuity of `(s, Q) ↦ E_Ψ(Q, s)` on `{Re s > 2} × X`;
  `continuous_eis`, `measurable_eis` (in `Q`); `differentiableOn_eis` (holomorphy in `s`).
* `eis_smul`: `E_Ψ(γ • Q) = E_{γ⁻¹·Ψ}(Q)` for `γ ∈ SL₂(R)` (the action on `X` through `toF 𝔪`),
  equivalently `eis_translate`: `E_{γ·Ψ}(Q) = E_Ψ(γ⁻¹ • Q)`.
* `TSection.stab Ψ`, `eis_smul_of_mem_stab`; `exists_level_eis`, `exists_level_eis_invariant`.
* `eis_eq_add`: `E_Ψ = Ψ_s(0,1) ht^s + ∑_{q ≠ ∞} Ψ̃_s(q) ht_q^s`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Local compactness of `X` -/

/-! ### Regularity of the summands -/

/-! ### Automorphy by reindexing -/

theorem _root_.ArtinKP.S.TSection.mem_stab {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)} :
    γ ∈ Ψ.stab ↔ ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p := Iff.rfl

/-! ### The term at the class of `(0, 1)` -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem continuous_mk_x (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    Continuous fun x : InfinitePlace F → ℂ => X.mk x v hv := by
  refine continuous_pi fun w => ?_
  exact Continuous.subtype_mk ((continuous_apply w).prodMk continuous_const) _

/-! ### Characters on the cell -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

section PiDensity

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type*} [Fintype ι]

/-- Tonelli on a finite product, for a product of functions of one coordinate each. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))]

/-- A product of measures with densities is the product measure with the product density. -/
theorem pi_withDensity {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h : ∀ x : ∀ i, α i, (Set.pi univ s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, forall_true_left, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  simp_rw [h]
  rw [lintegral_fintype_prod_eq_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ### One factor -/

/-! ### The product -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Holo
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 2: bounded holomorphic families are holomorphic into `L²(Γ\X)`

Finite volume is a hypothesis here (`hvol : X.quotVol Γ univ < ⊤`; WP-RC's `quotVol_univ_lt_top`).

* `l2Rep_of_bdd`, `norm_toL2_le`: a bounded measurable `Γ`-invariant function is in `L²(Γ\X)`,
  with norm `≤ vol^{1/2} · sup`.
* `norm_sub_sub_le`: second-order Cauchy/Schwarz estimate
  `|f(z) − f(c) − (z−c) f'(c)| ≤ 4B R⁻² |z−c|²` for `f` holomorphic and bounded by `B` on `B(c,R)`.
* `differentiable_toL2`: if `s ↦ f_s(P)` is entire for every `P` and `f` is bounded on
  `ball × X` near every `s₀`, then `s ↦ [f_s] ∈ L²(Γ\X)` is entire.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.X

noncomputable section

/-- Second-order estimate for a bounded holomorphic function on a disc. -/
lemma norm_sub_sub_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ ball c R) :
    ‖f z - f c - (z - c) * deriv f c‖ ≤ 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have hD : ∀ w ∈ ball c R, ‖dslope f c w‖ ≤ 2 * B / R := fun w hw =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hw
  have hdD : DifferentiableOn ℂ (dslope f c) (ball c R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds c hR)).mpr hd
  have hm2 : MapsTo (dslope f c) (ball c R) (closedBall (dslope f c c) (4 * B / R)) :=
    fun w hw => by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖dslope f c w - dslope f c c‖ ≤ ‖dslope f c w‖ + ‖dslope f c c‖ := norm_sub_le _ _
        _ ≤ 2 * B / R + 2 * B / R := add_le_add (hD w hw) (hD c hc)
        _ = 4 * B / R := by ring
  have h2 := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdD hm2 hz
  rw [dist_eq_norm, dist_eq_norm, dslope_same] at h2
  rcases eq_or_ne z c with rfl | hne
  · simp
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hne
    have e : f z - f c - (z - c) * deriv f c = (z - c) * (dslope f c z - deriv f c) := by
      rw [dslope_of_ne _ hne, slope_def_module, smul_eq_mul]
      field_simp
    rw [e, norm_mul]
    calc ‖z - c‖ * ‖dslope f c z - deriv f c‖ ≤ ‖z - c‖ * (4 * B / R / R * ‖z - c‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by ring

/-- The derivative of a bounded holomorphic function at the centre of a disc. -/
lemma norm_deriv_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) :
    ‖deriv f c‖ ≤ 2 * B / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have := Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hc
  rwa [dslope_same] at this

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-X2, file 9: product coordinates `(x, v)` on `X` (stub S3 of WP-X)

`X.measurePreserving_xv`: the map `P ↦ (P.x, P.v) : X F → (ι → ℂ) × (ι → ℝ)` carries `X.vol F`
to `volume.prod (X.nuV F)`, `X.nuV F = ∏_w dv_w / v_w³` on `(0,∞)^ι`.  Hence integrals over `X`
and over strips `{x ∈ D}` are iterated integrals (`X.lintegral_xv`, `X.setLIntegral_strip`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

lemma amb_eq_prod : amb = (volume : Measure ℂ).prod nu1 := by
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold nu1
  rw [prod_withDensity_right (by fun_prop), h2]
  rfl

lemma measurePreserving_coe : MeasurePreserving H3.coe H3.vol ((volume : Measure ℂ).prod nu1) :=
  ⟨H3.measurableEmbedding_coe.measurable, map_val_vol.trans amb_eq_prod⟩

variable (F : Type*) [Field F] [NumberField F]

lemma X.nuV_eq : X.nuV F =
    (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun v => ∏ w, ENNReal.ofReal ((v w ^ 3)⁻¹)) := by
  unfold X.nuV nu1
  exact pi_withDensity _ _ (fun _ => by fun_prop)

/-- **Product coordinates**: `P ↦ (x, v)` carries the invariant measure to
`dx ⊗ ∏_w dv_w / v_w³`. -/
theorem X.measurePreserving_xv :
    MeasurePreserving (fun P : X F => (P.x, P.v)) (X.vol F)
      ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
  have h2 : MeasurePreserving (fun (P : X F) w => H3.coe (P w)) (X.vol F)
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ).prod nu1) :=
    measurePreserving_pi (fun _ => H3.vol) (fun _ => (volume : Measure ℂ).prod nu1)
      (fun _ => measurePreserving_coe)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
    (fun _ => (volume : Measure ℂ)) (fun _ => nu1)
  exact h3.comp h2

variable {F}

lemma X.measurable_xv : Measurable fun P : X F => (P.x, P.v) :=
  (X.measurePreserving_xv F).measurable

/-- Integrals over `X` in product coordinates. -/
theorem X.lintegral_xv {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ P, f (P.x, P.v) ∂X.vol F = ∫⁻ x, ∫⁻ v, f (x, v) ∂X.nuV F := by
  rw [← lintegral_prod _ hf.aemeasurable]
  exact (X.measurePreserving_xv F).lintegral_comp hf

/-- Integrals over a strip `{x ∈ D}` are iterated integrals `∫_D dx ∫ ∏ dv/v³`. -/
theorem X.setLIntegral_strip {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in (X.x ⁻¹' D : Set (X F)), f (P.x, P.v) ∂X.vol F =
      ∫⁻ x in D, ∫⁻ v, f (x, v) ∂X.nuV F := by
  have hm : MeasurableSet (X.x ⁻¹' D : Set (X F)) :=
    (measurable_fst.comp X.measurable_xv) hD
  rw [← lintegral_indicator hm, ← lintegral_indicator hD]
  have h1 : ∀ P : X F, (X.x ⁻¹' D : Set (X F)).indicator (fun P => f (P.x, P.v)) P =
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p) (P.x, P.v) := by
    intro P
    by_cases h : P.x ∈ D
    · simp [h]
    · simp [h]
  simp_rw [h1]
  refine (X.lintegral_xv (f := fun p => D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p)
    (((measurable_const.indicator hD).comp measurable_fst).mul hf)).trans ?_
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ D
  · simp [h]
  · simp [h]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Linear
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 6: functionals and linearity in `Ψ`

* `differentiableOn_functional_resPart`, `tendsto_ray_functional`: for a bounded functional `ℓ`
  on `L²(Γ\X)` (e.g. `X.coeffFunctional Γ n ψ …`), `s ↦ ℓ(−Res(λ(s))[F_s])` is holomorphic on
  `Omega` and `(s_t − s₀) ℓ(…) → ℓ(θ_Ψ)` along the ray.
* `coeffFunctional_resPart`: for `Re s > 2` the local pairing of the resolvent expression is the
  integral of `u_s = E_Ψ − h_s` over the box.
* linearity: `src_add`, `src_smul`, `hpart_add`, `hpart_smul`, `Inv.add`, `Inv.smul`,
  `srcL2_add`, `srcL2_smul`, `resPart_add`, `resPart_smul`, `theta_add`, `theta_smul`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Linearity of the weights -/

lemma Inv.smul {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (h : Inv Γ Ψ) (c : ℂ) :
    Inv Γ (c • Ψ) := fun γ hγ => TSection.mem_stab.mpr fun s p => by
  rw [TSection.smul_apply, TSection.smul_apply, TSection.mem_stab.mp (h γ hγ) s p]

/-! ### Linearity of the classes, of the resolvent part and of `θ` -/

/-! ### Functionals -/

/-! ### A bound for the cut-off part on compact sets -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.N_Orbit
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 1: the `x`-integral of the tail of `E_Ψ` over a cell of the translations of `Γ`

For `Γ ≤ SL₂(𝓞_F)` fixing the twisted section `Ψ`, `Λ_Γ = {β : n(β) ∈ Γ}` (`lamN Γ`, embedded in
`ℂ^r` as `latN Γ`) and `D` a fundamental domain of `latN Γ`:

* `tail Ψ s Q = E_Ψ(Q, s) − Ψ_s(0,1)·ht(Q)^s` (no hypotheses in the definition);
* `exists_integral_tail`: for `Re s > 2` there is a constant `C` with
  `∫_D tail Ψ s (x, v) dx = C · ∏_w v_w^{2−s}` for **all** `v`
  (the classes `≠ ∞` are unfolded along the free action of `Λ_Γ`, `orbN`; each full-space integral
  is a Jacquet integral at frequency `0`, WP-B's `integral_hKer` and WP-K's `jacquet_zero`);
* `integrableOn_tail`: the tail is integrable over `D`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### The translation lattice of `Γ` -/

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

variable {S : Finset (FinitePlace F)}

/-! ### The terms as shifted kernels -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The tail -/

/-! ### Finiteness of the unfolded `L¹` norm -/

lemma ht_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    X.ht (X.mk x v hv) = ∏ w, v w := by
  simp [X.ht]

/-! ### The integral over a cell -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 3: Fourier uniqueness on a strip of `X` (core of stub S1 (b))

Product coordinates `P ↦ (x, v) : X F → XV F = (ι → ℂ) × (ι → ℝ)` carry `X.vol` to Lebesgue
measure with density `dens v = ∏_w v_w⁻³` on `v > 0` (`map_xv`).  For a basis `bV` of `ι → ℂ`
(the lattice basis of the translations) and `n : ℕ`, the box
`{x ∈ cell bV} × [1/(n+1), n+1]^ι` lies in the cell of the basis `bE bV n = bV ⊕ (n+2)·e_w` of
`XV F`, whose characters are `chi bV m x · phiK n k v`.  Hence (`RF_Torus.ae_eq_zero_of_coeff`):

`measure_ne_zero_null`: a function on `X`, square integrable on that box, all of whose
coefficients against `chi bV m (x) · phiK n k (v)` over the box vanish, is `0` a.e. on the box.
No Fubini and no slicing: the `v`-directions are treated as further circle directions.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The density of `X.vol` in product coordinates -/

lemma measurableSet_posSet : MeasurableSet (posSet F) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

lemma measurable_dens : Measurable (dens : (InfinitePlace F → ℝ) → ℝ≥0∞) := by
  unfold dens
  refine Measurable.indicator ?_ measurableSet_posSet
  exact Finset.measurable_prod _ fun w _ => by fun_prop

lemma nuV_eq_withDensity : X.nuV F = (volume : Measure (InfinitePlace F → ℝ)).withDensity dens := by
  rw [X.nuV_eq]
  have h1 : (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0))
      = (volume : Measure (InfinitePlace F → ℝ)).restrict (posSet F) :=
    (Measure.restrict_pi_pi (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun _ => Ioi (0 : ℝ))).symm
  rw [h1, ← withDensity_indicator measurableSet_posSet]
  rfl

/-! ### Boxes in `v` -/

lemma measurableSet_vBox (n : ℕ) : MeasurableSet (vBox F n) := by
  have : vBox F n = ⋂ w, {v : InfinitePlace F → ℝ | 1 / ((n : ℝ) + 1) ≤ v w} ∩
      {v | v w ≤ (n : ℝ) + 1} := by
    ext v; simp [vBox, forall_and]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (measurableSet_le measurable_const (measurable_pi_apply w)).inter
      (measurableSet_le (measurable_pi_apply w) measurable_const)

lemma vBox_subset_posSet (n : ℕ) : vBox F n ⊆ posSet F := fun v hv w _ =>
  lt_of_lt_of_le (by positivity) (hv w).1

lemma dens_ne_zero {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) : dens v ≠ 0 := by
  unfold dens
  rw [indicator_of_mem (vBox_subset_posSet n hv)]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-! ### The basis of `XV F` adapted to a box -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-! ### A basis of the translation lattice -/

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

lemma Cell.vol_ne_zero {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (h : Cell Γ D n₀) :
    volume D ≠ 0 :=
  h.fund.measure_ne_zero (NeZero.ne _)

lemma Cell.mono {D : Set (InfinitePlace F → ℂ)} {n₀ n : ℕ} (h : Cell Γ D n₀) (hn : n₀ ≤ n) :
    Cell Γ D n :=
  ⟨h.meas, h.fund, fun x hx w => (h.bdd x hx w).trans (by exact_mod_cast hn)⟩

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

lemma continuous_htC (s : ℂ) : Continuous (htC s : X F → ℂ) := by
  unfold htC
  refine (Complex.continuous_ofReal.comp X.continuous_ht).cpow continuous_const fun P => ?_
  exact Or.inl (by simpa using X.ht_pos P)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S2.cubicSymbol_sym
/-! # WP-N, file 3: coefficients of `θ_Ψ` from continuations (MATH2 §2.1(c),(d); item 5)

* `differentiableAt_setIntegral`: a bounded holomorphic family integrates to a holomorphic function
  over a set of finite measure.
* `hInt Ψ n ψ s = ∫_{box n} conj ψ · h_s` is entire (`differentiable_hInt`).
* **`coeff_theta_of_continuation`** (all frequencies): if `a` is holomorphic on `E.slit`, equals
  `∫_{box n} conj ψ · E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀) a(s_t) → r` along C5's ray, then
  `∫_{box n} conj ψ · θ_Ψ = r`.
* **`cf_theta_of_continuation`** (frequency `0`, MATH2 §2.1(d)): if `m'` is holomorphic on `E.slit`,
  equals `mD D Ψ` for `Re s > 2` and `(s_t − s₀) m'(s_t) → z`, then
  `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for all `(n, φ)`.

`EisEigen Ψ s` (owner WP-RF) enters as the hypothesis `hE : ∀ s, 2 < s.re → EisEigen Ψ s`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

/-! ### Holomorphic dependence of integrals on a parameter -/

/-- A family `f s`, measurable in `a`, holomorphic in `s` on a disc and bounded there uniformly
on `K`, has a holomorphic integral over `K` (`μ K < ∞`). -/
theorem differentiableAt_setIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : Set α} (hK : MeasurableSet K) (hμ : μ K ≠ ⊤) {f : ℂ → α → ℂ} {s₀ : ℂ} {R B₀ : ℝ}
    (hR : 0 < R) (hmeas : ∀ s ∈ ball s₀ R, Measurable (f s))
    (hdiff : ∀ a ∈ K, DifferentiableOn ℂ (fun s => f s a) (ball s₀ R))
    (hB₀ : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B₀) :
    DifferentiableAt ℂ (fun s => ∫ a in K, f s a ∂μ) s₀ := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hμ.lt_top⟩
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B := fun s hs a ha =>
    (hB₀ s hs a ha).trans (le_max_left _ _)
  set g : α → ℂ := fun a => deriv (fun s => f s a) s₀ with hg
  have hgb : ∀ a ∈ K, ‖g a‖ ≤ 2 * B / R := fun a ha =>
    C5.norm_deriv_le hR (hdiff a ha) fun z hz => hB z hz a ha
  -- measurability of the derivative on `K`
  set k : ℕ → ℂ := fun n => ((R / 2 : ℝ) : ℂ) / ((n : ℂ) + 1) with hk
  have hk0 : ∀ n, k n ≠ 0 := fun n => by
    rw [hk]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Nat.cast_add_one_ne_zero n)
  have hkR : ∀ n, s₀ + k n ∈ ball s₀ R := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hk, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < R / 2)]
    have h1 : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc R / 2 / ‖((n : ℂ) + 1)‖ ≤ R / 2 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos h1
      _ < R := by linarith
  have hkt : Tendsto k atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (((R / 2 : ℝ) : ℂ))
    simpa [hk, div_eq_mul_inv] using this
  have hgK : Measurable (K.indicator g) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n => K.indicator fun a => (k n)⁻¹ * (f (s₀ + k n) a - f s₀ a))
      (fun n => (((hmeas _ (hkR n)).sub (hmeas _ hs₀)).const_mul _).indicator hK) ?_
    rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ K
    · simp only [indicator_of_mem ha]
      have h1 := ((hdiff a ha).differentiableAt (ball_mem_nhds s₀ hR)).hasDerivAt.tendsto_slope
      have h2 : Tendsto (fun n => s₀ + k n) atTop (𝓝[≠] s₀) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · simpa using (tendsto_const_nhds (x := s₀)).add hkt
        · simpa using hk0 n
      refine (h1.comp h2).congr fun n => ?_
      simp [slope_def_module]
    · simp only [indicator_of_notMem ha]
      exact tendsto_const_nhds
  have hgint : Integrable g (μ.restrict K) :=
    Integrable.of_bound (hgK.aestronglyMeasurable.congr (indicator_ae_eq_restrict hK))
      (2 * B / R) (ae_restrict_of_forall_mem hK hgb)
  have hfint : ∀ s ∈ ball s₀ R, Integrable (f s) (μ.restrict K) := fun s hs =>
    Integrable.of_bound (hmeas s hs).aestronglyMeasurable B
      (ae_restrict_of_forall_mem hK (hB s hs))
  refine (HasDerivAt.differentiableAt (f' := ∫ a in K, g a ∂μ) ?_)
  rw [hasDerivAt_iff_isLittleO]
  set V : ℝ := (μ.restrict K).real univ with hV
  have key : ∀ z ∈ ball s₀ R,
      ‖(∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ‖ ≤
        (4 * B / R ^ 2) * V * ‖z - s₀‖ ^ 2 := by
    intro z hz
    have e : (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ
        = ∫ a in K, (f z a - f s₀ a - (z - s₀) * g a) ∂μ := by
      have i1 : Integrable (fun a => f z a - f s₀ a) (μ.restrict K) :=
        (hfint z hz).sub (hfint s₀ hs₀)
      have i2 : Integrable (fun a => (z - s₀) * g a) (μ.restrict K) := hgint.const_mul _
      rw [integral_sub i1 i2, integral_sub (hfint z hz) (hfint s₀ hs₀), integral_const_mul,
        smul_eq_mul]
    rw [e]
    have hb' : ∀ a ∈ K, ‖f z a - f s₀ a - (z - s₀) * g a‖ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 :=
      fun a ha => C5.norm_sub_sub_le hR (hdiff a ha) (fun w hw => hB w hw a ha) hz
    have := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
      (ae_restrict_of_forall_mem hK hb')
    calc _ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 * V := this
      _ = _ := by ring
  have hO : (fun z => (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ)
      - (z - s₀) • ∫ a in K, g a ∂μ) =O[𝓝 s₀] fun z => ‖z - s₀‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((4 * B / R ^ 2) * V) ?_
    filter_upwards [ball_mem_nhds s₀ hR] with z hz
    rw [norm_pow, norm_norm]
    exact key z hz
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub s₀ one_lt_two)

/-! ### The ray and the slit -/

lemma isOpen_slit : IsOpen E.slit := by
  have h : E.slit = {s : ℂ | 1 < s.re} ∩ ({s : ℂ | s.im ≠ 0} ∪ {s : ℂ | 2 < s.re}) := by
    ext s
    simp only [E.slit, mem_ofPred_eq, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by by_cases h : s.im = 0; exacts [Or.inr (h2 h), Or.inl h]⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, fun h => absurd h h2⟩
      · exact ⟨h1, fun _ => h2⟩
  rw [h]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re))

lemma ray_mem_slit {t : ℝ} (ht : 0 < t) : ray t ∈ E.slit := by
  have hre : (ray t).re = 4 / 3 + t := by
    simp only [ray, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.I_re, Complex.div_ofNat_re, Complex.re_ofNat]
    ring
  have him : (ray t).im = t := by
    simp only [ray, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.I_im, Complex.div_ofNat_im, Complex.im_ofNat]
    ring
  exact ⟨by rw [hre]; linarith, fun h => by rw [him] at h; exact absurd h ht.ne'⟩

lemma continuous_ray : Continuous ray := by unfold ray; fun_prop

lemma tendsto_ray : Tendsto ray (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have h := continuous_ray.tendsto 0
  have h0 : ray 0 = 4 / 3 := by simp [ray]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_ray_mul_zero {g : ℂ → ℂ} (hg : ContinuousAt g (4 / 3)) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * g (ray t)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := hg.tendsto.comp tendsto_ray
  simpa using h1.mul h2

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The cut-off part against a bounded test function -/

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

theorem differentiable_cf_htC {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (n : ℕ)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    Differentiable ℂ fun s : ℂ => cf D n φ (htC s) := by
  intro s₀
  have hcont : Continuous fun z : ℂ × X F => ‖((X.ht z.2 : ℝ) : ℂ) ^ z.1‖ :=
    ((Complex.continuous_ofReal.comp (X.continuous_ht.comp continuous_snd)).cpow continuous_fst
      fun z => Or.inl (by simpa using X.ht_pos z.2)).norm
  obtain ⟨B, hB⟩ := ((isCompact_closedBall s₀ 1).prod (isCompact_box (F := F) n)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine differentiableAt_setIntegral (X.measurableSet_box n) (X.vol_box_lt_top n).ne
    (R := 1) (B₀ := B) one_pos
    (fun s _ => (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul
      (continuous_htC s).measurable)
    (fun P _ => ?_) (fun s hs P hP => ?_)
  · refine (Differentiable.const_mul ?_ _).differentiableOn
    unfold htC
    exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (X.ht_pos P).ne'))
  · rw [norm_mul, RCLike.norm_conj]
    have h1 := hB (s, P) ⟨ball_subset_closedBall hs, hP⟩
    rw [norm_norm] at h1
    calc ‖stripFn D 0 φ P‖ * ‖htC s P‖ ≤ 1 * ‖htC s P‖ :=
          mul_le_mul_of_nonneg_right (norm_stripFn_le D 0 hφ1 P) (norm_nonneg _)
      _ ≤ B := by rw [one_mul]; exact h1

/-- **MATH2 §2.1(d), transfer form.**  If `m'` continues `mD D Ψ` holomorphically to `E.slit`
and `(s_t − s₀)·m'(s_t) → z` along the ray, then the constant term of `θ_Ψ` at `∞` is
`z·ht^{2/3}`: `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for every test pair `(n, φ)`. -/
theorem cf_theta_of_continuation (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {m' : ℂ → ℂ}
    (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    cf D n φ (X.lift Γ (theta Γ Ψ)) = z * cf D n φ (htC (2 / 3)) := by
  have hP := differentiable_cf_htC hD.meas n hφ hφ1
  have hP2 : Differentiable ℂ fun s : ℂ => cf D n φ (htC (2 - s)) :=
    hP.comp ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hΨ : Differentiable ℂ fun s : ℂ => Ψ s (Row.inf 𝔪) := Ψ.holo _
  refine integral_box_theta_eq_of_tendsto_ray hG Γ hΓ hE n (stripFn D 0 φ) (measurable_stripFn hD.meas 0 hφ)
    1 (norm_stripFn_le D 0 hφ1)
    (a := fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s) + m' s * cf D n φ (htC (2 - s)))
    ((hΨ.mul hP).differentiableOn.add (hm'.mul hP2.differentiableOn)) (fun s hs => ?_) ?_
  · rw [hmeq s hs]
    exact (cf_eis hG.ne_bot hΓ hs hD hφ hφ1).symm
  · have h1 := tendsto_ray_mul_zero (g := fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s))
      (hΨ.mul hP).continuous.continuousAt
    have h2 := hz.mul ((hP2.continuous.tendsto (4 / 3)).comp tendsto_ray)
    have e : (2 : ℂ) - 4 / 3 = 2 / 3 := by norm_num
    rw [e] at h2
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun t => ?_
    simp only [Function.comp_apply]
    ring

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S2.cubicSymbol_sym
/-! # WP-N, file 4: the continued coefficient `mext`, its residue `zRes`, the constant term of `θ_Ψ`

MATH2 §2.1(c),(d) and the first step of §2.2, for a cell `D` of `Γ` and a box index `n ≥ 1`:

* `phase s₁`, `cf_phase_ne_zero`: a test function `φ` with `cf D n φ (ht^{s₁}) ≠ 0`.
* `Acoef Γ Ψ D n φ s = cf(Eext) − Ψ_s(0,1)·cf(ht^s)` (written with `resPart` and `hInt`), holomorphic
  on `E.slit`; `Acoef_cross`: `A_φ(s)·⟨ht^{2−s},φ'⟩ = A_{φ'}(s)·⟨ht^{2−s},φ⟩` on `E.slit`.
* `mext Γ Ψ D n`: holomorphic on `E.slit` (`differentiableOn_mext`), equal to `mD D Ψ` for `Re s > 2`
  (`mext_eq_mD`), and `Acoef = mext · ⟨ht^{2−s}, φ⟩` on `E.slit` (`Acoef_eq_mext`) — the shape of the
  constant term of the continuation.
* `zRes Γ Ψ D n = lim (s_t − s₀)·mext(s_t)` (`tendsto_ray_mext`), and
  **`cf_theta`**: `cf D n' φ' (θ_Ψ) = zRes · cf D n' φ' (ht^{2/3})`.
* `zRes_eq_of_continuation`, `zRes_eq_zero_of_theta`, `cf_theta_eq_zero`.
* **`theta_eq_zero_of_inner`**: `⟪[F_{4/3}], θ_Ψ⟫ = 0 → θ_Ψ = 0` (`‖θ‖² = −c₀⟪F, θ⟫`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### A test function that sees `ht^{s₁}` -/

lemma measurable_phase (s₁ : ℂ) : Measurable (phase (F := F) s₁) := by
  unfold phase
  have h : Measurable fun v : InfinitePlace F → ℝ => ((∏ w, v w : ℝ) : ℂ) ^ s₁ :=
    (Complex.measurable_ofReal.comp
      (Finset.measurable_prod _ fun w _ => measurable_pi_apply w)).pow_const s₁
  exact h.div (Complex.measurable_ofReal.comp h.norm)

lemma norm_phase_le (s₁ : ℂ) (v : InfinitePlace F → ℝ) : ‖phase s₁ v‖ ≤ 1 := by
  unfold phase
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

lemma norm_htC_pos (s₁ : ℂ) (P : X F) : 0 < ‖htC s₁ P‖ := by
  unfold htC
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos P)]
  exact Real.rpow_pos_of_pos (X.ht_pos P) _

lemma conj_phase_mul (s₁ : ℂ) (P : X F) :
    conj (phase s₁ P.v) * htC s₁ P = ((‖htC s₁ P‖ : ℝ) : ℂ) := by
  have hu : ((∏ w, P.v w : ℝ) : ℂ) ^ s₁ = htC s₁ P := rfl
  unfold phase
  rw [hu, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
  have h0 : ((‖htC s₁ P‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_htC_pos s₁ P).ne'
  field_simp

lemma volume_vBox_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure (InfinitePlace F → ℝ)) (vBox F n) ≠ 0 := by
  have h : vBox F n = Icc (fun _ : InfinitePlace F => 1 / ((n : ℝ) + 1))
      (fun _ : InfinitePlace F => (n : ℝ) + 1) := by
    ext v
    simp only [vBox, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [h, Real.volume_Icc_pi]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 1 / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'

lemma nuV_vBox_ne_zero {n : ℕ} (hn : 1 ≤ n) : X.nuV F (vBox F n) ≠ 0 := by
  rw [RF.nuV_eq_withDensity, withDensity_apply _ (measurableSet_vBox n)]
  intro h
  rw [lintegral_eq_zero_iff RF.measurable_dens] at h
  have h1 : ∀ᵐ v ∂(volume : Measure (InfinitePlace F → ℝ)), v ∉ vBox F n := by
    have h2 := (ae_restrict_iff' (measurableSet_vBox n)).mp h
    filter_upwards [h2] with v hv hmem
    exact RF.dens_ne_zero hmem (hv hmem)
  exact volume_vBox_ne_zero hn (measure_eq_zero_iff_ae_notMem.mpr h1)

lemma vol_box_strip_ne_zero {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    (hn : 1 ≤ n) : X.vol F ((X.box n : Set (X F)) ∩ X.x ⁻¹' D) ≠ 0 := by
  have hset : ((X.box n : Set (X F)) ∩ X.x ⁻¹' D) = X.v ⁻¹' vBox F n ∩ X.x ⁻¹' D := by
    ext P
    simp only [mem_inter_iff, mem_preimage, mem_box_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hD.bdd _ h.2, h.1⟩, h.2⟩⟩
  have hVm : MeasurableSet (X.v ⁻¹' vBox F n : Set (X F)) := X.measurable_v (measurableSet_vBox n)
  have h1 := X.setLIntegral_strip (F := F) hD.meas
    (f := fun p => (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) p.2)
    ((measurable_const.indicator (measurableSet_vBox n)).comp measurable_snd)
  have h2 : ∫⁻ P in (X.x ⁻¹' D : Set (X F)), (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) P.v
      ∂X.vol F = X.vol F (X.v ⁻¹' vBox F n ∩ X.x ⁻¹' D) := by
    have e : (fun P : X F => (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) P.v)
        = (X.v ⁻¹' vBox F n : Set (X F)).indicator 1 := by
      funext P
      by_cases hP : P.v ∈ vBox F n
      · rw [indicator_of_mem hP, indicator_of_mem (show P ∈ X.v ⁻¹' vBox F n from hP)]; rfl
      · rw [indicator_of_notMem hP, indicator_of_notMem (show P ∉ X.v ⁻¹' vBox F n from hP)]
    rw [e, lintegral_indicator_one hVm, Measure.restrict_apply hVm]
  have h3 : ∀ x : InfinitePlace F → ℂ,
      ∫⁻ v, (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) p.2) (x, v) ∂X.nuV F
        = X.nuV F (vBox F n) := fun _ => by
    simp only
    rw [lintegral_indicator (measurableSet_vBox n), setLIntegral_const, one_mul]
  rw [hset, ← h2, h1, lintegral_congr h3, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter]
  exact mul_ne_zero (nuV_vBox_ne_zero hn) hD.vol_ne_zero

/-- The functional `cf D n (phase s₁)` does not vanish on `ht^{s₁}`. -/
theorem cf_phase_ne_zero {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n) (hn : 1 ≤ n)
    (s₁ : ℂ) : cf D n (phase s₁) (htC s₁) ≠ 0 := by
  have hSm : MeasurableSet (X.x ⁻¹' D : Set (X F)) := X.measurable_x hD.meas
  have e : ∀ P : X F, conj (stripFn D 0 (phase s₁) P) * htC s₁ P
      = (X.x ⁻¹' D : Set (X F)).indicator (fun P => ((‖htC s₁ P‖ : ℝ) : ℂ)) P := by
    intro P
    rw [stripFn_zero]
    by_cases hP : P.x ∈ D
    · rw [indicator_of_mem hP, indicator_of_mem (show P ∈ X.x ⁻¹' D from hP), one_mul,
        conj_phase_mul]
    · rw [indicator_of_notMem hP, indicator_of_notMem (show P ∉ X.x ⁻¹' D from hP)]
      simp
  unfold cf
  simp only [e]
  rw [setIntegral_indicator hSm, integral_complex_ofReal, Ne, Complex.ofReal_eq_zero]
  have hint : IntegrableOn (fun P : X F => ‖htC s₁ P‖) ((X.box n : Set (X F)) ∩ X.x ⁻¹' D)
      (X.vol F) :=
    ((continuous_htC s₁).norm.continuousOn.integrableOn_compact (isCompact_box n)).mono_set
      inter_subset_left
  have hpos : 0 < ∫ P in (X.box n : Set (X F)) ∩ X.x ⁻¹' D, ‖htC s₁ P‖ ∂X.vol F := by
    rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun P => norm_nonneg _) hint]
    have hsupp : Function.support (fun P : X F => ‖htC s₁ P‖) = univ := by
      ext P
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (norm_htC_pos s₁ P).ne'
    rw [hsupp, Measure.restrict_apply_univ]
    exact pos_iff_ne_zero.mpr (vol_box_strip_ne_zero hD hn)
  exact hpos.ne'

/-! ### The coefficient function `Acoef` and the cross identity -/

section

variable (hG : Good 𝔪) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) {D : Set (InfinitePlace F → ℂ)} {n n' : ℕ}
  {φ φ' : (InfinitePlace F → ℝ) → ℂ}

/-! ### The continued coefficient and its residue -/

include hG hΓ hE in
/-- **The shape of the constant term of the continuation**: on `E.slit`,
`cf(Eext) − Ψ_s(0,1) cf(ht^s) = mext(s) · cf(ht^{2−s})` for every test pair. -/
theorem Acoef_eq_mext (hD : Cell Γ D n) (hn : 1 ≤ n) (hD' : Cell Γ D n') (hφ' : Measurable φ')
    (hφ1' : ∀ v, ‖φ' v‖ ≤ 1) {s : ℂ} (hs : s ∈ E.slit) :
    Acoef Γ Ψ D n' φ' s = mext Γ Ψ D n s * cf D n' φ' (htC (2 - s)) := by
  have h := Acoef_cross hG hΓ hE hD (measurable_phase (2 - s)) (norm_phase_le (2 - s)) hD' hφ'
    hφ1' hs
  unfold mext
  rw [div_mul_eq_mul_div, eq_div_iff (cf_phase_ne_zero hD hn (2 - s))]
  exact h.symm

include hG hΓ in
theorem mext_eq_mD (hD : Cell Γ D n) (hn : 1 ≤ n) {s : ℂ} (hs : 2 < s.re)
    (hEs : EisEigen Ψ s) : mext Γ Ψ D n s = mD D Ψ s := by
  unfold mext
  rw [Acoef_eq hG hΓ hD (measurable_phase (2 - s)) (norm_phase_le (2 - s)) hs hEs,
    mul_div_assoc, div_self (cf_phase_ne_zero hD hn (2 - s)), mul_one]

include hG hΓ hE in
theorem differentiableOn_mext (hD : Cell Γ D n) (hn : 1 ≤ n) :
    DifferentiableOn ℂ (mext Γ Ψ D n) E.slit := by
  intro s₁ hs₁
  refine DifferentiableAt.differentiableWithinAt ?_
  set φ₁ : (InfinitePlace F → ℝ) → ℂ := phase (2 - s₁) with hφ₁
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ₁ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n (measurable_phase _) (norm_phase_le _)).comp
      ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hne : ∀ᶠ s in 𝓝 s₁, cf D n φ₁ (htC (2 - s)) ≠ 0 :=
    hP.continuous.continuousAt.eventually_ne (cf_phase_ne_zero hD hn (2 - s₁))
  have heq : mext Γ Ψ D n =ᶠ[𝓝 s₁]
      fun s => Acoef Γ Ψ D n φ₁ s / cf D n φ₁ (htC (2 - s)) := by
    filter_upwards [hne, isOpen_slit.mem_nhds hs₁] with s hs hslit
    rw [eq_div_iff hs]
    exact (Acoef_eq_mext hG hΓ hE hD hn hD (measurable_phase _) (norm_phase_le _) hslit).symm
  have hA := (differentiableOn_Acoef hG hΓ hD.meas n (measurable_phase (2 - s₁))
    (norm_phase_le (2 - s₁)) s₁ hs₁).differentiableAt (isOpen_slit.mem_nhds hs₁)
  exact (hA.div (hP s₁) (cf_phase_ne_zero hD hn (2 - s₁))).congr_of_eventuallyEq heq

include hG hΓ hE in
/-- `(s_t − s₀)·mext(s_t) → zRes` along the ray. -/
theorem tendsto_ray_mext (hD : Cell Γ D n) (hn : 1 ≤ n) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * mext Γ Ψ D n (ray t)) (𝓝[>] 0)
      (𝓝 (zRes Γ Ψ D n)) := by
  set φ₁ : (InfinitePlace F → ℝ) → ℂ := phase (2 / 3) with hφ₁
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ₁ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n (measurable_phase _) (norm_phase_le _)).comp
      ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hPt : Tendsto (fun t : ℝ => cf D n φ₁ (htC (2 - ray t))) (𝓝[>] 0)
      (𝓝 (cf D n φ₁ (htC (2 / 3)))) := by
    have h := (hP.continuous.tendsto (4 / 3)).comp tendsto_ray
    have e : (2 : ℂ) - 4 / 3 = 2 / 3 := by norm_num
    rw [e] at h
    exact h
  have hne := cf_phase_ne_zero hD hn (2 / 3 : ℂ)
  have hA := tendsto_ray_Acoef hG hΓ hD.meas n (measurable_phase (2 / 3))
    (norm_phase_le (2 / 3))
  have hdiv := hA.div hPt hne
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hPt.eventually_ne hne] with t ht hnt
  simp only [Pi.div_apply]
  rw [Acoef_eq_mext hG hΓ hE hD hn hD (measurable_phase _) (norm_phase_le _) (ray_mem_slit ht)]
  field_simp
  rfl

include hG hΓ hE in
/-- The residue can be read off any holomorphic continuation of `mD D Ψ` to `E.slit`. -/
theorem zRes_eq_of_continuation (hD : Cell Γ D n) (hn : 1 ≤ n) {m' : ℂ → ℂ}
    (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    zRes Γ Ψ D n = z := by
  have h := cf_theta_of_continuation hG Γ hΓ hE hD (measurable_phase (2 / 3))
    (norm_phase_le (2 / 3)) hm' hmeq hz
  unfold zRes
  rw [h, mul_div_assoc, div_self (cf_phase_ne_zero hD hn (2 / 3 : ℂ)), mul_one]

end

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma latN_le_latO (Γ : Subgroup (SL(2, 𝓞 F))) : latN Γ ≤ latO F :=
  AddSubgroup.map_mono le_top

/-! ### The two families of lattices -/

theorem exists_idealLat_le_latN (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ idealLat 𝔫 ≤ latN Γ := by
  obtain ⟨𝔫, h𝔫, h⟩ := exists_ideal_translations Γ
  refine ⟨𝔫, h𝔫, ?_⟩
  rintro x ⟨β, hβ, rfl⟩
  obtain ⟨γ, hγ⟩ := h β hβ
  refine ⟨β, ?_, rfl⟩
  change nInt β ∈ Γ
  rw [← hγ, nInt_eq_of_GammaN]
  exact (γ : Γ).2

/-! ### Cells -/

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

lemma integrableOn_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {f : (InfinitePlace F → ℂ) → ℂ} (hf : Continuous f) :
    IntegrableOn f D volume := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hsub

lemma volume_toReal_pos {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (h : PCell L D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) :
    0 < (volume D).toReal :=
  ENNReal.toReal_pos ((h.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _))
    (volume_ne_top_of_bdd hb)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Linear
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 7: linearity

Twisted level (for the linear combinations of WP-F, which are not genuine sections):
* `eis_add`, `eis_smulFun` (`Re s > 2`); `HasCoefT.add`, `HasCoefT.smulFun`, `HasCoefT.unique`;
* `resSlit_congr`, `resSlit_add`, `resSlit_mul` (function level) and their forms with seeds
  `resSlit_add_of_seed`, `resSlit_mul_of_seed`: `Res(a₀ + b₀) = Res a₀ + Res b₀`,
  `Res(f·a₀) = f(4/3)·Res a₀` for entire `f`.

Genuine level:
* `aSer_add`, `aSer_smulFun`: the Kubota series is linear in `Φ` (`Re s > 2`), read off the
  Fourier coefficients;
* **`tau_add`, `tau_smulFun`, `tau_smul`**.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Function level -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Twisted sections -/

theorem eis_smulFun (h𝔪 : 𝔪 ≠ ⊥) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Ψ : TSection ι 𝔪)
    {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    eis (TSection.smulFun f hf Ψ) s Q = f s * eis Ψ s Q := by
  have h1 := (hasSum_eis h𝔪 Ψ hs Q).mul_left (f s)
  have h2 := hasSum_eis h𝔪 (TSection.smulFun f hf Ψ) hs Q
  refine h2.unique (h1.congr_fun fun q => ?_)
  simp only [term, TSection.smulFun_apply]
  ring

/-! ### Genuine sections -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Vanish
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 8: vanishing of the coefficients at characters outside the full dual lattice

Let `Γ`, `Γ'` be of finite index, both fixing `Ψ`, `D` a bounded strict cell of `Λ_Γ` and
`ν' ∈ RF.dualLat Γ`.  If `e_{ν'}(g) ≠ 1` for some `g ∈ Λ_{Γ'}`, then the `ν'`-th Fourier
coefficient over `D` vanishes: for the series (`integral_eis_eChar_eq_zero`, `Re s > 2`), for the
continuation (`Afun_eChar_eq_zero`, on `E.slit`) and for `θ_Ψ` (**`coeff_theta_eq_zero`**).

For a genuine section `Φ` the group `Γ'` can be taken with `Λ_{Γ'} ⊇ Λ_M` for every depth `M ≥ 0`
of unipotent invariance (`transLat_le_latN_stabGroup`), whence
**`coeff_theta_eq_zero_of_transLat`**: only the characters trivial on `Λ_M` contribute to `θ`.
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
  {ι : F →+* ℂ}

/-! ### Genuine sections: the stabilizer contains `n(Λ_M)` -/

section genuine

variable {P : CubicPkg F} (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪)

lemma inv_stabGroup (Ψ : TSection ι 𝔪) : Inv (stabGroup Ψ) Ψ := fun _ hγ => hγ

lemma le_stabGroup {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) :
    Γ ≤ stabGroup Ψ := fun γ hγ => hΓ γ hγ

include hG hz6 in
theorem finiteIndex_stabGroup (Pk : CubicPkg F) (Ψ : TSection ι 𝔪) :
    (stabGroup Ψ).FiniteIndex := by
  obtain ⟨Γ₀, hfi, hΓ₀⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  exact Subgroup.finiteIndex_of_le (le_stabGroup hΓ₀)

end genuine

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.F_Per_Mean
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 1: means over cells of admissible lattices; scaled lattices

* `Adm A`: the lattice `A ⊂ ℂ^r` lies between `emb(I)` (`I` a nonzero ideal) and `emb(𝓞_F)`.
  `latN Γ`, `transLat 𝔪 M` (`M ≥ 0`) and `scaleLat a (transLat 𝔪 M)` (`a ∈ R`, `M` large) are
  admissible.
* `mean_adm`: a continuous `A₁`-periodic function whose integrals over all translates of a cell of
  `A₂` are `vol·I` has integral `vol(D₁)·I` over every bounded strict cell of `A₁` (`T.mean_eq`).
* `scaleLat a L`, `scaleSet a D`: the lattice `a·L` and its cell `a·D`.
* `hasCoef_adm`: `T.hasCoef_latN` for cells of any admissible lattice of periods.
* `const_adm`: the constant term of `E_Φ` over such a cell (`B.const_term_mCoeff`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Admissible lattices -/

lemma countable_latO : Countable (latO F) :=
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  ((Set.to_countable ((⊤ : AddSubgroup (𝓞 F)) : Set (𝓞 F))).image embO).to_subtype

lemma Adm.countable {A : AddSubgroup (InfinitePlace F → ℂ)} (h : Adm A) : Countable A := by
  have := countable_latO (F := F)
  exact (AddSubgroup.inclusion_injective h.le).countable

lemma adm_latN (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] : Adm (latN Γ) :=
  ⟨latN_le_latO Γ, exists_idealLat_le_latN Γ⟩

/-! ### Scaled lattices and cells -/

/-! ### Coefficients over cells of admissible lattices -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.N2_Cor
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N2, file 5: Corollary N without hypotheses; the intrinsic residue `z_Ψ`

* **`corollaryN`**, **`corollaryN_of_continuation`**: `N.corollaryN`, `N.corollaryN_of_continuation`
  with both named hypotheses discharged (`CuspOrth` by `N2.cuspOrth`, `EisEigen` by `GL.eisEigen`).
* `corollaryN_reps`, `corollaryN_of_continuation_reps`: the same, testing only the finitely many
  cusps `cuspMat Γ o` (`o` a `Γ`-orbit of pair classes on which the weights of `Ψ` at `4/3` do not
  vanish).
* `zPsi Ψ`: the residue `z_Ψ` of the `ht^{2−s}`-coefficient of the constant term at `∞`, defined
  with a chosen level group and cell; **`zRes_eq_zPsi`**: every `zRes Γ Ψ D n` (`n ≥ 1`) equals it.
* `cf_theta_translate_zPsi`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞` is `z_{σ·Ψ}·ht^{2/3}`.
* **`theta_eq_zero_iff`**, **`theta_eq_zero_iff_reps`**: `θ_Ψ = 0` iff `z_{σ·Ψ} = 0` for all
  `σ ∈ SL₂(R)`, iff for the finitely many representatives.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-- `GL.eisEigen` in the form taken by `N_Main`. -/
theorem eisE (hG : Good 𝔪) : ∀ (Ψ' : TSection ι 𝔪) (s : ℂ), 2 < s.re → EisEigen Ψ' s :=
  fun Ψ' _ hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ' hs

section

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

/-! ### Corollary N -/

/-! ### The intrinsic residue -/

/-- `z_Ψ` from any holomorphic continuation of `mD D Ψ` to `E.slit`. -/
theorem zPsi_eq_of_continuation (hΓ : Inv Γ Ψ) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : Cell Γ D n) {m' : ℂ → ℂ} (hm' : DifferentiableOn ℂ m' E.slit)
    (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    zPsi Pk hG hz6 Ψ = z := by
  have hD1 : Cell Γ D (max n 1) := hD.mono (le_max_left _ _)
  rw [← zRes_eq_zPsi Pk hG hz6 hΓ hD1 (le_max_right _ _)]
  exact zRes_eq_of_continuation hG hΓ (eisE hG Ψ) hD1 (le_max_right _ _) hm' hmeq hz

end

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.F_Per_Const
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 4: the constant term of `E_{Ψρ_∞}` (Lemma 5.2 for `ρ_∞`, by Proposition 5.4)

MATH2 proves `m_{Φρ_∞} = m_Φ / L_P` by unfolding with a congruence condition.  Here it is read off
from Proposition 5.4 at the frequency `0`: `U E_Φ = N^{3s/2}[q^{3−3s} E_{Φ♯} + (1−q^{2−3s}) E_{Φ♯ρ_∞}]`,
the constant term of `U E_Φ` is `q³` times that of `E_Φ` at height `v/|π³|`, and
`m_{Φ♯} = |π|³ m_Φ`.  Result (`mD_restrict`): for every genuine section `Φ₁`, `Re s > 2`,

  `mD D (restrict (Φ₁.twist)) s = (1 − q^{3−3s})/(1 − q^{2−3s}) · mD D (Φ₁.twist) s`,

and hence `zPsi (restrict Ψ₁) = q/(q+1) · zPsi Ψ₁` (`zPsi_restrict`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Algebra -/

section general

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- `mD` in terms of the integral of the series (`Re s > 2`). -/
lemma mD_eq_integral (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (_hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hD0 : (((volume D).toReal : ℝ) : ℂ) ≠ 0) :
    mD D Ψ s = (((volume D).toReal : ℝ) : ℂ)⁻¹
        * (∫ x in D, eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))) - Ψ s (Row.inf 𝔪) := by
  have hfin := volume_ne_top_of_bdd hb
  have hi : IntegrableOn (fun x : InfinitePlace F → ℂ =>
      eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))) D volume := integrableOn_of_bdd hb
    ((continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x (fun _ => (1 : ℝ)) (fun _ => one_pos)))
  have hc : IntegrableOn (fun _ : InfinitePlace F → ℂ => Ψ s (Row.inf 𝔪)) D volume :=
    integrableOn_const hfin
  have e : ∀ x : InfinitePlace F → ℂ, tail Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))
      = eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos)) - Ψ s (Row.inf 𝔪) := fun x => by
    rw [tail, ht_mk]
    simp
  rw [mD]
  simp only [e]
  rw [integral_sub hi hc, setIntegral_const, measureReal_def, Complex.real_smul, mul_sub,
    ← mul_assoc, inv_mul_cancel₀ hD0, one_mul]

end general

/-! ### Powers of positive reals -/

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Z
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 5: the residue `z_Ψ` — linearity, translations, `ρ_∞`

* `zPsi_of_mD`: `z_Ψ` from a continuation of `mD D Ψ` over a strict cell.
* `zPsi_add`, `zPsi_smul`, `zPsi_sum`: `Ψ ↦ z_Ψ` is linear.
* `zPsi_translate_nMat`: `z_{n(t)·Ψ} = z_Ψ` for `t ∈ R`.
* **`zPsi_restrict`**: `z_{Φρ_∞} = q/(q+1) · z_Φ` for every genuine section `Φ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA ArtinKP.N2

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Finite sums of twisted sections -/

section z

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma cell_of_pcell {Γ : Subgroup (SL(2, 𝓞 F))} {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : Cell Γ D n :=
  ⟨hD.meas, hD.isAddFundamentalDomain volume, hb⟩

include hG hz6 in
/-- A finite-index group fixing two sections, with a strict cell. -/
lemma exists_common (P : CubicPkg F) (Ψ Ψ' : TSection ι 𝔪) : ∃ (Γ : Subgroup (SL(2, 𝓞 F))) (_ : Γ.FiniteIndex)
    (D : Set (InfinitePlace F → ℂ)) (n : ℕ), Inv Γ Ψ ∧ Inv Γ Ψ' ∧ PCell (latN Γ) D ∧
      (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) ∧ 1 ≤ n := by
  have h1 := finiteIndex_stabGroup hG hz6 P Ψ
  have h2 := finiteIndex_stabGroup hG hz6 P Ψ'
  have h3 : (stabGroup Ψ ⊓ stabGroup Ψ').FiniteIndex := inferInstance
  obtain ⟨D, n, hD, hb⟩ := exists_pcell_latN (stabGroup Ψ ⊓ stabGroup Ψ')
  refine ⟨_, h3, D, max n 1, fun γ hγ => inv_stabGroup Ψ γ hγ.1,
    fun γ hγ => inv_stabGroup Ψ' γ hγ.2, hD, fun x hx w => (hb x hx w).trans ?_, le_max_right _ _⟩
  exact_mod_cast le_max_left n 1

include hG hz6 in
/-- The ray limit of `mext` is `z_Ψ`. -/
lemma tendsto_mext_zPsi {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}
    (hΓ : Inv Γ Ψ) {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n) (hn : 1 ≤ n) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * mext Γ Ψ D n (ray t)) (𝓝[>] 0)
      (𝓝 (zPsi P hG hz6 Ψ)) := by
  rw [← zRes_eq_zPsi P hG hz6 hΓ hD hn]
  exact tendsto_ray_mext hG hΓ (eisE hG Ψ) hD hn

/-- `mD` is homogeneous (`Re s > 2`). -/
lemma mD_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hD0 : (((volume D).toReal : ℝ) : ℂ) ≠ 0) :
    mD D (c • Ψ) s = c * mD D Ψ s := by
  rw [mD_eq_integral h𝔪 _ hs hDm hb hD0, mD_eq_integral h𝔪 _ hs hDm hb hD0]
  have e : ∀ Q : X F, eis (c • Ψ) s Q = c * eis Ψ s Q := fun Q =>
    T.eis_smulFun h𝔪 (fun _ => c) (differentiable_const c) Ψ hs Q
  simp only [e]
  rw [integral_const_mul, TSection.smul_apply]
  ring

include hG hz6 in
/-- **`z` is homogeneous.** -/
theorem zPsi_smul_oai (c : ℂ) (Ψ : TSection ι 𝔪) :
    zPsi P hG hz6 (c • Ψ) = c * zPsi P hG hz6 Ψ := by
  have h𝔪 := hG.ne_bot
  obtain ⟨Γ, hfi, D, n, hΓ, -, hD, hb, hn⟩ := exists_common hG hz6 P Ψ Ψ
  have hc := cell_of_pcell hD hb
  have := (adm_latN Γ).countable
  have hD0 : (((volume D).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (volume_toReal_pos hD hb).ne'
  refine zPsi_eq_of_continuation P hG hz6 (hΓ.smul c) hc
    (m' := fun s => c * mext Γ Ψ D n s)
    ((differentiableOn_mext hG hΓ (eisE hG Ψ) hc hn).const_mul c) (fun s hs => ?_) ?_
  · rw [mext_eq_mD hG hΓ hc hn hs (eisE hG Ψ s hs), mD_smul h𝔪 c Ψ hs hD.meas hb hD0]
  · have := (tendsto_mext_zPsi (P := P) hG hz6 hΓ hc hn).const_mul c
    refine this.congr fun t => ?_
    ring

/-! ### Translations -/

/-! ### `ρ_∞` -/

end z

end

end ArtinKP.F
end

theorem solution.{u_1} : type_of% @ArtinKP.F.zPsi_smul_oai.{u_1} := @ArtinKP.F.zPsi_smul_oai.{u_1}
