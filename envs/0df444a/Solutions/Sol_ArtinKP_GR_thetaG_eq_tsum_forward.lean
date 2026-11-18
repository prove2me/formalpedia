-- Prove2me | solution 1 for ArtinKP.GR.thetaG_eq_tsum_forward
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:44.306808+00:00
-- url     : https://prove2.me/submissions/9ddaffc9-99e6-4786-9ae6-06b2c6bc1e7e

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
import Theorems.Thm_ArtinKP_G2a_ThetaM_nT

section
-- module Solutions.Artin.KP.A_Interface
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A interface (symbols on global elements, Kubota symbol on `SL₂(R)`)

Later packages should import this file only.  Everything is in namespace `ArtinKP.A`, for
`F : Type*` a number field, `𝔪 : Ideal (𝓞 F)`, `R = SInt 𝔪`.

## Standing data (obtained once from `exists_cutoff_setup`)
* `P : CubicPkg F` — cubic Hilbert symbols `P.hv v : Fˣ →* Fˣ →* rootsOfUnity 3 F` on global
  elements; orientation pinned by `CubicPkg.tame`.
* `hG : Good 𝔪` — `𝔪 ≠ ⊥`, primes over `6` divide `𝔪`, extended ideals of `R` are principal.
* `hz6 : IsPrimitiveRoot z6 6`, `z6 : 𝓞 F`.

## Exported statements
* local: `IsTameSymbol`, `kubota_local`, `CubicPkg.isTame`;
* (A1) `CubicPkg.tame`, `CubicPkg.tame_zpow`, `CubicPkg.tame_formula`, `iota3_hv_eq`;
* (A2) `CubicPkg.HS`, `CubicPkg.HS_apply`, `CubicPkg.HS_mul_prod`, `CubicPkg.HS_mul_prod'`,
  `CubicPkg.HS_mul_finprod`;
* (A3) `cubicExt`, `cubicExt_eq_residueSymbol`, `cubicExt_eq_prod`, `cubicExt_reciprocity`,
  `cubicExt_unit_left`, `cubicExt_of_unit_right`, `cubicExt_mul_left`, `cubicExt_mul_right`,
  `cubicExt_pow_three`, `cubicExt_congr`;
* (A4) `CubicPkg.HS_self`, `CubicPkg.HS_skew`, `CubicPkg.HS_skew'`, `CubicPkg.HS_neg_left/right`,
  `CubicPkg.HS_pow_three_left/right`, `CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`,
  `CubicPkg.HS_add_eq`, `CubicPkg.IsDeepLevel`, `CubicPkg.exists_isDeepLevel`,
  `CubicPkg.HS_deep_left/right`, `HS_of_mem_SLevel_right/left`;
* (A5) `toF`, `kappa`, `sigmaS`, `kappa_mul`, `kappa_eq_prod`, `IsRad`, `sigmaS_eq_one`;
* (A6) `Gamma`, `mem_Gamma_iff`, `kappa_mul_of_mem_Gamma`, `exists_level_kappa_mul`, `kappaHom`;
* existence: `exists_cutoff_good`, `nonempty_cubicPkg_cyclotomic`, `exists_cutoff_setup`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- Membership in the goal's level group `SLevel 𝔪 k` in terms of valuations:
`v(b - 1) ≤ exp (-(k+1))` at every `v ∣ 𝔪`. -/
theorem val_le_of_mem_SLevel {𝔪 : Ideal (𝓞 F)} {k : ℕ} {b : Fˣ} (hb : b ∈ SLevel 𝔪 k)
    (v : HeightOneSpectrum (𝓞 F)) (hv : 𝔪 ≤ v.asIdeal) :
    v.valuation F ((b : F) - 1) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
  have h := hb v hv
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [NumberField.HeightOneSpectrum.adicAbv_def] at h
  have e : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1))
      = ((WithZeroMulInt.toNNReal hq.ne_zero (WithZero.exp (-((k + 1 : ℕ) : ℤ)) :
          WithZero (Multiplicative ℤ)) : NNReal) : ℝ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    push_cast
    rfl
  rw [e, NNReal.coe_le_coe] at h
  exact (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le.mp h

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma isFund : IsAddFundamentalDomain (latSub F) (fundD F) volume :=
  ZSpan.isAddFundamentalDomain' (latE (F := F)) volume

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.S_Ops
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 5: operations on genuine sections

* `GSection.nT t`: `(n(t)Φ)_s(c, d) = Φ_s(c, d + ct)`, `t ∈ F` (no symbol).
* `wFun`: `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)`; `twist_wFun`: its twist is the `w`-translate of the
  twist of `Φ` (MATH §5.2; the symbol is `σ_S((c,d), w)⁻¹·κ(w) = ⟨c, d⟩`).
* `GSection.torus β`: `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` for `c ≠ 0`, and
  `⟨d, β⟩ Φ_s(0, βd)` on the cell `c = 0` (MATH2 §6.1, with the `c = 0` factor decided by proof);
  `GSection.torusT β = |β|^{2s-1} A(β)` is `Ã(β)`.
  `torus_torus`: `A(β) A(β') = ⟨β, β'⟩ A(β β')`.
* `GSection.sharp π`: `Φ♯_s(c, d) = Φ_s(c, d/π³)`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem torus_apply (hG : Good 𝔪) (β : F) (hβ : β ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.torus hG β hβ s c d = tf ι P 𝔪 β c d * Φ s (β ^ 2 * c) (β * d) := rfl

/-- `A(β) A(β') = ⟨β, β'⟩ A(β β')` (MATH2 Lemma 6.1 (ii)); in particular the `Ã(β)` commute up to
`⟨β, β'⟩²`. -/
theorem torus_torus (hG : Good 𝔪) (β β' : F) (hβ : β ≠ 0) (hβ' : β' ≠ 0) (Φ : GSection ι P 𝔪) :
    (Φ.torus hG β' hβ').torus hG β hβ
      = brk ι P 𝔪 β β' • Φ.torus hG (β * β') (mul_ne_zero hβ hβ') := by
  ext s c d
  rw [smul_apply, torus_apply, torus_apply, torus_apply]
  have e1 : β' ^ 2 * (β ^ 2 * c) = (β * β') ^ 2 * c := by ring
  have e2 : β' * (β * d) = β * β' * d := by ring
  rw [e1, e2]
  by_cases h0 : c = 0 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [Φ.zero]
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
  have key : tf ι P 𝔪 β c d * tf ι P 𝔪 β' (β ^ 2 * c) (β * d)
      = brk ι P 𝔪 β β' * tf ι P 𝔪 (β * β') c d := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
      rw [hc, mul_zero, tf, if_pos rfl, tf, if_pos rfl, tf, if_pos rfl, brk_mul_left _ hβ hd,
        brk_mul_right _ hβ hβ']
      ring
    · have hW := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) β β'
      rw [tf, if_neg hc, tf, if_neg (mul_ne_zero (pow_ne_zero 2 hβ) hc), tf, if_neg hc,
        brk_mul_left _ (pow_ne_zero 2 hβ) hc, pow_two β, brk_mul_left _ hβ hβ,
        brk_mul_right _ hβ hβ']
      linear_combination (brk ι P 𝔪 β β' * brk ι P 𝔪 c β ^ 2 * brk ι P 𝔪 c β' ^ 2) * hW
  linear_combination (Φ s ((β * β') ^ 2 * c) (β * β' * d)) * key

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourIndex
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.BZ_Vol
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 4: stub B-2 — the covolume of the translation lattice `Λ_M`

* `exists_fund_sublattice`, `measure_fund_sublattice` (Mathlib only): for countable subgroups
  `L' ≤ L` of finite index of a measurable additive group with an invariant measure, a
  fundamental domain of `L'` has measure `[L : L'] ·` that of a fundamental domain of `L`.
* `card_transLat_quot`: `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`
  (`S2.card_latD_quot` transported by strong approximation `F = R + 𝔩_{M'}`).
* `transLat_zero`: `Λ_0 = emb(𝓞_F)`.
* **`volume_cell`** (B-2): `vol(D) · vol(𝔩_M) = vol(B1.fundD F)` for every fundamental cell `D`
  of `Λ_M`, every `M : ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

/-! ### Fundamental domains of a sublattice -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  (μ : Measure E) [μ.IsAddLeftInvariant]

/-- From a fundamental domain of `L` to one of a subgroup `L' ≤ L` of finite index. -/
theorem exists_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D : Set E} (hD : IsAddFundamentalDomain L D μ) :
    ∃ D' : Set E, IsAddFundamentalDomain L' D' μ ∧
      μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  classical
  set K := L'.addSubgroupOf L with hK
  let σ : L ⧸ K → L := fun q => Quotient.out q
  have hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ K) = q := fun q => Quotient.out_eq q
  have hσinj : ∀ q₁ q₂ : L ⧸ K, ((σ q₁ : L) : E) - ((σ q₂ : L) : E) ∈ L' → q₁ = q₂ := by
    intro q₁ q₂ h
    rw [← hσ q₁, ← hσ q₂, QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf]
    have : ((-(σ q₁) + σ q₂ : L) : E) = -(((σ q₁ : L) : E) - ((σ q₂ : L) : E)) := by
      push_cast
      abel
    rw [this]
    exact L'.neg_mem h
  let f : L ⧸ K → Set E := fun q => (σ q : L) +ᵥ D
  have hfm : ∀ q, NullMeasurableSet (f q) μ := fun q => hD.nullMeasurableSet_vadd (σ q)
  have hfd : Pairwise (Function.onFun (AEDisjoint μ) f) := by
    intro q₁ q₂ hq
    refine hD.aedisjoint fun h => hq (hσinj q₁ q₂ ?_)
    rw [h, sub_self]
    exact L'.zero_mem
  refine ⟨⋃ q, f q, ⟨NullMeasurableSet.iUnion hfm, ?_, ?_⟩, ?_⟩
  · -- covering
    filter_upwards [hD.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    set q : L ⧸ K := QuotientAddGroup.mk (-g) with hq
    have hmem : ((σ q : L) : E) + (g : E) ∈ L' := by
      have h1 : (QuotientAddGroup.mk (σ q) : L ⧸ K) = QuotientAddGroup.mk (-g) := hσ q
      rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : ((σ q : L) : E) + (g : E) = -((-(σ q) + -g : L) : E) := by
        push_cast
        abel
      rw [h2]
      exact L'.neg_mem h1
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    refine ⟨g +ᵥ x, hg, ?_⟩
    change ((σ q : L) : E) + ((g : E) + x) = (((σ q : L) : E) + (g : E)) + x
    rw [add_assoc]
  · -- disjointness
    intro g₁ g₂ hg
    change AEDisjoint μ (g₁ +ᵥ ⋃ q, f q) (g₂ +ᵥ ⋃ q, f q)
    rw [Set.vadd_set_iUnion, Set.vadd_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro q₁
    rw [AEDisjoint.iUnion_right_iff]
    intro q₂
    have e : ∀ (g : L') (q : L ⧸ K),
        g +ᵥ f q = ((⟨(g : E), hle g.2⟩ + σ q : L)) +ᵥ D := by
      intro g q
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, by
          change ((g : E) + ((σ q : L) : E)) + w = (g : E) + (((σ q : L) : E) + w)
          rw [add_assoc]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(σ q : L) +ᵥ w, ⟨w, hw, rfl⟩, by
          change (g : E) + (((σ q : L) : E) + w) = ((g : E) + ((σ q : L) : E)) + w
          rw [add_assoc]⟩
    rw [e, e]
    refine hD.aedisjoint fun h => hg ?_
    have h' : (g₁ : E) + ((σ q₁ : L) : E) = (g₂ : E) + ((σ q₂ : L) : E) :=
      congrArg (fun z : L => (z : E)) h
    have hq : q₁ = q₂ := by
      refine hσinj q₁ q₂ ?_
      have : ((σ q₁ : L) : E) - ((σ q₂ : L) : E) = (g₂ : E) - (g₁ : E) := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, h', add_comm]
      rw [this]
      exact L'.sub_mem g₂.2 g₁.2
    rw [hq] at h'
    exact Subtype.ext (add_right_cancel h')
  · -- measure
    let _ := Fintype.ofFinite (L ⧸ K)
    rw [measure_iUnion₀ hfd hfm, tsum_fintype]
    have : ∀ q, μ (f q) = μ D := fun q => by
      change μ (((σ q : L) : E) +ᵥ D) = μ D
      exact measure_vadd μ _ D
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- A fundamental domain of a sublattice `L' ≤ L` of finite index has measure
`[L : L'] · μ(D)`. -/
theorem measure_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D D' : Set E} (hD : IsAddFundamentalDomain L D μ)
    (hD' : IsAddFundamentalDomain L' D' μ) :
    μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  have : Countable L' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨D'', h1, h2⟩ := exists_fund_sublattice μ hle hD
  rw [← h2]
  exact hD'.measure_eq h1

end abstract

/-- Two surjective homomorphisms with the same kernel have equinumerous targets. -/
theorem card_eq_of_ker_eq {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nat.card B = Nat.card C := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, h]

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem transLat_mono {M M' : ℤ} (h : M ≤ M') : transLat 𝔪 M' ≤ transLat 𝔪 M := by
  rintro x ⟨b, hb, rfl⟩
  exact ⟨b, Small.mono (𝔪 := 𝔪) h hb, rfl⟩

theorem embR_mem_transLat {M : ℤ} {b : SInt 𝔪} :
    (embR b : InfinitePlace F → ℂ) ∈ transLat 𝔪 M ↔ b ∈ latR 𝔪 M := by
  constructor
  · rintro ⟨b', hb', h⟩
    rwa [← embR_injective h]
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`. -/
theorem card_transLat_quot (h𝔪 : 𝔪 ≠ ⊥) {M M' : ℤ} (h : M ≤ M') :
    Nat.card (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M))
      = ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat := by
  rw [← S2.card_latD_quot h𝔪 (k := fun _ => M) (k' := fun _ => M') fun _ _ => h]
  -- the two maps out of `R ∩ 𝔩_M`
  let f₀ : latR 𝔪 M →+ transLat 𝔪 M := (embR (𝔪 := 𝔪)).addSubgroupMap (latR 𝔪 M)
  have hf₀ : Function.Surjective f₀ := (embR (𝔪 := 𝔪)).addSubgroupMap_surjective (latR 𝔪 M)
  let g₀ : latR 𝔪 M →+ S2.latD 𝔪 (fun _ => M) :=
    { toFun := fun b => ⟨((b : SInt 𝔪) : F), b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : latR 𝔪 M →+ transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M) :=
    (QuotientAddGroup.mk' _).comp f₀
  let g : latR 𝔪 M →+
      S2.latD 𝔪 (fun _ => M) ⧸ (S2.latD 𝔪 (fun _ => M')).addSubgroupOf (S2.latD 𝔪 (fun _ => M)) :=
    (QuotientAddGroup.mk' _).comp g₀
  have hf : Function.Surjective f := (QuotientAddGroup.mk'_surjective _).comp hf₀
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sInt_sub_small h𝔪 M' (x : F)
    have hrM : Small 𝔪 M ((r : SInt 𝔪) : F) := by
      have h1 : Small 𝔪 M ((x : F) - (r : F)) := Small.mono (𝔪 := 𝔪) h hr
      have h2 : Small 𝔪 M (x : F) := x.2
      have := h2.sub h1
      rwa [sub_sub_cancel] at this
    refine ⟨⟨r, hrM⟩, ?_⟩
    change (QuotientAddGroup.mk (g₀ ⟨r, hrM⟩) : S2.latD 𝔪 (fun _ => M) ⧸ _) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    change Small 𝔪 M' (-((r : SInt 𝔪) : F) + (x : F))
    rwa [neg_add_eq_sub]
  refine card_eq_of_ker_eq f g hf hg ?_
  ext b
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  change (QuotientAddGroup.mk (f₀ b) : transLat 𝔪 M ⧸ _) = 0 ↔
    (QuotientAddGroup.mk (g₀ b) : S2.latD 𝔪 (fun _ => M) ⧸ _) = 0
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_addSubgroupOf]
  change (embR (b : SInt 𝔪) : InfinitePlace F → ℂ) ∈ transLat 𝔪 M' ↔ _
  rw [embR_mem_transLat]
  rfl

variable [IsTotallyComplex F]

/-- `Λ_0 = emb(𝓞_F)`. -/
theorem transLat_zero (𝔪 : Ideal (𝓞 F)) : transLat 𝔪 0 = latSub F := by
  ext x
  rw [mem_latSub]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((b : SInt 𝔪) : F) ≤ 1 := by
      intro v
      by_cases hv : 𝔪 ≤ v.asIdeal
      · have := hb v hv
        rwa [neg_zero, WithZero.exp_zero] at this
      · exact sInt_val_le_one b v hv
    obtain ⟨β, hβ⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hall
    exact ⟨β, by rw [embR_apply, ← hβ]⟩
  · rintro ⟨β, rfl⟩
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) β, fun v _ => ?_, rfl⟩
    rw [neg_zero, WithZero.exp_zero]
    exact v.valuation_le_one β

/-- **Stub B-2, proved** (only `𝔪 ≠ ⊥` is used): `vol(D) · vol(𝔩_M) = covol(𝓞_F)`. -/
theorem volume_cell' (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    volume D * ENNReal.ofReal (vol 𝔪 M) = volume (B1.fundD F) := by
  classical
  set M' : ℤ := max M 0 with hM'
  have h1 : M ≤ M' := le_max_left _ _
  have h0 : (0 : ℤ) ≤ M' := le_max_right _ _
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Ideal.absNorm v.asIdeal := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  set n₁ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat with hn₁
  set n₀ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - 0).toNat with hn₀
  have hn₁0 : n₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hn₀0 : n₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hc₁ := card_transLat_quot h𝔪 h1
  have hc₀ := card_transLat_quot h𝔪 h0
  have hfin₁ : Finite (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₁]; exact hn₁0)
  have hfin₀ : Finite (transLat 𝔪 0 ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 0)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₀]; exact hn₀0)
  have hF : IsAddFundamentalDomain (transLat 𝔪 0) (B1.fundD F) volume := by
    rw [transLat_zero]
    exact B1.isFund
  obtain ⟨D', hD', hvol₀⟩ := exists_fund_sublattice volume (transLat_mono h0) hF
  have hvol₁ := measure_fund_sublattice volume (transLat_mono h1) hD hD'
  rw [hc₀] at hvol₀
  rw [hc₁] at hvol₁
  -- `vol 𝔪 M = n₁ / n₀`
  have hvolM : vol 𝔪 M = (n₁ : ℝ) / (n₀ : ℝ) := by
    rw [vol, hn₁, hn₀, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hqv : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by exact_mod_cast (hq v).ne'
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), ← zpow_sub₀ hqv]
    congr 1
    ring
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀0
  rw [hvolM, ENNReal.ofReal_div_of_pos hn₀pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ← mul_div_assoc, mul_comm (volume D), ← hvol₁, hvol₀, mul_comm,
    ENNReal.mul_div_cancel_right (by exact_mod_cast hn₀0) (ENNReal.natCast_ne_top n₀)]

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 2: linearity of `Lam`, and the cusp change for `Lam` and for the Kirillov term

* `Lam_smulFun`, `Lam_smul`, `Lam_scal`, `Lam_nT` (all `s`); `Lam_add`, `Lam_sum`, `Lam_addProj`
  (`Re s > 1`, where the defining series converges: `summable_jacTerm`).
* `torusT_torusT`, `torusT_smulFun`, `torusT_smul`.
* `Kt ψ hG Φ β η s := Lam (Ã(β)Φ) η 1 s`, the `η`-term of the Kirillov function (`= S.kir` at a
  valid depth, `Kt_eq_kir`), with the rules (K4):
  `Kt_torusT`, `Kt_nT`, `Kt_smulFun`, `Kt_add`, `Kt_addProj`.
* `Lam_cusp`: `Lam Ψ c' μ s = κ(γ)|c|^{s-2} ψ(μa/c) ⟨c',c⟩⁻¹ Lam (wΦ) (c'/c) (μ/c²) s`,
  `Ψ = translate γ (n(-d/c)Φ)`;
  `cusp_torusT`: `Ã(μ)Ψ = κ(γ)⟨μ,c⟩ |c|^{s-2} n(μa/c) Ã(μ/c²)(wΦ)`;
  `Kt_cusp`, and `xiT_cusp` (MATH3 (2.2)): with `ξ^η_Φ(β) := |β|^{1/3} Kt Φ β η (4/3)`,
  `ξ^η_Ψ(μ) = κ(γ) ψ(μa/c) ⟨μ,c⟩ ξ^η_{wΦ}(μ/c²)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Convergence of the defining series, linearity -/

theorem valid_smulFun {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Valid ψ (GSection.smulFun f hf Φ) ν k :=
  ⟨fun b hb s c d => by rw [GSection.smulFun_apply, GSection.smulFun_apply, h.1 b hb], h.2⟩

/-- `Lam` commutes with multiplication by a function of `s` (all `s`). -/
theorem Lam_smulFun (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (c ν : F) (s : ℂ) :
    Lam ψ hG (GSection.smulFun f hf Φ) c ν s = f s * Lam ψ hG Φ c ν s := by
  have h := valid_depth ψ hG Φ ν
  rw [Lam_eq_lam ψ hG _ (valid_smulFun h f hf), Lam_eq_lam ψ hG _ h, lam, lam]
  simp only [GSection.smulFun_apply]
  rw [jac_const_mul]
  ring

theorem Lam_smul (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (a : ℂ) (c ν : F) (s : ℂ) :
    Lam ψ hG (a • Φ) c ν s = a * Lam ψ hG Φ c ν s :=
  Lam_smulFun ψ hG Φ (fun _ => a) (differentiable_const a) c ν s

/-! ### `Ã(β)` against the other operations -/

/-- `Ã(β) Ã(β') = ⟨β, β'⟩ Ã(β β')` on genuine sections. -/
theorem torusT_torusT (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β β' : F} (hβ : β ≠ 0)
    (hβ' : β' ≠ 0) :
    (Φ.torusT hG β' hβ').torusT hG β hβ
      = brk ι P 𝔪 β β' • Φ.torusT hG (β * β') (mul_ne_zero hβ hβ') := by
  ext s c d
  have h := congrArg (fun Ψ : GSection ι P 𝔪 => Ψ s c d) (GSection.torus_torus hG β β' hβ hβ' Φ)
  simp only [GSection.torus_apply, GSection.smul_apply] at h
  rw [GSection.torusT_apply, GSection.torusT_apply, GSection.smul_apply, GSection.torusT_apply,
    absS_mul, ofReal_mul_cpow (absS_nonneg _) (absS_nonneg _)]
  linear_combination (((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1) * ((absS 𝔪 β' : ℝ) : ℂ) ^ (2 * s - 1)) * h

theorem torusT_smulFun (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (GSection.smulFun f hf Φ).torusT hG β hβ = GSection.smulFun f hf (Φ.torusT hG β hβ) := by
  ext s c d
  simp only [GSection.torusT_apply, GSection.smulFun_apply]
  ring

/-! ### The Kirillov term -/

theorem Kt_of_ne (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    (η : F) (s : ℂ) : Kt ψ hG Φ β η s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Kt, dif_neg hβ]

/-- (K4) `𝒦_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ 𝒦_Φ(β β₀)`. -/
theorem Kt_torusT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0)
    (hβ₀ : β₀ ≠ 0) (η : F) (s : ℂ) :
    Kt ψ hG (Φ.torusT hG β₀ hβ₀) β η s = brk ι P 𝔪 β β₀ * Kt ψ hG Φ (β * β₀) η s := by
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ (mul_ne_zero hβ hβ₀), torusT_torusT hG Φ hβ hβ₀,
    Lam_smul]

/-- (K4) `𝒦_{h•Φ} = h(s) 𝒦_Φ`. -/
theorem Kt_smulFun (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (β η : F) (s : ℂ) :
    Kt ψ hG (GSection.smulFun f hf Φ) β η s = f s * Kt ψ hG Φ β η s := by
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ hβ, torusT_smulFun hG Φ hβ, Lam_smulFun]

theorem Kt_smul (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (a : ℂ) (β η : F) (s : ℂ) :
    Kt ψ hG (a • Φ) β η s = a * Kt ψ hG Φ β η s :=
  Kt_smulFun ψ hG Φ _ _ β η s

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Meas
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_one : SFin.mk 𝔪 k 1 = 0 := rfl

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Emb
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_fin {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).2.2 = SFin.mk 𝔪 k (Units.mk0 x hx) := by
  rw [sEmb_of_ne hx]

theorem sEmb_fst {x : F} (hx : x ≠ 0) (w : InfinitePlace F) :
    (sEmb 𝔪 k x).1 w = (w.mult : ℝ) * Real.log (w x) := by
  rw [sEmb_of_ne hx]

/-! ### Absolute values and valuations -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Phi
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Phi: the weight `Φ = ρ · 1_B([y]) · L(y)⁻¹` and the `S`-functions

* `Lmod` is a unitary character of `SModel`, radially trivial, rotating by `ω_{m_w}`.
* `psi y = 1_B([y]) L(y)⁻¹` is `Γ`-invariant; `Phi = ρ · psi`.
* `fpF` facts: its norm, and `L(y)⁻¹ fpF(y) = ∏_w κ(|y_w|)` on `y_f = 0`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Angular characters -/

theorem toCircle_zsmul_add (n : ℤ) (a b : AddCircle (2 * Real.pi)) :
    ((AddCircle.toCircle (n • (a + b)) : Circle) : ℂ) =
      ((AddCircle.toCircle (n • a) : Circle) : ℂ) * ((AddCircle.toCircle (n • b) : Circle) : ℂ) := by
  rw [smul_add, AddCircle.toCircle_add]; rfl

/-! ### The weight -/

/-! ### The forward `S`-function -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Coord
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # WP-H0, file 4: the coordinate dictionary, part 2 — `SFin`, `sEmb`, `fp`, `Fm`

* `SFin`: `SFin.mk x = 0 ↔ x ∈ SLevel` (`= F^× ∩ U_k`), equality of classes, and weak approximation
  in the form needed: every class of `SFin 𝔪 k` is the class of a nonzero `S`-integer
  (`exists_sInt_rep`); `mem_SLevel_of_sub_one_mem`: `d ≡ 1 mod 𝔪^{k+1}` lies in `SLevel 𝔪 k`.
* `fpF_sEmb_add`: `fp (sEmb ν + y)` is the indicator of `[ν] + y_f = 0` (i.e. `ν·y_f ∈ U_k`)
  times `∏_w ω_{m_w}(ν_w) ω_{m_w}(y_w) κ(|ν|_w · e^{x_w})`.
* `FmOf_sEmb_sub`: the product-form `Fm` at `sEmb ν − y`.
* rotation covariance: `fpF_add_rot`, `FmOf_sub_rot`. -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots FractionalIdeal

set_option linter.unusedSectionVars false

open scoped Classical nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### `SFin` -/

theorem SFin_mk_eq_mk_iff (x y : Fˣ) :
    SFin.mk 𝔪 k x = SFin.mk 𝔪 k y ↔ x⁻¹ * y ∈ SLevel 𝔪 k :=
  Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq

theorem SFin_mk_eq_zero_iff (x : Fˣ) : SFin.mk 𝔪 k x = 0 ↔ x ∈ SLevel 𝔪 k := by
  rw [← L3X.SFin.mk_one, eq_comm, SFin_mk_eq_mk_iff, inv_one, one_mul]

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-! ### The two functions at `sEmb ν ± y` -/

theorem exp_sEmb_fst_add {ν : F} (hν : ν ≠ 0) (w : InfinitePlace F) (t : ℝ) :
    Real.exp ((sEmb 𝔪 k ν).1 w + t) = w ν ^ w.mult * Real.exp t := by
  rw [L3X.sEmb_fst hν, Real.exp_add, Real.exp_nat_mul, Real.exp_log (w.pos_iff.2 hν)]

/-- **`fp (sEmb ν + y)`**: the indicator of `ν·y_f ∈ U_k` times the archimedean profile at
`ν·y_∞`. (`fp` of the frozen goal is `L3X.fpF κ m` by `rfl`; `w.mult = 2` for totally complex
`F`, so `w ν ^ w.mult` is the normalized absolute value.) -/
theorem fpF_sEmb_add {ν : F} (hν : ν ≠ 0) (y : SModel 𝔪 k) :
    L3X.fpF κ m (sEmb 𝔪 k ν + y) =
      if SFin.mk 𝔪 k (Units.mk0 ν hν) + y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • ((Complex.arg (w.embedding ν) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ) *
          ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) *
          (κ (w ν ^ w.mult * Real.exp (y.1 w)) : ℂ)
      else 0 := by
  unfold L3X.fpF
  have h2 : (sEmb 𝔪 k ν + y).2.2 = SFin.mk 𝔪 k (Units.mk0 ν hν) + y.2.2 := by
    rw [Prod.snd_add, Prod.snd_add, L3X.sEmb_fin hν]
  have h1 : ∀ w, Real.exp ((sEmb 𝔪 k ν + y).1 w) = w ν ^ w.mult * Real.exp (y.1 w) := fun w =>
    exp_sEmb_fst_add hν w _
  have h3 : ∀ w, (sEmb 𝔪 k ν + y).2.1 w =
      ((Complex.arg (w.embedding ν) : ℝ) : AddCircle (2 * Real.pi)) + y.2.1 w := fun w => by
    rw [L3X.sEmb_of_ne hν]; rfl
  simp only [h1, h2, h3, L3X.toCircle_zsmul_add]

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.G1_BfS
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-!
# WP-G1, part 10: the majorant `bf` on `SFin 𝔪 k` and its summability (MATH3 §4.5)

`bf([x]) = C · ∏_{v ∈ S_f} min(1, |x|_v^{1/3}) · 1[x ∈ 𝔩_D]` is well defined on
`SFin 𝔪 k = F^×/U_k`, and `Σ_{y ∈ SFin} bf(y) |y|^σ < ∞` for every `σ > -1/3`
(`exists_bf`; the cut `H0.KPCut` wants `σ ≥ -α`, any `α < 1/3`).

Proof: `[x] ↦ (ord_v x)_{v ∈ S_f}` has fibres that inject into the finite group `𝔩_0/𝔩_{k+1}`
(`x ↦ x / t_{ord x}`, `t_n` an element with valuations `n`), and the sum over valuation vectors is a
finite product of geometric series (`summable_pi_prod`, `summable_local_weight`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2
open NumberField.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `U_k = SLevel 𝔪 k` in the vocabulary of WP-S: `x ∈ U_k ↔ x - 1 ∈ 𝔩_{k+1}`. -/
theorem mem_SLevel_iff_small (x : Fˣ) :
    x ∈ SLevel 𝔪 k ↔ Small 𝔪 ((k : ℤ) + 1) ((x : F) - 1) := by
  constructor
  · intro h v hv
    have := val_le_of_mem_SLevel h v hv
    push_cast at this
    exact this
  · intro h v hv
    exact abv_le_of_val_le v (h v hv)

theorem mk_repS (y : SFin 𝔪 k) : SFin.mk 𝔪 k (repS y) = y := by
  show Additive.ofMul (QuotientGroup.mk (Quotient.out (Additive.toMul y))) = y
  rw [QuotientGroup.out_eq']
  rfl

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 6: interface repairs for WP-E's abstract residue layer (MATH3 findings 6, 7)

New lemmas beside `E.ResFun`, `E.HasResOn`, `E.Theta` (no file of WP-E is edited).

* `ResFun.SmulOn T U`: the scalar law of a residue functional for multipliers that are holomorphic
  on the open set `U` only (`E.ResFun.smul` asks for an entire multiplier).
* `hasResOn_smul`: for the model `HasResOn Ω s₀ γ`, a multiplier analytic on `Ω` with a limit `L`
  along the path `γ` multiplies the residue by `L`.
* `ofContinuation_smulOn`: `ResFun.ofContinuation Ω s₀ γ …` has `SmulOn U` for every open
  `U ⊇ Ω ∪ {s₀}`; `resFunSlit_smulOn`: the slit model has `SmulOn {Re s > 1}`.
  (What is true and sufficient: the multiplier must be analytic on the region `Ω` and continuous at
  `s₀` along the ray; holomorphy on a neighbourhood of `Ω ∪ {s₀}` gives both.)
* `Theta.tau_congr_at`: `τ` sees a section through `Lam` at the one frequency `ν` only, with a
  scalar that may depend on `ν` (`E.Theta.tau_congr` has one scalar for all `ν`).
* `Theta.tau_smul_at`: the same with an entire multiplier `h(s)`.
* `Theta.tau_sum_at`: `Lam Φ c ν s = Σ_i h_i(s) Lam Ψ_i c ν s` on `Re s > 2` gives
  `τ_Φ(ν) = Σ_i h_i(s₀) τ_{Ψ_i}(ν)`, for multipliers holomorphic on `U` (given `SmulOn U`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter Topology

namespace ArtinKP.G1

open ArtinKP.B7 ArtinKP.E

section theta

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} {D : Kubota S A Sec} {s₀ : ℂ}
  (T : Theta D s₀)

/-- **`tau_congr` per frequency**: if `Lam Φ c ν s = z · Lam Ψ c ν s` at the one frequency `ν`
(`c ≠ 0`, `Re s > 2`), then `τ_Φ(ν) = z τ_Ψ(ν)`. -/
theorem _root_.ArtinKP.E.Theta.tau_congr_at {Φ Ψ : Sec} {z : ℂ} {ν : R} (hν : ν ≠ 0)
    (h : ∀ (c : R) (s : ℂ), c ≠ 0 → 2 < s.re → D.Lam Φ c ν s = z * D.Lam Ψ c ν s) :
    T.tau Φ ν = z * T.tau Ψ ν := by
  have h1 := T.smul (fun _ => z) (differentiable_const z) (T.tau_spec Ψ ν hν)
  have h2 := T.congr h1 (fun s hs => by
    show z * D.aSer Ψ ν s = D.aSer Φ ν s
    unfold Kubota.aSer
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    unfold Kubota.term
    rw [h _ s (rp_ne_zero a.2) hs]
    ring)
  exact T.unique (T.tau_spec Φ ν hν) h2

end theta

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.G1_Kir
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 7: the Kirillov function — (K1)–(K4), the class decomposition, the bound

Section level (any `S_f`-character `ψ` with bounded dual lattices, `HasDual ψ d₀`):

* `exists_Kt_support` (K3): `Kt Φ β η s = 0` unless `β ∈ 𝔩_D` (support in a fractional ideal,
  i.e. `|β|_v ≤ q_v^{-D}` at every `v ∈ S_f` separately); from `S.kir_eq_zero` and DUAL.
* `exists_Kt_bound` (K2): `|β|^{1/3} |Kt Φ β η (4/3)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})` for all
  `β ∈ F^×`, all classes `η`; from `GL.xi_bound`, the support, and `S2.K_eq`.
* `exists_Kt_deep` (K1): `Kt Φ (βu) η s = Kt Φ β η s` for `u` deep.

`τ` level, for `D = B.kubota hG hz6` (`ψ = B.psiS`), any `T : E.Theta D (4/3)`:

* `tau_smul`, `tau_nT`, `tau_addProj`, `tau_sum`, `tau_smulFun`.
* `Kir T Φ β := τ_{Ã(β)Φ}(1)` (MATH3 §0), `xi T Φ β := |β|^{1/3} Kir T Φ β`; **(K4)**:
  `Kir_torusT` (`𝒦_{Ã(β₀)Φ}(β) = ⟨β,β₀⟩𝒦_Φ(ββ₀)`), `Kir_nT` (`𝒦_{n(t)Φ}(β) = ψ(βt)𝒦_Φ(β)`),
  `Kir_smulFun`, `Kir_addProj` (G2), `Kir_sum`, `xi_torusT`, `xi_nT`; `exists_Kir_deep` (K1);
  `Kir_cusp`/`xi_cusp` (MATH3 (2.2)).
* `tau_classDecomp` — **(CD)**: `τ_Ψ(ν) = Σ_η Lam Ψ η ν (4/3) · vol(𝔩_M)⁻¹ τ_{bigCell_η}(ν)`,
  given the scalar law `T.SmulOn {Re s > 1}` (true for `resFunSlit`: `resFunSlit_smulOn`).
* `exists_Kir_classDecomp`: one finite set of classes and weights `w_η` with
  `𝒦_Φ(β) = Σ_η Kt Φ β η (4/3) · w_η` for all `β ∈ F^×`.
* `exists_xi_le` — **the majorant for `ξ`** (MATH3 §4.3):
  `|ξ_Φ(β)| ≤ C ∏_v min(1, |β|_v^{1/3})` and `ξ_Φ(β) = 0` unless `β ∈ 𝔩_D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Section level: support, bound, deep invariance -/

/-! ### `τ` level -/

section tau

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

theorem coe_ne_zero' {c : SInt 𝔪} (hc : c ≠ 0) : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)

/-- Transfer of a `Lam`-identity at one frequency (stated on `F`, `Re s > 1`) to `τ`. -/
theorem tau_congr_F {Φ Ψ : GSection ι P 𝔪} {z : ℂ} {ν : SInt 𝔪} (hν : ν ≠ 0)
    (h : ∀ (c : F) (s : ℂ), c ≠ 0 → 1 < s.re →
      Lam (B.psiS hG.ne_bot) hG Φ c (ν : F) s = z * Lam (B.psiS hG.ne_bot) hG Ψ c (ν : F) s) :
    T.tau Φ ν = z * T.tau Ψ ν :=
  T.tau_congr_at hν fun c s hc hs => h (c : F) s (coe_ne_zero' hc) (by linarith)

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-- Transfer of an identity of Kirillov terms (all classes, `Re s > 1`) to `𝒦`. -/
theorem Kir_congr {Φ Ψ : GSection ι P 𝔪} {β β' : F} (hβ : β ≠ 0) (hβ' : β' ≠ 0) {z : ℂ}
    (h : ∀ (η : F) (s : ℂ), η ≠ 0 → 1 < s.re →
      Kt (B.psiS hG.ne_bot) hG Φ β η s = z * Kt (B.psiS hG.ne_bot) hG Ψ β' η s) :
    Kir hG hz6 T Φ β = z * Kir hG hz6 T Ψ β' := by
  rw [Kir_of_ne hG hz6 T Φ hβ, Kir_of_ne hG hz6 T Ψ hβ']
  refine tau_congr_F hG hz6 T one_ne_zero fun c s hc hs => ?_
  have h1 : ((1 : SInt 𝔪) : F) = 1 := rfl
  rw [h1, ← Kt_of_ne _ hG Φ hβ, ← Kt_of_ne _ hG Ψ hβ']
  exact h c s hc hs

/-- **(K4)** `𝒦_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ 𝒦_Φ(β β₀)`. -/
theorem Kir_torusT (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0) :
    Kir hG hz6 T (Φ.torusT hG β₀ hβ₀) β = brk ι P 𝔪 β β₀ * Kir hG hz6 T Φ (β * β₀) :=
  Kir_congr hG hz6 T hβ (mul_ne_zero hβ hβ₀) fun η s _ _ => Kt_torusT _ hG Φ hβ hβ₀ η s

theorem Kir_smul (Φ : GSection ι P 𝔪) (a : ℂ) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (a • Φ) β = a * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun η s _ _ => Kt_smul _ hG Φ a β η s

/-- `|β₀|^{1/3} ξ_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ ξ_Φ(β β₀)`. -/
theorem xi_torusT (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0) :
    ((absS 𝔪 β₀ ^ (1 / 3 : ℝ) : ℝ) : ℂ) * xi hG hz6 T (Φ.torusT hG β₀ hβ₀) β
      = brk ι P 𝔪 β β₀ * xi hG hz6 T Φ (β * β₀) := by
  rw [xi, xi, Kir_torusT hG hz6 T Φ hβ hβ₀, absS_mul,
    Real.mul_rpow (absS_nonneg _) (absS_nonneg _)]
  push_cast
  ring

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Delta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 8: the delta section (MATH3 §1.2 (G1)–(G3), §5 (C10)), as far as it is algebra

For `D = B.kubota hG hz6`, `T : E.Theta D (4/3)`:

* `exists_Kir_adual`: `𝒦_Φ(β) ≠ 0 → β ∈ A_N` (support in a dual lattice; no class decomposition
  and no scalar law needed).
* `exists_delta` — **the delta section**: if the Kirillov function of *some* section is not
  identically zero (hypothesis `hne`, the analytic input (C9)+(C10′)+Theorem E of MATH3 (G1)),
  then for every `k` with `k + 1` deep there is `Φ₀` with
  `𝒦_{Φ₀}(β) = 1[β ∈ 1 + 𝔩_{k+1}]` for all `β ∈ F^×` (`= 1_{U_k}`, `U_k = SLevel 𝔪 k`), and
  `ξ_{Φ₀}` is the same function (`xi_delta`).
  Construction: additive projection `Φ₂ = Σ_t ϕ(t) n(t) Φ₁` by Lemma FI, then
  `Φ₀ = 𝒦_{Φ₁}(β₁)⁻¹ Σ_j Ã(β₁/u_j) Φ₂`, `u_j = 1 + a_j`, `a_j` running over `𝔩_{k+1}/𝔩_{K'}`.
* `KW T`: the statement of MATH3's Lemma KW (`𝒦_Φ ≡ 0 ⇒ 𝒦_{wΦ} ≡ 0`).  It is **not** section
  level (its proof needs (Exp), (Aut), (C10′) and Theorem E); it is a named hypothesis here.
* `Kir_w_delta_inv` — **(INV)** of MATH3 §4.2, from `KW`: `𝒦_{wΦ₀}(βu) = 𝒦_{wΦ₀}(β)` for
  `u ∈ 1 + 𝔩_{k+1}`, `Φ₀` a delta section.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

/-- For a delta section, `ξ_{Φ₀} = 𝒦_{Φ₀} = 1_{U_k}` on `F^×`. -/
theorem xi_delta (k : ℕ) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ₀ β = open Classical in if Small 𝔪 ((k : ℤ) + 1) (β - 1) then 1 else 0)
    {β : F} (hβ : β ≠ 0) :
    xi hG hz6 T Φ₀ β = open Classical in if Small 𝔪 ((k : ℤ) + 1) (β - 1) then 1 else 0 := by
  classical
  rw [xi, hΦ₀ β hβ]
  by_cases hs : Small 𝔪 ((k : ℤ) + 1) (β - 1)
  · rw [if_pos hs, absS_eq_one_of_val hG.ne_bot (fun v hv => hs.val_eq_one (by omega) v hv)]
    simp
  · rw [if_neg hs, mul_zero]

/-! ### Lemma KW as a hypothesis, and (INV) -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem cellM_bdd (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    ∀ x ∈ cellM 𝔪 M, ∀ w, ‖x w‖ ≤ cellN 𝔪 M := by
  unfold cellM cellN
  rw [dif_pos ⟨h𝔪, hM⟩, dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.2

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

theorem kap_ne_zero (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : kap 𝔪 M ≠ 0 := by
  unfold kap
  refine inv_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ?_ (vol_pos 𝔪 M)).ne')
  exact volume_toReal_pos (pcell_cellM h𝔪 hM) (cellM_bdd h𝔪 hM)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Kap
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 9: the constant `kap 𝔪 M` is `covol(𝓞_F)⁻¹`

By WP-BZ's `volume_cell'` (WP-B's stub B-2): `kap 𝔪 M = (volume (B1.fundD F)).toReal⁻¹` for every
`M ≥ 0`; in particular it does not depend on `M`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

theorem kap_eq (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    kap 𝔪 M = ((((volume (B1.fundD F)).toReal : ℝ)) : ℂ)⁻¹ := by
  have h := BZ.volume_cell' h𝔪 M ((pcell_cellM h𝔪 hM).isAddFundamentalDomain volume)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (vol_pos 𝔪 M).le] at h'
  rw [kap, h']

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Exp
/-! # WP-G2a, file 6: the pointwise theta function and **(Exp)**

* `kapC F = covol(𝓞_F)⁻¹` (`= T.kap 𝔪 M` for every `M ≥ 0`).
* `IsExp Φ z`: for every finite-index `Γ` fixing `Φ.twist`,
  `X.lift Γ (C5.theta Γ Φ.twist) = z·ht^{2/3} + kapC·thetaS Φ` almost everywhere.
* **`exists_isExp`** (Theorem E + `hdiff`): such a `z` exists.  (Fourier uniqueness on the full
  stabilizer, `C9.ae_eq_htC_of_coeff`; other groups by `N.lift_theta_congr`.)
* `zc Φ` := that `z` (unique: `isExp_unique`); **`thetaT Φ Q := zc Φ·ht(Q)^{2/3} + kapC·thetaS Φ Q`**,
  continuous, and `thetaT_ae`: it represents `θ_{Φ.twist}` for every admissible `Γ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

lemma kap_eq_kapC (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : T.kap 𝔪 M = kapC F := T.kap_eq h𝔪 hM

lemma kapC_ne_zero (h𝔪 : 𝔪 ≠ ⊥) : kapC F ≠ 0 := by
  rw [← kap_eq_kapC h𝔪 le_rfl]
  exact T.kap_ne_zero h𝔪 le_rfl

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

lemma cj_mul (m : ℤ) (a b : ℂ) : cj m (a * b) = cj m a * cj m b := by
  unfold cj; split_ifs <;> simp

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

variable {hG hz6}

lemma C0_ne_zero : C0 ≠ 0 := by
  unfold C0
  have h1 : Complex.Gamma (4 / 3) ≠ 0 := by
    have : (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.Gamma_ofReal]
    exact Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h2 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  exact mul_ne_zero (div_ne_zero h2 h1) (Complex.ofReal_ne_zero.mpr (by positivity))

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.GR_Arch
/-! # WP-GR, file 1: the archimedean dictionary

G2a's profile `∏_w ω_{m_w}(ν_w Y_w)·κ(|ν_w Y_w|²)` (`G2a.omg`, `K.kappaB (4π)`) against the
frozen `L3X.fpF κ m (sEmb ν + y)` and `H0.FmOf κ m J cl (sEmb ν̃ − y)`.

* `Yof y w = exp(y.1 w / 2)·e^{iθ_w}` (MATH3 §0), `Yrt` a square root of it.
* `omg_polar`: for `m = ±1`, `ω_m(z·r·e^{iθ}) = e^{i m arg z}·e^{i m θ}`.
* `arch_forward`: the product at `ν_w·Y_w`;
* `arch_reflected`: the product of type `−m` at `ν̃_w / Y_w`.
-/

open scoped ComplexConjugate Topology Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.G2a ArtinKP.K

noncomputable section

/-! ### One place -/

lemma toCircle_coe (x : ℝ) :
    ((AddCircle.toCircle ((x : ℝ) : AddCircle (2 * Real.pi)) : Circle) : ℂ)
      = Complex.exp (x * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  rw [div_self (by positivity), one_mul]

lemma toCircle_arg {z : ℂ} (hz : z ≠ 0) :
    ((AddCircle.toCircle ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi)) : Circle) : ℂ)
      = z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [toCircle_coe, eq_div_iff hn, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma toCircle_neg_one_zsmul (a : AddCircle (2 * Real.pi)) :
    ((AddCircle.toCircle ((-1 : ℤ) • a) : Circle) : ℂ)
      = conj ((AddCircle.toCircle a : Circle) : ℂ) := by
  rw [neg_one_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

lemma cj_toCircle {m : ℤ} (hm : m = 1 ∨ m = -1) (a : AddCircle (2 * Real.pi)) :
    cj m ((AddCircle.toCircle a : Circle) : ℂ) = ((AddCircle.toCircle (m • a) : Circle) : ℂ) := by
  rcases hm with rfl | rfl
  · simp [cj]
  · rw [toCircle_neg_one_zsmul]
    simp [cj]

lemma cj_ofReal (m : ℤ) (r : ℝ) : cj m (r : ℂ) = (r : ℂ) := by
  unfold cj; split_ifs <;> simp

lemma cj_div (m : ℤ) (a b : ℂ) : cj m (a / b) = cj m a / cj m b := by
  unfold cj; split_ifs <;> simp

/-- `ω_m(z) = e^{i m arg z}` for `m = ±1`. -/
lemma omg_eq_toCircle {m : ℤ} (hm : m = 1 ∨ m = -1) {z : ℂ} (hz : z ≠ 0) :
    omg m z = ((AddCircle.toCircle (m • ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))) :
      Circle) : ℂ) := by
  rw [← cj_toCircle hm, toCircle_arg hz, cj_div, cj_ofReal, omg]

/-- `ω_m(z·r·e^{iθ}) = e^{i m arg z}·e^{i m θ}` for `m = ±1`, `r > 0`. -/
lemma omg_polar {m : ℤ} (hm : m = 1 ∨ m = -1) {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r)
    (θ : AddCircle (2 * Real.pi)) :
    omg m (z * ((r : ℂ) * ((AddCircle.toCircle θ : Circle) : ℂ))) =
      ((AddCircle.toCircle (m • ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))) : Circle) : ℂ) *
        ((AddCircle.toCircle (m • θ) : Circle) : ℂ) := by
  rw [← omg_eq_toCircle hm hz, ← cj_toCircle hm, omg, omg, cj_mul, cj_mul, cj_ofReal, norm_mul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]
  have h1 : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have h2 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp

lemma norm_polar (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : AddCircle (2 * Real.pi)) :
    ‖z * ((r : ℂ) * ((AddCircle.toCircle θ : Circle) : ℂ))‖ = ‖z‖ * r := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]

/-! ### The archimedean coordinate `Y(y)` -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

variable [IsTotallyComplex F]

lemma mult_eq_two (w : InfinitePlace F) : w.mult = 2 := by
  rw [InfinitePlace.mult, if_neg]
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)

/-- **Forward dictionary**: G2a's profile at `ν_w·Y_w` is the archimedean factor of
`L3X.fpF κ m (sEmb ν + y)` (`H0.fpF_sEmb_add`). -/
theorem arch_forward (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
    {ν : F} (hν : ν ≠ 0) (y : SModel 𝔪 k) :
    ∏ w : InfinitePlace F, (omg (m w) (w.embedding ν * Yof y w) *
        (κ (‖w.embedding ν * Yof y w‖ ^ 2) : ℂ)) =
      ∏ w : InfinitePlace F, ((AddCircle.toCircle (m w • ((Complex.arg (w.embedding ν) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ) *
          ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) *
          (κ (w ν ^ w.mult * Real.exp (y.1 w)) : ℂ) := by
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding ν ≠ 0 := (map_ne_zero _).mpr hν
  rw [Yof, omg_polar (hm w) hz (Real.exp_pos _), norm_polar _ (Real.exp_pos _),
    InfinitePlace.norm_embedding_eq, mult_eq_two, mul_pow, ← Real.exp_nat_mul]
  congr 3
  push_cast
  ring_nf

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GR_Theta
/-! # WP-GR, file 3: `Θ` and its two expansions (MATH3 §1, §2; §6.1 (6))

* `thmE`: G2a's named hypothesis `ThmE` from WP-GK (`GK.per_all`, `S2.cubicSymbol_gen`).
* `Ccon = kapC·(−2πi·C0)^r` (MATH3's `C`).
* **`ThetaG`**: `Θ(x, y) = C⁻¹·Θ_m^{nT(−x)Φ_{y_f}}(emb(−x), Y(y))`, `Φ_{y_f} = GK.PhiB hG Φ₀ (rep y_f)`.
* `xi_PhiB`: `ξ_{Φ_{y_f}}(β) = 1[[β] + y_f = 0]` for a delta section `Φ₀`.
* **`thetaG_forward`**: HB's forward expansion, for every `x ∈ F`.
* **`thetaG_reflected`**: HB's reflected expansion (MATH3 (2.4) with (4.1)), for every `x ∈ F` and
  `γ ∈ SL₂(R)` with bottom row `(c, cx)`, `c ≠ 0`; needs the named hypothesis `WeylFlip`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma Ccon_ne_zero (h𝔪 : 𝔪 ≠ ⊥) : Ccon F ≠ 0 := by
  refine mul_ne_zero (kapC_ne_zero h𝔪) (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr ?_) C0_ne_zero))
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

variable {k : ℕ}

variable {hG hz6}

/-- `ξ_{aΦ} = a·ξ_Φ`. -/
lemma xi_smul (Φ : GSection ι P 𝔪) (a : ℂ) {β : F} (hβ : β ≠ 0) :
    G1.xi hG hz6 (T.theta hG hz6) (a • Φ) β = a * G1.xi hG hz6 (T.theta hG hz6) Φ β := by
  rw [G1.xi, G1.xi, G1.Kir_smul hG hz6 _ Φ a hβ]
  ring

/-- **`ξ_{Φ_{y_f}}(β) = 1[[β] + y_f = 0]`** (MATH3 §1.2, last display), `Φ₀` a delta section of
level `k`, `k + 1` deep. -/
theorem xi_PhiB (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : GK.IsDelta hG hz6 k Φ₀) (β₀ : Fˣ) {β : F} (hβ : β ≠ 0) :
    G1.xi hG hz6 (T.theta hG hz6) (GK.PhiB hG Φ₀ β₀) β =
      if SFin.mk 𝔪 k (Units.mk0 β hβ) + SFin.mk 𝔪 k β₀ = 0 then 1 else 0 := by
  have hβ₀ := β₀.ne_zero
  have h1 := G1.xi_torusT hG hz6 (T.theta hG hz6) Φ₀ hβ hβ₀
  rw [GK.PhiB, xi_smul _ _ hβ, h1,
    G1.xi_delta hG hz6 (T.theta hG hz6) k hΦ₀ (mul_ne_zero hβ hβ₀)]
  have hiff : SFin.mk 𝔪 k (Units.mk0 β hβ) + SFin.mk 𝔪 k β₀ = 0 ↔
      Small 𝔪 ((k : ℤ) + 1) (β * (β₀ : F) - 1) := by
    rw [← L3X.SFin.mk_mul, H0.SFin_mk_eq_zero_iff, G1.mem_SLevel_iff_small]
    rfl
  by_cases hs : Small 𝔪 ((k : ℤ) + 1) (β * (β₀ : F) - 1)
  · rw [if_pos hs, if_pos (hiff.mpr hs), mul_one]
    have hs' : Small 𝔪 ((k + 1 : ℕ) : ℤ) (β * (β₀ : F) - 1) := by
      push_cast; exact hs
    have h2 : brk ι P 𝔪 (β * (β₀ : F)) (β₀ : F) = 1 := brk_deep_left hG hk _ hs'
    rwa [brk_mul_left _ hβ hβ₀, brk_self, mul_one] at h2
  · rw [if_neg hs, if_neg (fun h => hs (hiff.mp h)), mul_zero]

variable {g : AllowedGen ι 𝔪}

/-- **The forward expansion** (MATH3 §1.3; HB's `thetaG_forward`), for every `x ∈ F`. -/
theorem thetaG_eq_tsum_forward_oai (hE : ThmE hG hz6 g P) (hk : P.IsDeepLevel 𝔪 (k + 1))
    {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
    (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F) (y : SModel 𝔪 k) :
    ThetaG hG hz6 m Φ₀ x y =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * x)) *
        (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
          L3X.fpF (kappaB (4 * Real.pi)) m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y)) := by
  have hC := Ccon_ne_zero (F := F) hG.ne_bot
  rw [ThetaG, ThetaM_nT hE, ← Ccon, inv_mul_cancel_left₀ hC]
  refine tsum_congr fun ν => ?_
  have hν : ((ν : SInt 𝔪) : F) ≠ 0 := H0.coe_ne_zero ν
  rw [mul_neg, xi_PhiB hk hΦ₀ _ hν, H0.fpF_sEmb_add _ _ hν, G1.mk_repS,
    arch_forward (kappaB (4 * Real.pi)) m hm hν y]
  split_ifs <;> ring

end

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.thetaG_eq_tsum_forward_oai.{u_1} := @ArtinKP.GR.thetaG_eq_tsum_forward_oai.{u_1}
