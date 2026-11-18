-- Prove2me | solution 1 for ArtinKP.F.integral_restrict_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:33.623427+00:00
-- url     : https://prove2.me/submissions/60c0c3d0-3924-42dd-a13f-e4d17ba34777

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
import Theorems.Thm_ArtinKP_F_U_coeff
import Theorems.Thm_ArtinKP_F_const_adm

section
-- module Solutions.Artin.KP.B7_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma card_quot_gen :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) = Ideal.absNorm v.asIdeal :=
  (congrArg (fun I : Ideal (SInt 𝔪) => Nat.card (SInt 𝔪 ⧸ I)) (span_gen h g)).trans (C3I.natCard_L h)

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinKP.S.TSection.instCoeFunForallComplexForallRow _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.B.Row.inf_d _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.add_apply _root_.ArtinKP.S.TSection.smulFun_apply _root_.ArtinKP.S.TSection.smul_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.TSection.zero_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

variable {𝔪 : Ideal (𝓞 F)}

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

section kappa2

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include P hG hz6

/-- `κ(c, d + ct) = κ(c, d)`. -/
theorem kappaRow_n (p : Row 𝔪) (t : SInt 𝔪) : kappaRow ι (p.act (nMat t)) = kappaRow ι p := by
  have hk : kappa ι 𝔪 (nMat t) = 1 := by
    rw [kappa, if_pos (nMat_10 t)]
  rw [kappaRow_act ι P hG hz6, hk, mul_one]
  have h1 : Xs (0 : F) 1 = 1 := Xs_zero 1
  have e : sig ι P 𝔪 (p.c : F) (p.d : F) (((nMat t).1 0 0 : SInt 𝔪) : F)
      (((nMat t).1 0 1 : SInt 𝔪) : F) (((nMat t).1 1 0 : SInt 𝔪) : F)
      (((nMat t).1 1 1 : SInt 𝔪) : F) = 1 := by
    simp only [sig, nMat_00, nMat_01, nMat_10, nMat_11]
    push_cast
    rw [show (p.c : F) * 1 + (p.d : F) * 0 = p.c by ring, h1, div_one]
    by_cases hc : (p.c : F) = 0
    · have hd : (p.d : F) ≠ 0 := p.ne_zero.resolve_left (not_not.mpr hc)
      simp [hc, div_self hd]
    · simp [Xs_of_ne _ hc, div_self hc]
  rw [e, inv_one, mul_one]

end kappa2

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The product formula for `S`-units -/

theorem Ninf_pos {x : F} (hx : x ≠ 0) : 0 < Ninf x :=
  Finset.prod_pos fun _ _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)

theorem Ninf_mul (x y : F) : Ninf (x * y) = Ninf x * Ninf y := by
  simp only [Ninf, map_mul, Finset.prod_mul_distrib]

/-! ### Rows modulo `S`-units -/

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

/-! ### Height form (MATH2 §0.2) -/

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

theorem cpow_sq_cancel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (6 * s) * ((x ^ 2 : ℝ) : ℂ) ^ (-(3 * s)) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx2 : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hx 2).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx2, ← Complex.exp_add,
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (pow_pos hx 2).le, Real.log_pow]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem sharp_apply (hG : Good 𝔪) (π : F) (hπ : π ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.sharp hG π hπ s c d = Φ s c (d / π ^ 3) := by
  have htf : tf ι P 𝔪 (π ^ 3) c d = 1 := by
    unfold tf
    split_ifs
    · exact brk_pow_three_right _ _
    · rw [brk_pow_three_right, one_pow]
  have e1 : (π ^ 3) ^ 2 * c = (π ^ 2) ^ 3 * c := by ring
  have e2 : π ^ 3 * d = (π ^ 2) ^ 3 * (d / π ^ 3) := by field_simp
  change ((absS 𝔪 π : ℝ) : ℂ) ^ (6 * s) * (tf ι P 𝔪 (π ^ 3) c d
    * Φ s ((π ^ 3) ^ 2 * c) (π ^ 3 * d)) = _
  rw [htf, one_mul, e1, e2, Φ.cube s (π ^ 2) (pow_ne_zero 2 hπ), absS_pow, ← mul_assoc,
    cpow_sq_cancel (absS_pos hπ), one_mul]

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem emb_mul (a b : F) : emb (a * b) = emb a * emb b := by
  ext w
  simp

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem chiInf_zero (x : InfinitePlace F → ℂ) : chiInf (0 : F) x = 1 := by
  simp [chiInf, eInf, archChar]

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.E_Series
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-! # E_Series: the Kubota coefficient series and its splitting at a prime (corrected (4.1))

Abstract setting (`R` a domain; in the application `R = SInt 𝔪`):

* `Cls R` = nonzero classes of `R` modulo units (`(R∖0)/U_S`), `ClsP π` = those prime to `π`;
  `tsum_split`: a unit-invariant absolutely summable family over `Cls R` is the iterated sum over
  `c = π^j c'`, `π ∤ c'`.
* `Pairing S`: the pairing `⟨c, d⟩` (in the application `ι (c, d)_S`, WP-A's `HS`).
* `Kubota S A Sec`: the **interface** to the analytic packages.  A section `Φ : Sec` is seen only
  through its normalized finite Jacquet functional `Lam Φ c ν s = |c|_{S_f}^s · J_Φ(c; ν, s)`, and
  `act β = Ã(β)` (MATH2 §6.1).  The coefficient series is
  `aSer Φ ν s = ∑_{c ∈ (R∖0)/U} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`.
* `aSer_split` — **(4.1′)**: for `π ∤ ν₀`, `Re s > 2`,
  `aSer Φ (ν₀ π^k) s = Cform q G G' x (m ↦ Y_m(Ã(π)^k Φ)) k`, with B7's `Cform` verbatim, `x = q^{-s}`,
  and the three `π`-coprime twisted series `Y_m(Ψ) = ∑_{π ∤ c'} g(ν₀,c') ((π/c')(c'/π))^{-m}
  Lam Ψ (π^m c') ν₀ s N(c')^{-s}`.
* `aSer_unit` (MATH2 Lemma 6.2), `Lam_act_act` (`Ã(β)Ã(β') = ⟨β,β'⟩ Ã(ββ')` on `Lam`),
  `Lam_iter_eq_pow`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### Classes modulo units -/

/-! ### The norm `N(c) = #(R/cR)` -/

/-! ### Symbols -/

namespace Pairing

variable {S : CubicSymbol R} (B : Pairing S)

lemma br_ne_zero {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : B.br a b ≠ 0 := by
  intro h
  have := B.br_pow_three a b ha hb
  rw [h] at this
  norm_num at this

lemma br_one_left {b : R} (hb : b ≠ 0) : B.br 1 b = 1 := by
  have h := B.br_mul_left 1 1 b one_ne_zero one_ne_zero hb
  rw [one_mul] at h
  exact (mul_eq_left₀ (B.br_ne_zero one_ne_zero hb)).1 h.symm

lemma br_pow_left {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    B.br (a ^ n) b = B.br a b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, B.br_one_left hb]
  | succ n ih => rw [pow_succ, B.br_mul_left _ _ _ (pow_ne_zero _ ha) ha hb, ih, pow_succ]

/-- `⟨π^n c, π⟩ = ⟨c, π⟩`. -/
lemma br_pow_mul_self {π c : R} (hπ : π ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    B.br (π ^ n * c) π = B.br c π := by
  rw [B.br_mul_left _ _ _ (pow_ne_zero _ hπ) hc hπ, B.br_pow_left hπ hπ, B.br_self π hπ, one_pow,
    one_mul]

end Pairing

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- `Ã(π)^k` on `Lam`: `Lam (Ã(π)^k Φ) c ν = ⟨c,π⟩^{2k} Lam Φ (π^{2k} c) (π^k ν)`. -/
theorem Lam_iter (Φ : Sec) {π : R} (hπ : π ≠ 0) (k : ℕ) (c ν : R) {s : ℂ} (hc : c ≠ 0)
    (hs : 2 < s.re) :
    D.Lam ((D.act π)^[k] Φ) c ν s =
      D.br c π ^ (2 * k) * D.Lam Φ (π ^ (2 * k) * c) (π ^ k * ν) s := by
  induction k generalizing c ν with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', D.Lam_act _ π c ν s hπ hc hs,
      ih _ _ (mul_ne_zero (pow_ne_zero _ hπ) hc), D.toPairing.br_pow_mul_self hπ hc,
      show π ^ (2 * k) * (π ^ 2 * c) = π ^ (2 * (k + 1)) * c by ring,
      show π ^ k * (π * ν) = π ^ (k + 1) * ν by ring]
    ring

/-- `Ã(π)³` translates the frequency by `π³` and does nothing else (MATH2 Lemma 6.1(ii):
`Ã(π)³Φ = |π|^{-3} Φ(c, d/π³)`). -/
theorem Lam_iter_three (Φ : Sec) {π : R} (hπ : π ≠ 0) (c ν : R) {s : ℂ} (hc : c ≠ 0)
    (hs : 2 < s.re) : D.Lam ((D.act π)^[3] Φ) c ν s = D.Lam Φ c (π ^ 3 * ν) s := by
  have h3 := D.br_pow_three c π hc hπ
  rw [D.Lam_iter Φ hπ 3 c ν hc hs, show π ^ (2 * 3) * c = (π ^ 2) ^ 3 * c by ring,
    D.Lam_cube Φ (π ^ 2) c _ s (pow_ne_zero _ hπ) hc hs, show 2 * 3 = 3 * 2 by norm_num, pow_mul,
    h3, one_pow, one_mul]

end Kubota

/-! ### The prime datum and the splitting (4.1′) -/

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem kubota_Lam (c : SInt 𝔪) (s : ℂ) :
    (kubota hG hz6).Lam Φ c ν s = S2.LamR (psiS hG.ne_bot) hG Φ c ν s := rfl

theorem kubota_act (β : SInt 𝔪) : (kubota hG hz6).act β Φ = S2.actR hG β Φ := rfl

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.F_Eis_Op
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-FB, part 2: the maps `g_t` on `X F`, the operator `U`, and the product formula at `π`

MATH2 §5.1: `g_t : (x, v) ↦ ((x + t)/π³, v/|π³|)` is the action of the `GL₂(F)` matrix
`[[1, t], [0, π³]]`, of determinant `π³`; it is **not** in `SL₂(F)`, and the tree's action on
`X F` is of `SL(2, F)` only.  So the map is defined in coordinates, for an arbitrary `a ≠ 0` in
place of `π³`:

* `gmap a ha t : X F → X F`, `(x, v) ↦ ((x + t)/a, v/|a|)` (ordinary moduli at each place);
  `gmap_eq_torus_trans` (it is `X.torus ∘ X.trans`), `measurePreserving_gmap`, `continuous_gmap`;
* `Nh a = ∏_w |a|_w` (ordinary moduli; `Nh a ^ 2 = B.Ninf a`, so `Nh a = N_∞(a)^{1/2}`);
* `pairHt_gmap`: `I_{(c,d)}(g_t Q) = Nh a · I_{(c, c t + a d)}(Q)`
  (MATH2: `N_∞(π)^{3/2}` for `a = π³`); `ht_gmap`;
* `U a ha T u Q = ∑_{t ∈ T} u (g_t Q)`;
* `Ninf_mul_absS_of_span`: `N_∞(π) · |π|_{S_f} = N P` for a generator `π` of `P·R`, `P` exterior
  (the product formula; WP-FA §6 item 2), and `Ninf_mul_absS_gen` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### `Nh`: the product of the ordinary moduli -/

theorem Nh_pos {a : F} (ha : a ≠ 0) : 0 < Nh a :=
  Finset.prod_pos fun _ _ => norm_pos_iff.2 ((map_ne_zero _).2 ha)

theorem Nh_nonneg (a : F) : 0 ≤ Nh a := Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem Nh_sq (a : F) : Nh a ^ 2 = Ninf a := by
  unfold Nh Ninf
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun w _ => (Complex.normSq_eq_norm_sq _).symm

theorem Nh_pow (a : F) (n : ℕ) : Nh (a ^ n) = Nh a ^ n := by
  simp only [Nh, map_pow, norm_pow, Finset.prod_pow]

/-- `Nh(a)^s = N_∞(a)^{s/2}` as complex powers. -/
theorem Nh_cpow {a : F} (ha : a ≠ 0) (s : ℂ) :
    ((Nh a : ℝ) : ℂ) ^ s = ((Ninf a : ℝ) : ℂ) ^ (s / 2) := by
  have h0 : ((Nh a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Nh_pos ha).ne'
  rw [← Nh_sq, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nh_nonneg a) (Nh_nonneg a),
    ← Complex.cpow_add _ _ h0]
  congr 1
  ring

/-! ### The maps `g_t` -/

/-! ### The operator `U` -/

/-! ### The product formula at a generator of an exterior prime -/

open NumberField.HeightOneSpectrum in
theorem adicAbv_eq_inv_of_val {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (h : v.valuation F x = WithZero.exp (-1 : ℤ)) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast (zero_lt_one.trans h')
  have h1 := abv_le_of_val_le v (x := x) (n := 1) h.le
  have h2 := abv_le_of_val_le v (x := x⁻¹) (n := -1)
    (by rw [map_inv₀, h, ← WithZero.exp_neg])
  rw [zpow_neg_one] at h1
  rw [neg_neg, zpow_one, map_inv₀] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx0
  refine le_antisymm h1 ?_
  rw [inv_le_comm₀ hq hpos]
  exact h2

/-- **`N_∞(π) · |π|_{S_f} = N P`** for a generator `π` of `P·R`, `P` an exterior prime. -/
theorem Ninf_mul_absS_of_span [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) {π : SInt 𝔪} (hπ : π ≠ 0)
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    Ninf (π : F) * absS 𝔪 (π : F) = Ideal.absNorm v.asIdeal := by
  classical
  obtain ⟨hvv, hw⟩ := val_generator v hv π hspan
  have hπF : (π : F) ≠ 0 := fun h => hπ (Subtype.ext h)
  have hnot : FinitePlace.mk v ∉ sPl 𝔪 := by
    intro hmem
    obtain ⟨v', hv', he⟩ := Finset.mem_image.mp hmem
    rw [FinitePlace.mk_eq_iff] at he
    exact hv ((CubicPkg.mem_sFin h𝔪 v).mp (he ▸ hv'))
  have h2 : ∏ᶠ w : FinitePlace F, w (π : F)
      = ∏ w ∈ insert (FinitePlace.mk v) (sPl 𝔪), w (π : F) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw' => ?_
    by_contra hwS
    rw [Finset.mem_coe, Finset.mem_insert, not_or] at hwS
    apply hw'
    have e : w (π : F) = NumberField.HeightOneSpectrum.adicAbv F w.maximalIdeal (π : F) := by
      conv_lhs => rw [← FinitePlace.mk_maximalIdeal w]
      exact mk_apply_eq _ _
    change w (π : F) = 1
    rw [e]
    refine abv_eq_one_of_val_eq_one _ (hw _ (fun hle => hwS.2 ?_) (fun he => hwS.1 ?_))
    · rw [← FinitePlace.mk_maximalIdeal w]
      exact Finset.mem_image_of_mem _ ((CubicPkg.mem_sFin h𝔪 _).mpr hle)
    · rw [← FinitePlace.mk_maximalIdeal w, he]
  rw [Finset.prod_insert hnot, prod_sPl_eq_absS, mk_apply_eq, adicAbv_eq_inv_of_val hvv,
    X.finprod_finitePlace hπF] at h2
  have hN : 0 < Ninf (π : F) := Ninf_pos hπF
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast (zero_lt_one.trans h')
  change (Ninf (π : F))⁻¹ = _ at h2
  field_simp at h2
  linarith

/-- The product formula at an allowed generator of a good exterior prime, with FA's `q`. -/
theorem Ninf_mul_absS_gen [IsTotallyComplex F] {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)}
    (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥) :
    Ninf (g.gen v.asIdeal : F) * absS 𝔪 (g.gen v.asIdeal : F)
      = (Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) : ℝ) := by
  rw [card_quot_gen h g]
  exact Ninf_mul_absS_of_span h𝔪 (not_le_of_good h) (gen_ne_zero h g) (span_gen h g)

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 4: the operator `U` on Fourier coefficients (MATH2 §5.1)

Vocabulary of WP-B (`B_FourArch`): `emb : F →+ ℂ^r`, `eInf`, and the character
`chiInf ν x = conj e_∞(ν x)` against which the `ν`-th coefficient is taken; a coefficient is an
integral over a cell `D` (a fundamental domain of a lattice `L ⊂ ℂ^r` of periods).

* `sum_eInf_reps`: `∑_{t ∈ T} e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]` for `T` deep
  (`FA.sum_reps_sAddChar` and `B.psiS_small`);
* `setIntegral_image_mulE`: the change of variables `x = a·y` on `ℂ^r`, Jacobian `N_∞(a)`;
* `setIntegral_translate`, `integrableOn_translate`: integrals of periodic functions over a
  cell are translation invariant;
* `coeff_sum_translate`: on `ℂ^r`, for an `L`-periodic `h`,
  `∫_{aD} (∑_t h((x+t)/a)) conj e_∞(νx) dx = N_∞(a) (∑_t e_∞(νt)) ∫_D h(y) conj e_∞(νa·y) dy`;
* `coeff_U`: the same for `U a T u` at height `v`;
* `coeff_U_gen`: **`(Uu)_ν(v) = q³ · 1[ν ∈ R] · u_{νπ³}(v/|π³|)`** at `π = g.gen P`
  (cells `π³D` and `D`; the factor `N_∞(π³) = vol(π³D)/vol(D)` is the normalization of the cell).
-/

set_option autoImplicit false

open scoped ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The character sum in `e_∞` form -/

/-! ### Scaling on `ℂ^r` -/

theorem mulE_apply (A y : InfinitePlace F → ℂ) : mulE A y = A * y := by
  ext w
  simp [mulE]

theorem det_mulE (A : InfinitePlace F → ℂ) :
    LinearMap.det (mulE A) = ∏ w, Complex.normSq (A w) := by
  rw [mulE, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  change LinearMap.det (Algebra.lmul ℝ ℂ (A w)) = _
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply]

/-- Change of variables `x = A·y` on `ℂ^r`: the Jacobian is `∏_w |A_w|²`. -/
theorem setIntegral_image_mulE {A : InfinitePlace F → ℂ} (hA : ∀ w, A w ≠ 0)
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (G : (InfinitePlace F → ℂ) → ℂ) :
    ∫ x in (fun y => A * y) '' D, G x
      = ((∏ w, Complex.normSq (A w) : ℝ) : ℂ) * ∫ y in D, G (A * y) := by
  have e : (fun y : InfinitePlace F → ℂ => A * y)
      = ⇑(LinearMap.toContinuousLinearMap (mulE A)) := funext fun y => (mulE_apply A y).symm
  have hinj : Set.InjOn (fun y : InfinitePlace F → ℂ => A * y) D := by
    intro y _ y' _ hyy
    funext w
    exact mul_left_cancel₀ (hA w) (congrFun hyy w)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (f := fun y : InfinitePlace F → ℂ => A * y)
    (f' := fun _ => LinearMap.toContinuousLinearMap (mulE A))
    (fun x _ => by
      rw [e]
      exact (LinearMap.toContinuousLinearMap (mulE A)).hasFDerivAt.hasFDerivWithinAt) hinj G
  rw [h]
  have hdet : (LinearMap.toContinuousLinearMap (mulE A)).det = ∏ w, Complex.normSq (A w) := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, det_mulE]
  simp only [hdet]
  rw [abs_of_nonneg (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _), integral_smul,
    Complex.real_smul]

/-! ### Translation invariance over a cell -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 3: Proposition 5.4 for the Eisenstein series `B.eis`, `Re s > 2` (MATH2 §5.3)

With `Ψ = Φ.twist`, `Ψ♯ = (Φ.sharp π).twist`, `q = #(R/πR) = N P`, `T` a complete set of
representatives of `R/π³R` deep for `Φ`, and `U = FB.U (π³) T`:

  `U (eis Ψ s) Q = Nh(π³)^s · [ q³·(q^{-s})³ · eis Ψ♯ s Q + (1 − q²·(q^{-s})³) · eis (restrict Ψ♯) s Q ]`

pointwise in `Q : X F`, for every `s` with `Re s > 2`; `Nh(π³)^s = N_∞(π)^{3s/2}`
(`Nh_pi_cube_cpow`), `q³(q^{-s})³ = q^{3-3s}`, `q²(q^{-s})³ = q^{2-3s}` (`q_cpow_three`,
`q_cpow_two`).

* `primeElt_gen'`: `FA.PrimeElt` at `g.gen P`, unconditional (S2's cubic symbol);
* `fQ`, `fQ_pi`, `fQ_unit`: the summand `f = I_p(Q)^s` and its two homogeneities;
* `term_gmap`, `eis_gmap`: `eis Ψ s (g_t Q) = Nh(π³)^s · ∑' gU`;
* `U_eis_primeElt`: the identity for any `PrimeElt`, with FA's constants;
* `U_eis`: the same with `X = (q^{-s})³` under `N_∞(π)|π|_{S_f} = q`;
* `U_eis_gen`, `exists_U_eis_gen`: at an allowed generator of a good exterior prime, all
  hypotheses discharged; the second also produces the deep `T`, uniformly in `s`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The summand `f = I_p(Q)^s` -/

/-! ### The Eisenstein series at `g_t Q` -/

/-! ### Rewriting the constants in MATH2's form -/

/-- `Nh(π³)^s = N_∞(π)^{3s/2}`. -/
theorem Nh_pi_cube_cpow {a : F} (ha : a ≠ 0) (s : ℂ) :
    ((Nh (a ^ 3) : ℝ) : ℂ) ^ s = ((Ninf a : ℝ) : ℂ) ^ (3 * s / 2) := by
  have h0 : 0 ≤ Nh a := Nh_nonneg a
  have hN : ((Ninf a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Ninf_pos ha).ne'
  rw [Nh_pow, pow_three, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg h0 (mul_nonneg h0 h0), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg h0 h0,
    Nh_cpow ha, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN]
  congr 1
  ring

/-- `q³ (q^{-s})³ = q^{3-3s}`. -/
theorem q_cpow_three {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    (q : ℂ) ^ 3 * ((q : ℂ) ^ (-s)) ^ 3 = (q : ℂ) ^ (3 - 3 * s) := by
  have h0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ h0]
  congr 1; push_cast; ring

/-- `q² (q^{-s})³ = q^{2-3s}`. -/
theorem q_cpow_two {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    (q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3 = (q : ℂ) ^ (2 - 3 * s) := by
  have h0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ h0]
  congr 1; push_cast; ring

/-! ### At an allowed generator of a good exterior prime -/

/-! ### Regularity in `s` and `Q`, and almost-everywhere classes

What a later package needs to continue the identity of `U_eis_gen` analytically: `T` does not
depend on `s` (`exists_U_eis_gen`); both sides are holomorphic in `s` on `Re s > 2` for each
`Q` (`differentiableOn_U_eis`, `B.differentiableOn_eis`) and continuous in `Q`; and `U` is
defined on almost-everywhere classes (`U_ae_congr`, from `measurePreserving_gmap`), so it acts
on `L²_loc`-valued functions of `s`. -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem validDepth_mono {ν' : F} {M M' : ℤ} (h : ValidDepth hG Φ ν' M) (hMM : M ≤ M') :
    ValidDepth hG Φ ν' M' :=
  ⟨fun b hb => h.unip b (hb.mono hMM), fun x hx => h.char x (hx.mono hMM)⟩

theorem exists_validDepth_nonneg (ν' : F) : ∃ M : ℤ, 0 ≤ M ∧ ValidDepth hG Φ ν' M := by
  obtain ⟨M, hM⟩ := exists_validDepth hG Φ ν'
  exact ⟨max M 0, le_max_right _ _, validDepth_mono hG Φ hM (le_max_left _ _)⟩

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

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

lemma intMat_nInt (β : 𝓞 F) :
    RO.intMat 𝔪 (nInt β) = S.nMat (algebraMap (𝓞 F) (SInt 𝔪) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RO.intMat, nInt_coe, S.nMat]

/-- `Λ_M ⊆ Λ_{stab}` for a depth `M ≥ 0` of unipotent invariance of `Φ`. -/
theorem transLat_le_latN_stabGroup {M : ℤ} (hM : 0 ≤ M)
    (hunip : ∀ b : F, Small 𝔪 M b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d) :
    transLat 𝔪 M ≤ latN (stabGroup (Φ.twist hG hz6)) := by
  intro g hg
  obtain ⟨β, -, hβ⟩ := transLat_le_latO hM hg
  obtain ⟨b, hb, hbg⟩ := hg
  have hβb : ((β : 𝓞 F) : F) = (b : F) := by
    have h0 : emb (((β : 𝓞 F) : F) - (b : F)) = 0 := by
      rw [map_sub, sub_eq_zero]
      have h1 : emb ((β : 𝓞 F) : F) = g := hβ
      have h2 : emb (b : F) = g := hbg
      rw [h1, h2]
    exact sub_eq_zero.mp (emb_eq_zero h0)
  refine ⟨β, ?_, hβ⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [intMat_nInt, TSection.mem_stab]
  intro s p
  rw [GSection.twist_apply, GSection.twist_apply, kappaRow_n ι P hG hz6, act_nMat_c,
    act_nMat_d]
  have hsm : Small 𝔪 M ((β : 𝓞 F) : F) := by
    rw [hβb]; exact hb
  have h3 := hunip _ hsm s (p.c : F) (p.d : F)
  push_cast
  rw [add_comm]
  rw [h3]

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

lemma adm_transLat (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : Adm (transLat 𝔪 M) :=
  ⟨transLat_le_latO hM, exists_idealLat_le_transLat h𝔪 M⟩

/-! ### Scaled lattices and cells -/

lemma emb_one : emb (1 : F) = 1 := by
  ext w; simp

lemma emb_inv_mul {a : F} (ha : a ≠ 0) (x : InfinitePlace F → ℂ) :
    emb a⁻¹ * (emb a * x) = x := by
  rw [← mul_assoc, ← emb_mul, inv_mul_cancel₀ ha, emb_one, one_mul]

lemma emb_mul_inv {a : F} (ha : a ≠ 0) (x : InfinitePlace F → ℂ) :
    emb a * (emb a⁻¹ * x) = x := by
  rw [← mul_assoc, ← emb_mul, mul_inv_cancel₀ ha, emb_one, one_mul]

lemma mem_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    {x : InfinitePlace F → ℂ} : x ∈ scaleSet a D ↔ emb a⁻¹ * x ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [emb_inv_mul ha]
  · intro h
    exact ⟨_, h, emb_mul_inv ha x⟩

lemma measurableSet_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) : MeasurableSet (scaleSet a D) := by
  have e : scaleSet a D = (fun x : InfinitePlace F → ℂ => emb a⁻¹ * x) ⁻¹' D := by
    ext x; exact mem_scaleSet ha
  rw [e]
  exact (continuous_const.mul continuous_id).measurable hD

lemma pcell_scale {a : F} (ha : a ≠ 0) {L : AddSubgroup (InfinitePlace F → ℂ)}
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell L D) : PCell (scaleLat a L) (scaleSet a D) := by
  refine ⟨measurableSet_scaleSet ha hD.meas, fun x => ?_⟩
  obtain ⟨g₀, hg₀, huniq⟩ := hD.fund (emb a⁻¹ * x)
  refine ⟨⟨emb a * (g₀ : InfinitePlace F → ℂ), ⟨g₀, g₀.2, rfl⟩⟩, ?_, ?_⟩
  · change emb a * (g₀ : InfinitePlace F → ℂ) + x ∈ scaleSet a D
    rw [mem_scaleSet ha, mul_add, emb_inv_mul ha]
    exact hg₀
  · rintro ⟨g, y, hy, rfl⟩ hg
    have hg' : emb a * y + x ∈ scaleSet a D := hg
    rw [mem_scaleSet ha, mul_add, emb_inv_mul ha] at hg'
    have := huniq ⟨y, hy⟩ hg'
    apply Subtype.ext
    change emb a * y = emb a * (g₀ : InfinitePlace F → ℂ)
    rw [← this]

lemma exists_bdd_scaleSet (a : F) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : ∃ n' : ℕ, ∀ x ∈ scaleSet a D, ∀ w, ‖x w‖ ≤ n' := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖emb a‖
  refine ⟨N * n, ?_⟩
  rintro x ⟨y, hy, rfl⟩ w
  change ‖emb a w * y w‖ ≤ _
  rw [norm_mul]
  push_cast
  exact mul_le_mul ((norm_le_pi_norm (emb a) w).trans hN) (h y hy w) (norm_nonneg _)
    (Nat.cast_nonneg _)

/-- `vol(a·D) = N_∞(a)·vol(D)`. -/
lemma volume_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) :
    (((volume (scaleSet a D)).toReal : ℝ) : ℂ)
      = ((Ninf a : ℝ) : ℂ) * (((volume D).toReal : ℝ) : ℂ) := by
  have hA : ∀ w : InfinitePlace F, emb a w ≠ 0 := fun w => by
    rw [emb_apply]; exact (map_ne_zero _).2 ha
  have h := FB.setIntegral_image_mulE hA hD (fun _ => (1 : ℂ))
  rw [setIntegral_const, setIntegral_const] at h
  simp only [Complex.real_smul, mul_one, measureReal_def] at h
  rw [scaleSet, h]
  rfl

/-- `a·Λ_M ⊆ Λ_{M−K}` for `a ∈ R` with `|a|_v ≤ q_v^K` on `S_f`. -/
lemma scaleLat_transLat_le (r : SInt 𝔪) {K M : ℤ} (hK : Small 𝔪 (-K) (r : F)) :
    scaleLat (r : F) (transLat 𝔪 M) ≤ transLat 𝔪 (M - K) := by
  rintro x ⟨y, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨r * b, ?_, ?_⟩
  · have h1 : Small 𝔪 (-K + M) ((r : F) * (b : F)) := hK.mul hb
    have e : -K + M = M - K := by ring
    rw [e] at h1
    exact h1
  · change emb (((r * b : SInt 𝔪) : F)) = emb (r : F) * emb (b : F)
    rw [← emb_mul]
    rfl

/-- `a·Λ_M` contains the image of a nonzero ideal. -/
lemma exists_idealLat_le_scaleLat (h𝔪 : 𝔪 ≠ ⊥) {a : F} (ha : a ≠ 0) (M : ℤ) :
    ∃ I : Ideal (𝓞 F), I ≠ ⊥ ∧ idealLat I ≤ scaleLat a (transLat 𝔪 M) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (K := F) a
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero hy)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hxy
    exact ha hxy.symm
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  refine ⟨Ideal.span {x * b ^ M.toNat}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hx0 (pow_ne_zero _ hb0), ?_⟩
  rintro z ⟨β, hβ, rfl⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hβ
  have e : ((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F)
      = ((c : 𝓞 F) : F) * ((y : 𝓞 F) : F) * ((b : 𝓞 F) : F) ^ M.toNat := by
    change (((c * y * b ^ M.toNat : 𝓞 F)) : F) = _
    push_cast; rfl
  refine ⟨embR (algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat)), ⟨_, ?_, rfl⟩, ?_⟩
  · have h1 : Small 𝔪 0 ((c * y : 𝓞 F) : F) := fun v _ => by
      simpa using v.valuation_le_one (K := F) (c * y)
    have h2 := h1.mul (small_pow_of_mem hb M.toNat)
    have h3 : Small 𝔪 M ((((c * y : 𝓞 F)) : F) * ((b : 𝓞 F) : F) ^ M.toNat) :=
      h2.mono (by rw [zero_add]; exact Int.self_le_toNat M)
    change Small 𝔪 M (((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F))
    rw [e]
    push_cast at h3
    exact h3
  · change emb a * emb (((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F))
      = emb (((c * (x * b ^ M.toNat) : 𝓞 F)) : F)
    rw [← emb_mul, e]
    congr 1
    have hxy' : a = ((x : 𝓞 F) : F) / ((y : 𝓞 F) : F) := hxy.symm
    have hy0' : ((y : 𝓞 F) : F) ≠ 0 := hy0
    rw [hxy']
    push_cast
    field_simp

/-- **`a·Λ_M` is admissible** for `a ∈ R ∖ 0` and `M` beyond the `S_f`-size of `a`. -/
lemma adm_scaleLat (h𝔪 : 𝔪 ≠ ⊥) (r : SInt 𝔪) (hr : (r : F) ≠ 0) {K M : ℤ}
    (hK : Small 𝔪 (-K) (r : F)) (hKM : K ≤ M) : Adm (scaleLat (r : F) (transLat 𝔪 M)) :=
  ⟨(scaleLat_transLat_le r hK).trans (transLat_le_latO (by omega)),
    exists_idealLat_le_scaleLat h𝔪 hr M⟩

/-! ### Coefficients over cells of admissible lattices -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The Kirillov term -/

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.F_Per_Sharp
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 2: `Φ♯` and `Ã(π)³`

* `sharp_sharp_inv`: `Φ ↦ Φ♯` (at `π`) is inverted by `♯` at `π⁻¹`.
* **`iterate_act`**: `Ã(π)³ Φ = |π|_{S_f}^{-3} • Φ♯` as genuine sections (MATH2 §4.4, last display).
* `Lam_sharp`: `Lam Φ♯ c μ = |π|³ · Lam Φ c (π³ μ)`; `mCoeff_sharp`: `m_{Φ♯} = |π|³ m_Φ`.
* `sharp_zero_one`: `Φ♯_s(0, 1) = |π|^{3s} Φ_s(0, 1)`.
-/

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.B7 ArtinKP.E

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

theorem sharp_zero_one {π : F} (hπ : π ≠ 0) (s : ℂ) :
    Φ.sharp hG π hπ s 0 1 = ((absS 𝔪 π : ℝ) : ℂ) ^ (3 * s) * Φ s 0 1 := by
  rw [GSection.sharp_apply]
  have h := Φ.cube s π hπ 0 (1 / π ^ 3)
  have e : π ^ 3 * (1 / π ^ 3) = 1 := by field_simp
  rw [mul_zero, e] at h
  rw [h, ← mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne')]
  simp

lemma cpow_pos_eq {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

/-- The three symbol factors of `A(β)³` multiply to `1`. -/
lemma tf_three (β : F) (hβ : β ≠ 0) (c d : F) :
    tf ι P 𝔪 β c d * (tf ι P 𝔪 β (β ^ 2 * c) (β * d)
      * tf ι P 𝔪 β (β ^ 2 * (β ^ 2 * c)) (β * (β * d))) = 1 := by
  by_cases hc : c = 0
  · subst hc
    simp only [mul_zero, tf, if_true]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [brk_mul_left _ hβ (mul_ne_zero hβ hd), brk_mul_left _ hβ hd, brk_self]
      have h3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) d β
      linear_combination h3
  · have h2 : β ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) hc
    have h4 : β ^ 2 * (β ^ 2 * c) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) h2
    rw [tf, if_neg hc, tf, if_neg h2, tf, if_neg h4,
      brk_mul_left _ (pow_ne_zero 2 hβ) h2, brk_mul_left _ (pow_ne_zero 2 hβ) hc, pow_two β,
      brk_mul_left _ hβ hβ, brk_self]
    have h3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) c β
    linear_combination (brk ι P 𝔪 c β ^ 3 + 1) * h3

include hz6 in
/-- **`Ã(π)³ Φ = |π|_{S_f}^{-3} Φ♯`.** -/
theorem iterate_act {π : SInt 𝔪} (hπ : (π : F) ≠ 0) :
    ((kubota (ι := ι) (P := P) hG hz6).act π)^[3] Φ
      = (((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3) • Φ.sharp hG (π : F) hπ := by
  have hact : ∀ Ψ : GSection ι P 𝔪, (kubota (ι := ι) (P := P) hG hz6).act π Ψ
      = Ψ.torusT hG (π : F) hπ := fun Ψ => by
    rw [kubota_act, S2.actR, dif_neg hπ]
  have ha0 : ((absS 𝔪 (π : F) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne'
  ext s c d
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, hact]
  rw [GSection.smul_apply, GSection.sharp_apply, GSection.torusT_apply, GSection.torusT_apply,
    GSection.torusT_apply]
  have e1 : (π : F) ^ 2 * ((π : F) ^ 2 * ((π : F) ^ 2 * c)) = ((π : F) ^ 2) ^ 3 * c := by ring
  have e2 : (π : F) * ((π : F) * ((π : F) * d)) = ((π : F) ^ 2) ^ 3 * (d / (π : F) ^ 3) := by
    field_simp
  rw [e1, e2, Φ.cube s ((π : F) ^ 2) (pow_ne_zero 2 hπ), absS_pow]
  have key := tf_three (ι := ι) (P := P) (𝔪 := 𝔪) (π : F) hπ c d
  have hA : ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1) * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
      * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
        * (((absS 𝔪 (π : F) ^ 2 : ℝ) : ℂ)) ^ (-(3 * s))))
      = ((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3 := by
    have hpos := absS_pos (𝔪 := 𝔪) hπ
    have hx2 : (0 : ℝ) < absS 𝔪 (π : F) ^ 2 := by positivity
    have e3 : ((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3
        = Complex.exp ((Real.log (absS 𝔪 (π : F)) : ℂ) * (-3)) := by
      rw [← cpow_pos_eq hpos, show (-3 : ℂ) = -((3 : ℕ) : ℂ) by norm_num, Complex.cpow_neg,
        Complex.cpow_natCast, inv_pow]
    rw [e3, cpow_pos_eq hpos, cpow_pos_eq hx2, Real.log_pow, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination
    (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1) * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
      * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
        * (((absS 𝔪 (π : F) ^ 2 : ℝ) : ℂ)) ^ (-(3 * s)))) * Φ s c (d / (π : F) ^ 3)) * key
      + Φ s c (d / (π : F) ^ 3) * hA

include hz6 in
/-- **`Lam Φ♯ c μ = |π|³ · Lam Φ c (π³ μ)`** (MATH2 (J2)). -/
theorem Lam_sharp {π : SInt 𝔪} (hπ : (π : F) ≠ 0) {c : SInt 𝔪} (hc : c ≠ 0) (μ : SInt 𝔪)
    {s : ℂ} (hs : 2 < s.re) :
    (kubota hG hz6).Lam (Φ.sharp hG (π : F) hπ) c μ s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * (kubota hG hz6).Lam Φ c (π ^ 3 * μ) s := by
  have hπ' : π ≠ 0 := fun h => hπ (by rw [h]; rfl)
  have h1 := (kubota (ι := ι) (P := P) hG hz6).Lam_iter_three Φ hπ' c μ hc hs
  rw [iterate_act hG hz6 Φ hπ, kubota_Lam, S2.LamR, G1.Lam_smul] at h1
  have ha0 : ((absS 𝔪 (π : F) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne'
  rw [← h1, kubota_Lam, S2.LamR, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, one_mul]

include hz6 in
/-- `m_{Φ♯} = |π|³ · m_Φ`. -/
theorem mCoeff_sharp {π : SInt 𝔪} (hπ : (π : F) ≠ 0) {s : ℂ} (hs : 2 < s.re) :
    mCoeff hG hz6 (Φ.sharp hG (π : F) hπ) s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * mCoeff hG hz6 Φ s := by
  have key : ∀ a : Cls (SInt 𝔪), kTerm hG hz6 (Φ.sharp hG (π : F) hπ) 0 a s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * kTerm hG hz6 Φ 0 a s := fun a => by
    have h := Lam_sharp hG hz6 Φ hπ (rp_ne_zero a.2) 0 hs
    rw [kubota_Lam, kubota_Lam, mul_zero] at h
    rw [kTerm, kTerm, h]
    ring
  rw [mCoeff, mCoeff, aCoeff, aCoeff, tsum_congr key, tsum_mul_left]
  ring

end

end ArtinKP.F
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

lemma alg_const (A Ai Qs p3s n ni p q V k m φ X Y JR : ℂ) (hD : 1 - q ^ 2 * Qs ≠ 0) (hA : A ≠ 0)
    (f4 : A * Qs * p3s = Ai) (hn : n ^ 3 * ni ^ 3 = 1) (hq : q ^ 3 = n ^ 3 * p ^ 3)
    (E : A * (q ^ 3 * Qs * (n ^ 3 * V * (p3s * φ * X + k * (p ^ 3 * m) * Y))
        + (1 - q ^ 2 * Qs) * JR)
      = n ^ 3 * (q ^ 3 * (V * (φ * (X * Ai) + k * m * (Y * (A * ni ^ 3)))))) :
    JR = n ^ 3 * V * (k * (p ^ 3 * m) * ((1 - q ^ 3 * Qs) / (1 - q ^ 2 * Qs)) * Y) := by
  apply mul_left_cancel₀ (mul_ne_zero hA hD)
  have hr : (1 - q ^ 2 * Qs) * ((1 - q ^ 3 * Qs) / (1 - q ^ 2 * Qs)) = 1 - q ^ 3 * Qs :=
    mul_div_cancel₀ _ hD
  linear_combination E - n ^ 3 * q ^ 3 * V * φ * X * f4 + V * k * m * Y * A * q ^ 3 * hn
    + V * k * m * Y * A * hq - A * n ^ 3 * V * k * p ^ 3 * m * Y * hr

section general

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- Translations by `r` with `Φ_s(c, d + c r) = Φ_s(c, d)` lie in the lattice of the stabilizer. -/
lemma mem_latN_stabGroup_of_unip (Φ : GSection ι P 𝔪) {x : InfinitePlace F → ℂ}
    (hx : x ∈ latO F) {r : F} (hxr : x = emb r)
    (hunip : ∀ (s : ℂ) (c d : F), Φ s c (d + c * r) = Φ s c d) :
    x ∈ latN (stabGroup (Φ.twist hG hz6)) := by
  obtain ⟨β, -, hβ⟩ := hx
  have hβr : ((β : 𝓞 F) : F) = r := by
    have h0 : emb (((β : 𝓞 F) : F) - r) = 0 := by
      rw [map_sub, sub_eq_zero, ← hxr]
      exact hβ
    exact sub_eq_zero.mp (emb_eq_zero h0)
  refine ⟨β, ?_, hβ⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [intMat_nInt, TSection.mem_stab]
  intro s p
  rw [GSection.twist_apply, GSection.twist_apply, kappaRow_n ι P hG hz6, act_nMat_c,
    act_nMat_d]
  have h3 := hunip s (p.c : F) (p.d : F)
  push_cast
  rw [add_comm]
  rw [show (algebraMap (𝓞 F) F) β = r from hβr, h3]

end general

/-! ### Powers of positive reals -/

lemma inv_pow_three_eq {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ)⁻¹ ^ 3 = Complex.exp ((Real.log x : ℂ) * (-3)) := by
  rw [← cpow_pos_eq hx, show (-3 : ℂ) = -((3 : ℕ) : ℂ) by norm_num, Complex.cpow_neg,
    Complex.cpow_natCast, inv_pow]

lemma cpow_fact1 {n p : ℝ} (hn : 0 < n) (hp : 0 < p) (s : ℂ) :
    ((n : ℝ) : ℂ) ^ (3 * s / 2) * (((n * p : ℝ) : ℂ) ^ (-s)) ^ 3 * ((p : ℝ) : ℂ) ^ (3 * s)
      = ((n : ℝ) : ℂ) ^ (3 * (-s) / 2) := by
  rw [cpow_pos_eq hn, cpow_pos_eq (mul_pos hn hp), cpow_pos_eq hp, cpow_pos_eq hn,
    ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
    Real.log_mul hn.ne' hp.ne']
  congr 1
  push_cast
  ring

lemma cpow_fact2 {n : ℝ} (hn : 0 < n) (s : ℂ) :
    ((n : ℝ) : ℂ) ^ (3 * s / 2) * ((n : ℝ) : ℂ)⁻¹ ^ 3 = ((n : ℝ) : ℂ) ^ (3 * (-(2 - s)) / 2) := by
  rw [inv_pow_three_eq hn, cpow_pos_eq hn, cpow_pos_eq hn, ← Complex.exp_add]
  congr 1
  ring

lemma prod_div_cpow (vv : InfinitePlace F → ℝ) (hvv : ∀ w, 0 < vv w) {a : F} (ha : a ≠ 0)
    (z : ℂ) :
    (((∏ w, vv w / ‖w.embedding a‖ : ℝ)) : ℂ) ^ z
      = ((∏ w, vv w : ℝ) : ℂ) ^ z * ((FB.Nh a : ℝ) : ℂ) ^ (-z) := by
  have e : ∏ w, vv w / ‖w.embedding a‖ = (∏ w, vv w) / FB.Nh a := by
    rw [Finset.prod_div_distrib]; rfl
  have h1 : 0 < ∏ w, vv w := Finset.prod_pos fun w _ => hvv w
  have h2 := FB.Nh_pos ha
  rw [e, cpow_pos_eq (div_pos h1 h2), cpow_pos_eq h1, cpow_pos_eq h2,
    Real.log_div h1.ne' h2.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include h in
lemma absNorm_eq_mul (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm v.asIdeal : ℂ)
      = ((Ninf (g.gen v.asIdeal : F) * absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) := by
  rw [FB.Ninf_mul_absS_gen h g h𝔪, card_quot_gen h g, Complex.ofReal_natCast]

include h in
lemma one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  exact_mod_cast this

include hG hz6 in
/-- `a·Λ_M` consists of periods of `Φ♯` (`a = π³`, `M` a depth of unipotent invariance of `Φ`). -/
lemma scaleLat_le_stab_sharp {π : F} (hπ : π ≠ 0) {M : ℤ}
    (hunip : ∀ b : F, Small 𝔪 M b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d)
    (hA : scaleLat (π ^ 3) (transLat 𝔪 M) ≤ latO F) :
    scaleLat (π ^ 3) (transLat 𝔪 M) ≤ latN (stabGroup ((Φ.sharp hG π hπ).twist hG hz6)) := by
  intro x hx
  obtain ⟨y, ⟨b, hb, rfl⟩, rfl⟩ := hx
  refine mem_latN_stabGroup_of_unip hG hz6 _ (hA ⟨_, ⟨b, hb, rfl⟩, rfl⟩) (r := π ^ 3 * (b : F))
    (by rw [emb_mul]; rfl) fun s c d => ?_
  rw [GSection.sharp_apply, GSection.sharp_apply]
  have e : (d + c * (π ^ 3 * (b : F))) / π ^ 3 = d / π ^ 3 + c * (b : F) := by
    field_simp
  rw [e, hunip _ hb]

open Classical in
include hG hz6 in
/-- **The constant term of `E_{Φ♯ρ_∞}` over the cell `π³D`.** -/
theorem integral_restrict_scale_oai {Tr : Finset (SInt 𝔪)} (hT : IsU hG hz6 h g Φ Tr) {M K : ℤ}
    (hM : 0 ≤ M) (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M)
    (hK : Small 𝔪 (-K) ((g.gen v.asIdeal : F) ^ 3)) (hKM : K ≤ M)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {s : ℂ} (hs : 2 < s.re)
    (hd : 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ 2 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3 ≠ 0)
    (vv : InfinitePlace F → ℝ)
    (hvv : ∀ w, 0 < vv w) :
    ∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
        eis (TSection.restrict v (not_le_of_good h)
          ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s
          (X.mk x vv hvv)
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 * (((volume D).toReal : ℝ) : ℂ)
        * (T.kap 𝔪 0 * (((absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 * mCoeff hG hz6 Φ s)
          * ((1 - (Ideal.absNorm v.asIdeal : ℂ) ^ 3 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3)
            / (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ 2 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3))
          * ((∏ w, vv w : ℝ) : ℂ) ^ (2 - s)) := by
  have h𝔪 := hG.ne_bot
  have hπ : (g.gen v.asIdeal : F) ≠ 0 := gen_coe_ne_zero h g
  have hπ3 : (g.gen v.asIdeal : F) ^ 3 ≠ 0 := pow_ne_zero 3 hπ
  have hnpos : 0 < Ninf (g.gen v.asIdeal : F) := Ninf_pos hπ
  have hppos : 0 < absS 𝔪 (g.gen v.asIdeal : F) := absS_pos hπ
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by have := one_lt_absNorm h; omega
  -- Proposition 5.4 at frequency 0
  have E0 := U_coeff hG hz6 h g Φ hT hM 0 hV (fun t _ => by
    have e : (((0 : SInt 𝔪) : F)) * (t : F) / (g.gen v.asIdeal : F) ^ 3 = 0 := by
      rw [show (((0 : SInt 𝔪) : F)) = 0 from rfl, zero_mul, zero_div]
    rw [e]; exact Small.zero) hD hb hs vv hvv
  have ez : (((0 : SInt 𝔪) : F)) / (g.gen v.asIdeal : F) ^ 3 = 0 := by
    rw [show (((0 : SInt 𝔪) : F)) = 0 from rfl, zero_div]
  rw [ez, show (((0 : SInt 𝔪) : F)) = 0 from rfl] at E0
  simp only [chiInf_zero, mul_one, dvd_zero, if_true] at E0
  -- the admissible lattice `a·Λ_M`
  have ecast : (((g.gen v.asIdeal ^ 3 : SInt 𝔪)) : F) = (g.gen v.asIdeal : F) ^ 3 := rfl
  have hAdm : Adm (scaleLat ((g.gen v.asIdeal : F) ^ 3) (transLat 𝔪 M)) := by
    have := adm_scaleLat h𝔪 (g.gen v.asIdeal ^ 3) (by rw [ecast]; exact hπ3) (K := K) (M := M)
      (by rw [ecast]; exact hK) hKM
    rwa [ecast] at this
  obtain ⟨n', hn'⟩ := exists_bdd_scaleSet ((g.gen v.asIdeal : F) ^ 3) hb
  obtain ⟨M', hM', hV'⟩ := exists_validDepth_nonneg hG
    (Φ.sharp hG (g.gen v.asIdeal : F) hπ) (((0 : SInt 𝔪)) : F)
  have hJs := const_adm hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) hM' hV' hAdm
    (pcell_scale hπ3 hD) hn' (inv_stabGroup _)
    (scaleLat_le_stab_sharp hG hz6 Φ hπ hV.unip hAdm.le) hs vv hvv
  have hJΦ := const_adm hG hz6 Φ hM hV (adm_transLat h𝔪 hM) hD hb (inv_stabGroup _)
    (transLat_le_latN_stabGroup hG hz6 Φ hM hV.unip) hs
    (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
    (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ3)))
  rw [hJs, hJΦ] at E0
  have hNa : ((Ninf ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ)
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 := by
    rw [pow_succ, pow_succ, pow_one, Ninf_mul, Ninf_mul]
    push_cast
    ring
  rw [volume_scaleSet hπ3 hD.meas, hNa, sharp_zero_one, mCoeff_sharp hG hz6 Φ hπ hs,
    prod_div_cpow vv hvv hπ3, prod_div_cpow vv hvv hπ3, FB.Nh_pi_cube_cpow hπ,
    FB.Nh_pi_cube_cpow hπ, ← cpow_fact2 hnpos s, ← FB.q_cpow_three hq0 s,
    ← FB.q_cpow_two hq0 s] at E0
  have f4 := cpow_fact1 hnpos hppos s
  rw [← absNorm_eq_mul h g h𝔪] at f4
  have hn3 : ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3
      * ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ)⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnpos.ne'), one_pow]
  have hq3 : (Ideal.absNorm v.asIdeal : ℂ) ^ 3
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3
        * ((absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 := by
    rw [absNorm_eq_mul h g h𝔪]; push_cast; ring
  have hA : ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) ≠ 0 := by
    rw [cpow_pos_eq hnpos]; exact Complex.exp_ne_zero _
  refine alg_const _ _ _ _ _ _ _ _ _ _ _ (Φ s 0 1) (((∏ w, vv w : ℝ) : ℂ) ^ s) _ _ hd hA f4 hn3
    hq3 ?_
  linear_combination E0

end gen

end

end ArtinKP.F
end

theorem solution.{u_1} : type_of% @ArtinKP.F.integral_restrict_scale_oai.{u_1} := @ArtinKP.F.integral_restrict_scale_oai.{u_1}
