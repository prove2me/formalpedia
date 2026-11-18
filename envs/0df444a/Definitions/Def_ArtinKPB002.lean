-- Prove2me | Definitions.Def_ArtinKPB002
-- name    : ArtinKPB002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:25:15.885207+00:00
-- url     : https://prove2.me/theorems/20ce7fda-d360-4f56-96ef-65193971fb41
-- title:
--   Definitions bundle ArtinKPB002 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 262 declarations of that development: 67 definitions, 7 inductive types or structures, 10 instances and 178 theorems. The definitions and types are `ArtinKP.B.IdxI`, `ArtinKP.B.eInf`, `ArtinKP.B.embR`, `ArtinKP.B.extOf`, `ArtinKP.B.kTerm`, `ArtinKP.B.latR`, `ArtinKP.B.latREquiv`, `ArtinKP.B.nrmR`, `ArtinKP.B.psiS`, `ArtinKP.B.sec`, `ArtinKP.B.thetaEquiv`, `ArtinKP.B.thetaFun`, `ArtinKP.B.transLat`, `ArtinKP.B1.IsSInt`, `ArtinKP.B1.IsSUnit`, `ArtinKP.B1.SIntRing`, `ArtinKP.B1.SPair`, `ArtinKP.B1.emb`, `ArtinKP.B7.AddData`, `ArtinKP.B7.AddData.ψ`, `ArtinKP.B7.CubicSymbol`, `ArtinKP.B7.gauss`, `ArtinKP.B7.rep`, `ArtinKP.B7.rsum`, `ArtinKP.B7.sAdd`, `ArtinKP.E.Cls`, `ArtinKP.E.nrm`, `ArtinKP.E.rp`, `ArtinKP.K.archChar`, `ArtinKP.RF.dep`, `ArtinKP.RO.SOf`, `ArtinKP.RO.sIntEquiv`, `ArtinKP.S.GSection`, `ArtinKP.S.GSection.nT`, `ArtinKP.S.GSection.smulFun`, `ArtinKP.S.GSection.twist`, `ArtinKP.S.InI`, `ArtinKP.S.IsK`, `ArtinKP.S.Row`, `ArtinKP.S.Row.act` and 34 more.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `C0.C0R_P`, `KP.A_Kubota`, `KP.A_Pkg`, `KP.A_Residue`, `KP.B1_Bridge`, `KP.B1_Lattice`, `KP.B1_Pairs`, `KP.B1_Rescale`, `KP.B7_Gauss`, `KP.B7_Link`, `KP.B7_Sum`, `KP.B_FourArch`, `KP.B_FourCoeff`, `KP.B_FourIndex`, `KP.B_Kub`, `KP.B_Norm`, `KP.E_Series`, `KP.K_Char`, `KP.K_Jacquet`, `KP.RF_SNorm`, `KP.RO_Ring`, `KP.S2_Index`, `KP.S2_Kubota`, `KP.S2_Lattice`, `KP.S2_Symbol`, `KP.S_Basic`, `KP.S_Genuine`, `KP.S_Jacquet`, `KP.S_Level`, `KP.S_Ops`, `KP.S_Twisted`, `KP.X_Disjoint`, `T12.C3B_Norm`, `T12.C3I_Add`, `T12.L2B_Quot`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHecke`, `Def_ArtinHeckeLocalCoeff`, `Def_ArtinHeckePoissonLocal`, `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule`, `Def_NumberField_PlaceDecompositionAction` and `Def_NumberField_TateGlobalZeta`; the bundle `ArtinKPB001` of this split; the published statement `ArtinKP.S2.cubicExt_eq_zero_iff`.
--
--   **Imported by** (directly, in this split): the bundles `ArtinKPB003` and `ArtinKPB004`; the statement `ArtinKP.B.summable_kTerm_of_two_lt_re`; the proofs of `ArtinKP.B.summable_kTerm_of_two_lt_re` and `ArtinKP.N2.integrable_lift_pou`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

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
import Definitions.Def_ArtinKPB001
import Theorems.Thm_ArtinKP_S2_cubicExt_eq_zero_iff

section
-- module Solutions.Artin.C0.C0R_P
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace C0R

variable {F : Type*} [Field F] [NumberField F]

/-- An ideal all of whose prime divisors contain `𝔪` becomes the unit ideal in `R`. -/
theorem map_eq_top_of_primes (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (J : Ideal (𝓞 F))
    (hprimes : ∀ Q : Ideal (𝓞 F), Q.IsPrime → J ≤ Q → 𝔪 ≤ Q) :
    J.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
  have hQ : (M.comap (algebraMap (𝓞 F) (SInt 𝔪))).IsPrime := Ideal.comap_isPrime _ M
  have hJQ : J ≤ M.comap (algebraMap (𝓞 F) (SInt 𝔪)) := Ideal.map_le_iff_le_comap.1 hJM
  have h𝔪Q := hprimes _ hQ hJQ
  have : 𝔪.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ M :=
    Ideal.map_le_iff_le_comap.2 h𝔪Q
  rw [map_self_eq_top 𝔪 h𝔪, top_le_iff] at this
  exact hM.ne_top this

end C0R

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.A_Pkg
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace CubicPkg

variable (P : CubicPkg F)

/-! ### The `S`-part -/

/-- (A4) cubes pair trivially. -/
theorem HS_pow_three_left (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 (a ^ 3) b = 1 := by
  rw [map_pow, MonoidHom.pow_apply, root_pow_three]

/-- `S`-units pair trivially: `(u, u')_S = 1`. -/
theorem HS_unit {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal) (u u' : Fˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (u : F) = 1)
    (hu' : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (u' : F) = 1) :
    P.HS 𝔪 u u' = 1 := by
  have := P.HS_mul_prod' h𝔪 h3 u u' ∅ (by simp) fun v hv _ => ⟨hu v hv, hu' v hv⟩
  simpa using this

/-! ### Deep units -/

/-- (A4) deep levels exist (local constancy of the Hilbert symbols at the places of `S`). -/
theorem exists_isDeepLevel {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 1 ≤ N ∧ P.IsDeepLevel 𝔪 N := by
  classical
  choose Nv hNv using P.deep
  refine ⟨(sFin 𝔪).sup Nv + 1, by omega, fun v hv a b hb => ?_⟩
  refine hNv v a b (hb.trans ?_)
  rw [WithZero.exp_le_exp]
  have : Nv v ≤ (sFin 𝔪).sup Nv := Finset.le_sup ((mem_sFin h𝔪 v).mpr hv)
  omega

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Residue
/-!
# WP-A: the exterior cubic residue symbol and reciprocity

* `Good 𝔪`: the standing hypotheses on the modulus (`𝔪 ≠ ⊥`, every prime over `6` divides `𝔪`,
  `R = SInt 𝔪` is a PID in the form "every extended ideal is principal");
  `exists_cutoff_good` gives it from `SmallPrimesDvd N₀ 𝔪`.
* `cubicExt ι 𝔪 d c = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` in terms of the goal's
  `sexticResidueSymbol`.
* `cubicExt_eq_prod`: `(d/c) = ι ∏_v (d, c)_v` over the exterior places dividing `c`.
* `cubicExt_reciprocity` (A3): `(d/c) = (c/d) · (c, d)_S` — with the orientation of `CubicPkg`
  the sign in MATH.md (A3) is `+1`.
* unit laws, multiplicativity, dependence on `d mod c` only.

The first section is a universe-polymorphic copy of `C0Y.val_generator`, `C0Y.sextic_spec`
(`Solutions/Artin/C0/C0YR.lean`, stated there for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

theorem iota3_ne_zero (ι : F →+* ℂ) (z : rootsOfUnity 3 F) : iota3 ι z ≠ 0 := by
  intro h0
  have := iota3_pow_three ι z
  rw [h0] at this
  norm_num at this

variable (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)}

open CubicPkg in
/-- (A3) **cubic reciprocity** for coprime `c, d ∈ R`: `(d/c) = (c/d) · (c, d)_S`. -/
theorem cubicExt_reciprocity (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (c d : SInt 𝔪) (cu du : Fˣ) (hcu : (cu : F) = c)
    (hdu : (du : F) = d)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
      v.valuation F (c : F) = 1 ∨ v.valuation F (d : F) = 1) :
    cubicExt ι 𝔪 d c = cubicExt ι 𝔪 c d * iota3 ι (P.HS 𝔪 cu du) := by
  classical
  have hc0 : (c : F) ≠ 0 := hcu ▸ cu.ne_zero
  have hd0 : (d : F) ≠ 0 := hdu ▸ du.ne_zero
  have hA := cubicExt_eq_prod ι P hG hz6 c d cu du hcu hdu (extSupp 𝔪 (c : F))
    (fun v hv => ⟨((mem_extSupp hc0 v).mp hv).1,
      (hcop v ((mem_extSupp hc0 v).mp hv).1).resolve_left ((mem_extSupp hc0 v).mp hv).2⟩)
    subset_rfl
  have hB := cubicExt_eq_prod ι P hG hz6 d c du cu hdu hcu (extSupp 𝔪 (d : F))
    (fun v hv => ⟨((mem_extSupp hd0 v).mp hv).1,
      (hcop v ((mem_extSupp hd0 v).mp hv).1).resolve_right ((mem_extSupp hd0 v).mp hv).2⟩)
    subset_rfl
  have hdisj : Disjoint (extSupp 𝔪 (c : F)) (extSupp 𝔪 (d : F)) := by
    rw [Finset.disjoint_left]
    intro v hc hd
    obtain ⟨hext, h1⟩ := (mem_extSupp hc0 v).mp hc
    obtain ⟨-, h2⟩ := (mem_extSupp hd0 v).mp hd
    rcases hcop v hext with h | h
    · exact h1 h
    · exact h2 h
  have hprod := P.HS_mul_prod' hG.ne_bot hG.three cu du (extSupp 𝔪 (c : F) ∪ extSupp 𝔪 (d : F))
    (fun v hv => by
      rcases Finset.mem_union.mp hv with h | h <;> exact not_le_of_mem_extSupp h)
    (fun v hv hvT => by
      rw [Finset.mem_union, not_or, mem_extSupp hc0, mem_extSupp hd0] at hvT
      rw [hcu, hdu]
      exact ⟨by_contra fun h => hvT.1 ⟨hv, h⟩, by_contra fun h => hvT.2 ⟨hv, h⟩⟩)
  rw [Finset.prod_union hdisj] at hprod
  have hinv : ∏ v ∈ extSupp 𝔪 (c : F), P.hv v cu du
      = (∏ v ∈ extSupp 𝔪 (c : F), P.hv v du cu)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => P.skew' v cu du
  rw [hinv] at hprod
  have key : ∏ v ∈ extSupp 𝔪 (c : F), P.hv v du cu
      = (∏ v ∈ extSupp 𝔪 (d : F), P.hv v cu du) * P.HS 𝔪 cu du := by
    calc ∏ v ∈ extSupp 𝔪 (c : F), P.hv v du cu
        = (∏ v ∈ extSupp 𝔪 (c : F), P.hv v du cu) * (P.HS 𝔪 cu du *
            ((∏ v ∈ extSupp 𝔪 (c : F), P.hv v du cu)⁻¹ *
              ∏ v ∈ extSupp 𝔪 (d : F), P.hv v cu du)) := by rw [hprod, mul_one]
      _ = _ := by rw [mul_left_comm (P.HS 𝔪 cu du), mul_inv_cancel_left, mul_comm]
  rw [hA, hB, key, map_mul]

/-- (A3) **unit law**: `(ε/c) = (c, ε)_S` for an `S`-unit `ε`. -/
theorem cubicExt_unit_left (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (c ε : SInt 𝔪) (cu εu : Fˣ) (hcu : (cu : F) = c)
    (hεu : (εu : F) = ε)
    (hε : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (ε : F) = 1) :
    cubicExt ι 𝔪 ε c = iota3 ι (P.HS 𝔪 cu εu) := by
  rw [cubicExt_reciprocity ι P hG hz6 c ε cu εu hcu hεu fun v hv => Or.inr (hε v hv),
    cubicExt_of_unit_right ι c ε hε, one_mul]

open CubicPkg in
/-- Multiplicativity in the numerator. -/
theorem cubicExt_mul_left (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (c d d' : SInt 𝔪) (hc : c ≠ 0)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) ≠ 1 →
      v.valuation F (d : F) = 1)
    (hd' : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) ≠ 1 →
      v.valuation F (d' : F) = 1) :
    cubicExt ι 𝔪 (d * d') c = cubicExt ι 𝔪 d c * cubicExt ι 𝔪 d' c := by
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  by_cases hE : extSupp 𝔪 (c : F) = ∅
  · simp [cubicExt, hE]
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨hext₀, hne₀⟩ := (mem_extSupp hc0 v₀).mp hv₀
  have hd0 : (d : F) ≠ 0 := ne_zero_of_val_eq_one _ (hd v₀ hext₀ hne₀)
  have hd0' : (d' : F) ≠ 0 := ne_zero_of_val_eq_one _ (hd' v₀ hext₀ hne₀)
  have h1 := cubicExt_eq_prod ι P hG hz6 c d (Units.mk0 _ hc0) (Units.mk0 _ hd0) rfl rfl
    (extSupp 𝔪 (c : F)) (fun v hv => ⟨((mem_extSupp hc0 v).mp hv).1,
      hd v ((mem_extSupp hc0 v).mp hv).1 ((mem_extSupp hc0 v).mp hv).2⟩) subset_rfl
  have h2 := cubicExt_eq_prod ι P hG hz6 c d' (Units.mk0 _ hc0) (Units.mk0 _ hd0') rfl rfl
    (extSupp 𝔪 (c : F)) (fun v hv => ⟨((mem_extSupp hc0 v).mp hv).1,
      hd' v ((mem_extSupp hc0 v).mp hv).1 ((mem_extSupp hc0 v).mp hv).2⟩) subset_rfl
  have h3 := cubicExt_eq_prod ι P hG hz6 c (d * d') (Units.mk0 _ hc0)
    (Units.mk0 _ hd0 * Units.mk0 _ hd0') rfl (by simp)
    (extSupp 𝔪 (c : F)) (fun v hv => ⟨((mem_extSupp hc0 v).mp hv).1, by
      rw [Subalgebra.coe_mul, map_mul, hd v ((mem_extSupp hc0 v).mp hv).1
        ((mem_extSupp hc0 v).mp hv).2, hd' v ((mem_extSupp hc0 v).mp hv).1
        ((mem_extSupp hc0 v).mp hv).2, one_mul]⟩) subset_rfl
  rw [h1, h2, h3, ← map_mul, ← Finset.prod_mul_distrib]
  simp only [map_mul, MonoidHom.mul_apply]

open CubicPkg in
/-- Multiplicativity in the denominator. -/
theorem cubicExt_mul_right (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (c c' d : SInt 𝔪) (hc : c ≠ 0) (hc' : c' ≠ 0) (hd0 : d ≠ 0)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c : F) ≠ 1 →
      v.valuation F (d : F) = 1)
    (hd' : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (c' : F) ≠ 1 →
      v.valuation F (d : F) = 1) :
    cubicExt ι 𝔪 d (c * c') = cubicExt ι 𝔪 d c * cubicExt ι 𝔪 d c' := by
  classical
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hc0' : (c' : F) ≠ 0 := fun h => hc' (Subtype.ext h)
  have hdF : (d : F) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hcc0 : ((c * c' : SInt 𝔪) : F) ≠ 0 := by
    rw [Subalgebra.coe_mul]; exact mul_ne_zero hc0 hc0'
  set T := extSupp 𝔪 (c : F) ∪ extSupp 𝔪 (c' : F) with hTdef
  have hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal ∧ v.valuation F (d : F) = 1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact ⟨((mem_extSupp hc0 v).mp h).1,
        hd v ((mem_extSupp hc0 v).mp h).1 ((mem_extSupp hc0 v).mp h).2⟩
    · exact ⟨((mem_extSupp hc0' v).mp h).1,
        hd' v ((mem_extSupp hc0' v).mp h).1 ((mem_extSupp hc0' v).mp h).2⟩
  have hsub : extSupp 𝔪 ((c * c' : SInt 𝔪) : F) ⊆ T := by
    intro v hv
    obtain ⟨hext, hne⟩ := (mem_extSupp hcc0 v).mp hv
    rw [hTdef, Finset.mem_union, mem_extSupp hc0, mem_extSupp hc0']
    by_contra hcon
    rw [not_or] at hcon
    apply hne
    have e1 : v.valuation F (c : F) = 1 := by_contra fun h => hcon.1 ⟨hext, h⟩
    have e2 : v.valuation F (c' : F) = 1 := by_contra fun h => hcon.2 ⟨hext, h⟩
    rw [Subalgebra.coe_mul, map_mul, e1, e2, one_mul]
  have h1 := cubicExt_eq_prod ι P hG hz6 c d (Units.mk0 _ hc0) (Units.mk0 _ hdF) rfl rfl T hT
    Finset.subset_union_left
  have h2 := cubicExt_eq_prod ι P hG hz6 c' d (Units.mk0 _ hc0') (Units.mk0 _ hdF) rfl rfl T hT
    Finset.subset_union_right
  have h3 := cubicExt_eq_prod ι P hG hz6 (c * c') d (Units.mk0 _ hc0 * Units.mk0 _ hc0')
    (Units.mk0 _ hdF) (by simp) rfl T hT hsub
  rw [h1, h2, h3, ← map_mul, ← Finset.prod_mul_distrib]
  simp only [map_mul]

/-- `(d/c)` depends only on `d` modulo `c`. -/
theorem cubicExt_congr (hG : Good 𝔪) (c d d' : SInt 𝔪) (hc : c ≠ 0)
    (h : d - d' ∈ Ideal.span {c}) : cubicExt ι 𝔪 d c = cubicExt ι 𝔪 d' c := by
  have hc0 : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨hext, hne⟩ := (CubicPkg.mem_extSupp hc0 v).mp hv
  obtain ⟨p, hp⟩ := (hG.principal v.asIdeal).principal
  have hp' : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := hp.symm
  have hcm : c ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    mem_map_of_val_lt_one v hext p hp' c (lt_of_le_of_ne (sInt_val_le_one c v hext) hne)
  have hmk : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d
      = Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d' := by
    rw [Ideal.Quotient.eq]
    exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hcm)) h
  have key : sexticResidueSymbol ι 𝔪 v.asIdeal d = sexticResidueSymbol ι 𝔪 v.asIdeal d' := by
    unfold sexticResidueSymbol
    rw [hmk]
  rw [key]

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Kubota
/-!
# WP-A: the Kubota symbol on `SL₂(R)`, `R = SInt 𝔪`

* `kappa ι 𝔪 γ = (d/c)⁻¹` (`1` if `c = 0`), with `(d/c) = cubicExt`.
* `sigmaS P 𝔪 g₁ g₂ = (X(g₁g₂)/X(g₁), X(g₁g₂)/X(g₂))_S` on rational matrices.
* `kappa_mul` (Lemma A5): `κ(γ₁γ₂) = κ(γ₁) κ(γ₂) σ_S(γ₁,γ₂)⁻¹`.

  **Orientation.**  With the symbols oriented by `CubicPkg.tame` the exponent is `ε = -1`
  (equivalently `ε = +1` for the opposite pairing `(b,a)_S`).  It is forced: for
  `γ₁ = diag(ε₁⁻¹, ε₁)` with an `S`-unit `ε₁`, and `c₂ ≠ 0`,
  `κ(γ₁γ₂)/κ(γ₂) = (ε₁/c₂)⁻¹ = (c₂, ε₁)_S⁻¹ = σ_S(γ₁, γ₂)⁻¹` by the unit law.
* `sigmaS_eq_one`: `σ_S(g₁, g₂) = 1` as soon as `a₂`, `d₁` and `d₃` lie in the radical of `(·,·)_S`.
* `Gamma 𝔪 𝔫`: the image in `SL₂(R)` of the principal congruence subgroup of `SL₂(𝓞 F)` of level
  `𝔫`; `kappa_mul_of_mem_Gamma` (Corollary A6): `κ` is multiplicative on `Γ(𝔫)` for `𝔫 ≤ 𝔪^N`,
  `N ≥ 1` any deep level of the package (`CubicPkg.IsDeepLevel`); `kappaHom`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-- `κ` takes values in the cube roots of unity. -/
theorem kappa_pow_three (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    kappa ι 𝔪 γ ^ 3 = 1 := by
  rw [kappa_eq_prod ι P hG hz6 γ _ (fun v hv => CubicPkg.not_le_of_mem_extSupp hv) subset_rfl]
  exact iota3_pow_three ι _

theorem kappa_ne_zero (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    kappa ι 𝔪 γ ≠ 0 := by
  intro h0
  have := kappa_pow_three ι P hG hz6 γ
  rw [h0] at this
  norm_num at this

/-! ### Triviality of `σ_S` on deep matrices -/

/-! ### The principal congruence subgroup and Corollary A6 -/

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.B1_Lattice
/-! # WP-B1, file 1: the lattice `𝓞_F² ⊂ ℂ^r × ℂ^r` and the Minkowski bound for the top height

`F` totally complex, `ι = InfinitePlace F`.  `emb : F →+ (ι → ℂ)` is the diagonal embedding,
`latE` the `ℝ`-basis of `ι → ℂ` given by an integral basis, `pairLattice` the `ℤ`-span of the
product basis of `(ι → ℂ) × (ι → ℂ)`; it is exactly `{(emb c, emb d) | c d ∈ 𝓞_F}` (`mem_pairLattice`).

**Lemma M** (`exists_integer_pair_pairHt_ge`): there is `c₀ > 0` such that for every `P ∈ X` some
nonzero pair `(c,d) ∈ 𝓞_F²` has `I_{(c,d)}(P) ≥ c₀`.  Proof: Minkowski's convex body theorem for the
body `{|c_w| ≤ λ/√v_w, |c_w x_w + d_w| ≤ λ√v_w}`, whose volume `(π²λ⁴)^r` does not depend on `P`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The diagonal embedding `F → ℂ^r`. -/
def emb : F →+ (InfinitePlace F → ℂ) where
  toFun a := fun w => w.embedding a
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] lemma emb_apply (a : F) (w : InfinitePlace F) : emb a w = w.embedding a := rfl

lemma emb_eq_zero {a : F} (h : emb a = 0) : a = 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := congrFun h w
  simpa using this

/-! ### The Minkowski body -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.X_Disjoint
/-! # WP-X, file 4: disjointness of cusp neighbourhoods

For two pairs `(c,d)`, `(c',d')` with `Δ = c d' - c' d ≠ 0`:
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`.  With the `S`-normalized heights
`ht^S_{(c,d)} = I_{(c,d)} / ∏_{v ∈ S} max(|c|_v, |d|_v)` and `Δ` an `S`-integer the product formula
gives `ht^S_{(c,d)} · ht^S_{(c',d')} ≤ 1`: the regions `{ht^S_{(c,d)} > 1}` of non-proportional
pairs are disjoint.  No reduction theory is used.
-/

open scoped MatrixGroups ComplexConjugate
open NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

namespace X

/-- The `S`-part of the norm of a pair: `∏_{v ∈ S} max(|c|_v, |d|_v)`. -/
def sNorm (S : Finset (FinitePlace F)) (c d : F) : ℝ := ∏ v ∈ S, max (v c) (v d)

open IsDedekindDomain in
/-- Elements of the ring of `S₀`-integers have absolute value `≤ 1` at the places outside `S₀`. -/
lemma finitePlace_le_one_of_mem_integer (S₀ : Set (HeightOneSpectrum (𝓞 F))) (x : S₀.integer F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S₀) : FinitePlace.mk v (x : F) ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def]
  have h : v.valuation F (x : F) ≤ 1 := x.property v hv
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr h

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Rescale
/-! # WP-B1, file 3: rescaling a pair of `S`-integers into `𝓞_F²` by an `S`-unit

For a finite set `S` of finite places there is `δ > 0` such that every nonzero pair `(c,d)` of
`S`-integers has an `S`-unit multiple `u·(c,d) ∈ 𝓞_F²` with `∏_{v∈S} max(|uc|_v, |ud|_v) ≥ δ`
(`exists_unit_rescale`).  Input: finiteness of the class group (`𝔭^h` is principal).
-/

open scoped ENNReal
open NumberField IsDedekindDomain

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- A generator of `𝔭^h`: an integer which is a non-unit exactly at the finite place `v`. -/
lemma exists_pi (v : FinitePlace F) : ∃ π : 𝓞 F, π ≠ 0 ∧ v (π : F) < 1 ∧
    ∀ v' : FinitePlace F, v' ≠ v → v' (π : F) = 1 := by
  classical
  set 𝔭 := v.maximalIdeal with h𝔭
  have hI0 : 𝔭.asIdeal ≠ 0 := 𝔭.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hprin : (𝔭.asIdeal ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem (mem_nonZeroDivisors_of_ne_zero hI0) h)]
    have : ClassGroup.mk0 ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero hI0⟩ ^ h = 1 := pow_card_eq_one
    rwa [← map_pow, SubmonoidClass.mk_pow] at this
  obtain ⟨π, hπ⟩ := hprin
  have hπmem : π ∈ 𝔭.asIdeal ^ h := by rw [hπ]; exact Submodule.mem_span_singleton_self π
  have hh0 : h ≠ 0 := Fintype.card_ne_zero
  refine ⟨π, ?_, ?_, ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI0 (by rw [hπ]; simp)
  · rw [← FinitePlace.mk_maximalIdeal v, FinitePlace.mk_apply]
    exact (FinitePlace.norm_lt_one_iff_mem _ _ _).mpr (Ideal.pow_le_self hh0 hπmem)
  · intro v' hv'
    rw [← FinitePlace.mk_maximalIdeal v', FinitePlace.mk_apply]
    refine (FinitePlace.norm_eq_one_iff_notMem _ _ _).mpr fun hmem => ?_
    have hle : 𝔭.asIdeal ^ h ≤ v'.maximalIdeal.asIdeal := by
      rw [hπ]; exact (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
    have hle2 : 𝔭.asIdeal ≤ v'.maximalIdeal.asIdeal := v'.maximalIdeal.isPrime.le_of_pow_le hle
    have heq : 𝔭.asIdeal = v'.maximalIdeal.asIdeal :=
      𝔭.isMaximal.eq_of_le v'.maximalIdeal.isPrime.ne_top hle2
    apply hv'
    rw [← FinitePlace.mk_maximalIdeal v', ← FinitePlace.mk_maximalIdeal v]
    exact congrArg FinitePlace.mk (HeightOneSpectrum.ext heq).symm

/-- An element of `F` which is integral at every finite place is an algebraic integer. -/
lemma exists_int_of_forall_le_one (x : F) (h : ∀ v : FinitePlace F, v x ≤ 1) :
    ∃ a : 𝓞 F, (a : F) = x := by
  have := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun 𝔭 => by
    have h1 := h (FinitePlace.mk 𝔭)
    rw [FinitePlace.mk_apply, FinitePlace.norm_embedding,
      NumberField.HeightOneSpectrum.adicAbv_def] at h1
    exact (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal 𝔭)).mp (by exact_mod_cast h1)
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

/-- **Rescaling into `𝓞_F²`.** -/
theorem exists_unit_rescale (S : Finset (FinitePlace F)) : ∃ δ : ℝ, 0 < δ ∧
    ∀ c d : F, (c ≠ 0 ∨ d ≠ 0) →
    (∀ v : FinitePlace F, v ∉ S → v c ≤ 1) → (∀ v : FinitePlace F, v ∉ S → v d ≤ 1) →
    ∃ u : F, u ≠ 0 ∧ (∀ v : FinitePlace F, v ∉ S → v u = 1) ∧
      (∃ c' d' : 𝓞 F, (c' : F) = u * c ∧ (d' : F) = u * d) ∧
      δ ≤ X.sNorm S (u * c) (u * d) := by
  classical
  choose π hπ0 hπlt hπone using fun v : FinitePlace F => exists_pi v
  have hπF : ∀ v, ((π v : 𝓞 F) : F) ≠ 0 := fun v => by simpa using hπ0 v
  have hπpos : ∀ v : FinitePlace F, 0 < v ((π v : 𝓞 F) : F) := fun v => FinitePlace.pos_iff.mpr (hπF v)
  refine ⟨∏ v ∈ S, v ((π v : 𝓞 F) : F), Finset.prod_pos fun v _ => hπpos v, ?_⟩
  intro c d hne hc hd
  set x : FinitePlace F → ℝ := fun v => max (v c) (v d) with hx
  have hxpos : ∀ v, 0 < x v := fun v => by
    rcases hne with h | h
    · exact lt_max_of_lt_left (FinitePlace.pos_iff.mpr h)
    · exact lt_max_of_lt_right (FinitePlace.pos_iff.mpr h)
  have hy : ∀ v : FinitePlace F, 1 < (v ((π v : 𝓞 F) : F))⁻¹ := fun v =>
    (one_lt_inv₀ (hπpos v)).mpr (hπlt v)
  choose n hn using fun v : FinitePlace F => exists_mem_Ioc_zpow (hxpos v) (hy v)
  set u : F := ∏ v ∈ S, ((π v : 𝓞 F) : F) ^ (n v + 1) with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (hπF v)
  have hvu : ∀ v' : FinitePlace F, v' u = ∏ v ∈ S, (v' ((π v : 𝓞 F) : F)) ^ (n v + 1) := by
    intro v'
    rw [hu, map_prod]
    exact Finset.prod_congr rfl fun v _ => map_zpow₀ v' _ _
  have hout : ∀ v' : FinitePlace F, v' ∉ S → v' u = 1 := by
    intro v' hv'
    rw [hvu]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [hπone v v' (fun h => hv' (h ▸ hv)), one_zpow]
  have hin : ∀ v' ∈ S, v' u = (v' ((π v' : 𝓞 F) : F)) ^ (n v' + 1) := by
    intro v' hv'
    rw [hvu]
    refine Finset.prod_eq_single v' (fun v _ hne' => ?_) (fun h => (h hv').elim)
    rw [hπone v v' (fun h => hne' h.symm), one_zpow]
  have hbd : ∀ v ∈ S, v ((π v : 𝓞 F) : F) ≤ v u * x v ∧ v u * x v ≤ 1 := by
    intro v hv
    obtain ⟨h1, h2⟩ := hn v
    set p := v ((π v : 𝓞 F) : F) with hp
    have hp0 : 0 < p := hπpos v
    rw [hin v hv]
    have e1 : p ^ (n v + 1) = ((p⁻¹) ^ (n v + 1))⁻¹ := by rw [inv_zpow, inv_inv]
    have hpos1 : 0 < (p⁻¹) ^ (n v + 1) := zpow_pos (inv_pos.mpr hp0) _
    rw [e1, inv_mul_le_one₀ hpos1, inv_mul_eq_div, le_div_iff₀ hpos1]
    refine ⟨?_, h2⟩
    rw [zpow_add_one₀ (inv_pos.mpr hp0).ne', ← mul_assoc, mul_comm p, mul_assoc,
      mul_inv_cancel₀ hp0.ne', mul_one]
    exact h1.le
  have hvuc : ∀ v : FinitePlace F, max (v (u * c)) (v (u * d)) = v u * x v := by
    intro v
    rw [map_mul, map_mul, hx, mul_max_of_nonneg _ _ (apply_nonneg v u)]
  have hint : ∀ a : F, (∀ v : FinitePlace F, v ∉ S → v a ≤ 1) →
      (∀ v : FinitePlace F, v a ≤ x v) → ∀ v : FinitePlace F, v (u * a) ≤ 1 := by
    intro a ha hax v
    rw [map_mul]
    by_cases hv : v ∈ S
    · exact (mul_le_mul_of_nonneg_left (hax v) (apply_nonneg v u)).trans (hbd v hv).2
    · rw [hout v hv, one_mul]; exact ha v hv
  obtain ⟨c', hc'⟩ := exists_int_of_forall_le_one (u * c) (hint c hc fun v => le_max_left _ _)
  obtain ⟨d', hd'⟩ := exists_int_of_forall_le_one (u * d) (hint d hd fun v => le_max_right _ _)
  refine ⟨u, hu0, hout, ⟨c', d', hc', hd'⟩, ?_⟩
  unfold X.sNorm
  refine Finset.prod_le_prod (fun v _ => (hπpos v).le) fun v hv => ?_
  rw [hvuc]
  exact (hbd v hv).1

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Pairs
/-! # WP-B1, file 4: primitive pairs of `S`-integers modulo `S`-units; convergence and top height

`S` is any finite set of finite places of the totally complex field `F`; `IsSInt S`, `IsSUnit S`
describe the ring `R = 𝓞_S` and its units inside `F`.  `SPair S` = primitive pairs of `R²`
(`a c + b d = 1` solvable in `R`), `PairClass S = SPair S / U_S`, `PairClass.ht p P = ht_p(P)` the
`S`-normalized height, `PairClass.act` the right action of `SL₂(𝓞_F)`:
`(p.act γ).ht P = p.ht (γ • P)`.

* `summable_sHt_rpow`, `exists_summable_majorant_sHt`: (B1) for any family of pairwise
  `U_S`-inequivalent nonzero pairs of `S`-integers (primitive or not), `σ > 2`.
* `PairClass.summable_ht_rpow`, `PairClass.exists_summable_majorant`, `PairClass.exists_max_ht`.
* `PairClass.exists_ht_ge` (Lemma M): `sup_p ht_p(P) ≥ c₀ > 0`, under `SBezout S` (true when `R` is a PID).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- `a ∈ R = 𝓞_S`. -/
def IsSInt (S : Finset (FinitePlace F)) (a : F) : Prop := ∀ v : FinitePlace F, v ∉ S → v a ≤ 1

/-- `u ∈ U_S = R^×`. -/
def IsSUnit (S : Finset (FinitePlace F)) (u : F) : Prop :=
  u ≠ 0 ∧ ∀ v : FinitePlace F, v ∉ S → v u = 1

variable {S : Finset (FinitePlace F)}

lemma isSInt_zero : IsSInt S (0 : F) := fun v _ => by simp
lemma isSInt_one : IsSInt S (1 : F) := fun v _ => by simp

lemma IsSInt.mul {a b : F} (ha : IsSInt S a) (hb : IsSInt S b) : IsSInt S (a * b) := fun v hv => by
  rw [map_mul]; exact mul_le_one₀ (ha v hv) (apply_nonneg v b) (hb v hv)

lemma IsSInt.add {a b : F} (ha : IsSInt S a) (hb : IsSInt S b) : IsSInt S (a + b) := fun v hv =>
  (FinitePlace.add_le v a b).trans (max_le (ha v hv) (hb v hv))

lemma IsSInt.neg {a : F} (ha : IsSInt S a) : IsSInt S (-a) := fun v hv => by
  have h2 : v (-a) = v a := v.1.map_neg a
  rw [h2]; exact ha v hv

lemma IsSUnit.isSInt {u : F} (hu : IsSUnit S u) : IsSInt S u := fun v hv => (hu.2 v hv).le

lemma IsSUnit.inv {u : F} (hu : IsSUnit S u) : IsSUnit S u⁻¹ :=
  ⟨inv_ne_zero hu.1, fun v hv => by rw [map_inv₀, hu.2 v hv, inv_one]⟩

/-! ### The raw right action of `SL₂(𝓞_F)` on pairs -/

/-! ### Primitive pairs and pair classes -/

/-- A primitive pair of `S`-integers. -/
@[ext] structure SPair (S : Finset (FinitePlace F)) where
  c : F
  d : F
  hc : IsSInt S c
  hd : IsSInt S d
  prim : ∃ a b : F, IsSInt S a ∧ IsSInt S b ∧ a * c + b * d = 1

/-! ### (B1) for families of `S`-integer pairs -/

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Bridge
/-! # WP-B1, file 10: bridges to the ring `R = 𝓞_S`

* `SIntRing S : Subring F`, the ring `{a | IsSInt S a}`; `isSInt_image_iff`: for
  `S = S₀.image FinitePlace.mk` it is Mathlib's `S₀.integer F` (so `SInt 𝔪` when `↑S₀ = placesOf 𝔪`).
* `sBezout_of_isPrincipalIdealRing`: the hypothesis `SBezout S` of Lemma M holds when `R` is a PID.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open NumberField IsDedekindDomain

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-- The ring `R = 𝓞_S` of `S`-integers, as a subring of `F`. -/
def SIntRing (S : Finset (FinitePlace F)) : Subring F where
  carrier := {a | IsSInt S a}
  mul_mem' := IsSInt.mul
  one_mem' := isSInt_one
  add_mem' := IsSInt.add
  zero_mem' := isSInt_zero
  neg_mem' := IsSInt.neg

open scoped Classical in
/-- For `S = S₀.image FinitePlace.mk`, `IsSInt S` is membership in Mathlib's ring of `S₀`-integers. -/
theorem isSInt_image_iff (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (a : F) :
    IsSInt (S₀.image FinitePlace.mk) a ↔ a ∈ (S₀ : Set (HeightOneSpectrum (𝓞 F))).integer F := by
  constructor
  · intro h v hv
    have hv' : FinitePlace.mk v ∉ S₀.image FinitePlace.mk := by
      intro hmem
      obtain ⟨v', hv', he⟩ := Finset.mem_image.mp hmem
      rw [FinitePlace.mk_eq_iff] at he
      exact hv (he ▸ hv')
    have h1 := h _ hv'
    rw [FinitePlace.mk_apply, FinitePlace.norm_embedding,
      NumberField.HeightOneSpectrum.adicAbv_def] at h1
    exact (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp (by exact_mod_cast h1)
  · intro h v hv
    rw [← FinitePlace.mk_maximalIdeal v] at hv ⊢
    exact X.finitePlace_le_one_of_mem_integer _ ⟨a, h⟩ _ fun hmem =>
      hv (Finset.mem_image_of_mem _ hmem)

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

/-- The chosen representative of a residue class modulo `c`. -/
noncomputable def rep (c : R) (x : R ⧸ Ideal.span {c}) : R :=
  Function.surjInv Ideal.Quotient.mk_surjective x

/-- The sum of `f` over (chosen representatives of) the residues modulo `c`. -/
noncomputable def rsum (c : R) (f : R → ℂ) : ℂ :=
  ∑ᶠ x : R ⧸ Ideal.span {c}, f (rep c x)

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

/-- Interface to WP-A: the cubic exterior symbol `sym d c = (d/c)` on a ring `R`. -/
structure CubicSymbol (R : Type*) [CommRing R] where
  /-- `sym d c = (d/c)` -/
  sym : R → R → ℂ
  sym_mul_left : ∀ d d' c : R, c ≠ 0 → sym (d * d') c = sym d c * sym d' c
  sym_mul_right : ∀ d c c' : R, c ≠ 0 → c' ≠ 0 → sym d (c * c') = sym d c * sym d c'
  sym_congr : ∀ d d' c : R, c ≠ 0 → c ∣ d - d' → sym d c = sym d' c
  sym_eq_zero_iff : ∀ d c : R, c ≠ 0 → (sym d c = 0 ↔ ¬ IsCoprime d c)
  sym_pow_three : ∀ d c : R, c ≠ 0 → IsCoprime d c → sym d c ^ 3 = 1
  sym_unit_right : ∀ d c : R, IsUnit c → sym d c = 1

/-- An additive character of `K` that is trivial on `R`. -/
structure AddData (R K : Type*) [CommRing R] [Field K] [Algebra R K] where
  /-- the character -/
  e : K → ℂ
  e_add : ∀ x y : K, e (x + y) = e x * e y
  e_int : ∀ r : R, e (algebraMap R K r) = 1
  inj : Function.Injective (algebraMap R K)

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

namespace AddData

variable (A : AddData R K)

/-- `ψ a c = e(a / c)`. -/
noncomputable def ψ (a c : R) : ℂ := A.e (algebraMap R K a / algebraMap R K c)

end AddData

/-! ### Elementary facts about the symbol -/

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-- The cubic Gauss sum `g(ν, c) = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)`. -/
noncomputable def gauss (ν c : R) : ℂ :=
  rsum c (fun d => (S.sym d c)⁻¹ * A.ψ (ν * d) c)

/-! ### Constant-term sums -/

/-! ### Prime powers -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3B_Norm
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Add
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

end C3I

end ArtinPrimitiveRoots
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

/-- `𝓞 → R / I R` is onto for `I` coprime to `𝔪`. -/
lemma exists_sub_mem_map (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (r : SInt 𝔪) :
    ∃ c : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) c ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨c, hc⟩ := hN w hw
  refine ⟨c, ?_⟩
  have : r - algebraMap (𝓞 F) (SInt 𝔪) c = algebraMap (𝓞 F) (SInt 𝔪) u * r := by
    rw [← hc]
    have : algebraMap (𝓞 F) (SInt 𝔪) u + algebraMap (𝓞 F) (SInt 𝔪) w = 1 := by
      rw [← map_add, huw, map_one]
    linear_combination (-r) * this
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

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

/-- Every nonzero ideal of `𝓞 F` extends to `R` as an exterior ideal does. (Universe-polymorphic
copy of `L3B.exists_exterior_map_eq`, which is stated for `F : Type`.) -/
theorem exists_exterior_map_eq (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧
      I.map (algebraMap (𝓞 F) (SInt 𝔪)) = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff] at hx
    exact ⟨⊤, ⟨top_ne_bot, top_sup_eq _⟩, by rw [hx]⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨𝔄, hE, hmap⟩ := ih ha
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp.ne_zero).1 hp
    by_cases hcop : p ⊔ 𝔪 = ⊤
    · refine ⟨p * 𝔄, ⟨mul_ne_zero hp.ne_zero hE.1, ?_⟩, ?_⟩
      · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact hcop), sup_comm,
          hE.2]
      · rw [Ideal.map_mul, Ideal.map_mul, hmap]
    · have hmax : p.IsMaximal := hpP.isMaximal hp.ne_zero
      have h𝔪p : 𝔪 ≤ p := by
        have := hmax.eq_of_le hcop le_sup_left
        rw [this]; exact le_sup_right
      have htop : p.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
        apply C0R.map_eq_top_of_primes 𝔪 h𝔪 p
        intro Q hQ hpQ
        have : Q = p := (hmax.eq_of_le hQ.ne_top hpQ).symm
        rw [this]; exact h𝔪p
      exact ⟨𝔄, hE, by rw [Ideal.map_mul, htop, Ideal.top_mul, hmap]⟩

/-- Every element of `F` has a witness for `sAddChar`. -/
lemma hasWit_all (h𝔪 : 𝔪 ≠ ⊥) (x : F) : C3I.HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h; exact hd0 (by simpa using h)
  have hI : Ideal.span ({d} : Set (𝓞 F)) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
  refine C3I.hasWit_of_mul_mem x 𝔄 hE.2 fun i hi => ?_
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ Ideal.span {algebraMap (𝓞 F) (SInt 𝔪) d} := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (SInt 𝔪)) hi
    rwa [← hmap, Ideal.map_span, Set.image_singleton] at this
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
  have hiF : algebraMap (𝓞 F) F i = (r : F) * algebraMap (𝓞 F) F d := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hr
    simp only [Subalgebra.coe_mul] at this
    exact this.symm
  rw [← hbd, hiF, show algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d * ((r : F) * algebraMap (𝓞 F) F d) =
    algebraMap (𝓞 F) F b * (r : F) by field_simp]
  exact mul_mem (algebraMap (𝓞 F) (SInt 𝔪) b).2 r.2

/-- `sAddChar 𝔪` is additive on all of `F`. -/
theorem sAddChar_add_all (h𝔪 : 𝔪 ≠ ⊥) (x y : F) :
    sAddChar 𝔪 (x + y) = sAddChar 𝔪 x * sAddChar 𝔪 y :=
  C3I.sAddChar_add (hasWit_all h𝔪 x) (hasWit_all h𝔪 y)

/-- `sAddChar 𝔪` as additive-character data for `R = SInt 𝔪 ⊆ F`. -/
noncomputable def sAdd (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : AddData (SInt 𝔪) F where
  e := sAddChar 𝔪
  e_add := sAddChar_add_all h𝔪
  e_int := fun r => C3B.sAddChar_of_mem _ r.2
  inj := Subtype.val_injective

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Basic
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

/-- `x` has valuation `≤ exp (-N)` at every finite place of `S`. -/
def Small (𝔪 : Ideal (𝓞 F)) (N : ℤ) (x : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F x ≤ WithZero.exp (-N)

namespace Small

variable {𝔪 : Ideal (𝓞 F)} {N M : ℤ} {x y : F}

theorem zero : Small 𝔪 N (0 : F) := fun v _ => by simp

theorem add (hx : Small 𝔪 N x) (hy : Small 𝔪 N y) : Small 𝔪 N (x + y) := fun v hv =>
  (Valuation.map_add _ x y).trans (max_le (hx v hv) (hy v hv))

theorem neg (hx : Small 𝔪 N x) : Small 𝔪 N (-x) := fun v hv => by
  rw [Valuation.map_neg]; exact hx v hv

theorem sub (hx : Small 𝔪 N x) (hy : Small 𝔪 N y) : Small 𝔪 N (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem mul (hx : Small 𝔪 N x) (hy : Small 𝔪 M y) : Small 𝔪 (N + M) (x * y) := fun v hv => by
  rw [map_mul, neg_add, WithZero.exp_add]
  exact mul_le_mul' (hx v hv) (hy v hv)

theorem mono (h : N ≤ M) (hx : Small 𝔪 M x) : Small 𝔪 N x := fun v hv =>
  (hx v hv).trans (WithZero.exp_le_exp.mpr (by omega))

/-- A deep unit is a unit at the places of `S_f`. -/
theorem val_eq_one (hN : 1 ≤ N) (h : Small 𝔪 N (x - 1)) (v : HeightOneSpectrum (𝓞 F))
    (hv : 𝔪 ≤ v.asIdeal) : v.valuation F x = 1 := by
  have h1 : v.valuation F (x - 1) < 1 := by
    refine (h v hv).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have := Valuation.map_one_add_of_lt (v := v.valuation F) h1
  rwa [add_sub_cancel] at this

end Small

/-! ### Absolute values at `S_f` -/

open NumberField.HeightOneSpectrum in
theorem abv_le_of_val_le (v : HeightOneSpectrum (𝓞 F)) {x : F} {n : ℤ}
    (h : v.valuation F x ≤ WithZero.exp (-n)) :
    adicAbv F v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [NumberField.HeightOneSpectrum.adicAbv_def]
  have e : (Ideal.absNorm v.asIdeal : ℝ) ^ (-n)
      = ((WithZeroMulInt.toNNReal hq.ne_zero (WithZero.exp (-n) :
          WithZero (Multiplicative ℤ)) : NNReal) : ℝ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    push_cast
    rfl
  rw [e, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono hq).monotone h

/-- `|x|_{S_f} = ∏_{v ∣ 𝔪} |x|_v` (normalized absolute values). -/
def absS (𝔪 : Ideal (𝓞 F)) (x : F) : ℝ :=
  ∏ v ∈ CubicPkg.sFin 𝔪, NumberField.HeightOneSpectrum.adicAbv F v x

/-- `‖(c, d)‖_{S_f} = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`. -/
def normS (𝔪 : Ideal (𝓞 F)) (c d : F) : ℝ :=
  ∏ v ∈ CubicPkg.sFin 𝔪, max (NumberField.HeightOneSpectrum.adicAbv F v c)
    (NumberField.HeightOneSpectrum.adicAbv F v d)

section abs

variable {𝔪 : Ideal (𝓞 F)}

open NumberField.HeightOneSpectrum

@[simp] theorem absS_one : absS 𝔪 (1 : F) = 1 := by simp [absS]

theorem absS_pos {x : F} (hx : x ≠ 0) : 0 < absS 𝔪 x :=
  Finset.prod_pos fun v _ => (adicAbv F v).pos hx

theorem normS_nonneg (c d : F) : 0 ≤ normS 𝔪 c d :=
  Finset.prod_nonneg fun v _ => le_max_of_le_left ((adicAbv F v).nonneg c)

theorem normS_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : 0 < normS 𝔪 c d :=
  Finset.prod_pos fun v _ => by
    rcases h with h | h
    · exact lt_max_of_lt_left ((adicAbv F v).pos h)
    · exact lt_max_of_lt_right ((adicAbv F v).pos h)

theorem normS_mul_left (t c d : F) : normS 𝔪 (t * c) (t * d) = absS 𝔪 t * normS 𝔪 c d := by
  simp only [normS, absS, map_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mul_max_of_nonneg _ _ ((adicAbv F v).nonneg t)]

end abs

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

open Classical in
/-- `⟨x, y⟩ := ι (x, y)_S` for `x, y ≠ 0`; `1` if `x = 0` or `y = 0`.  On coprime elements of `R`
this is `(y/x)(x/y)⁻¹` (`brk_reciprocity`), MATH2's `⟨x, y⟩`. -/
def brk (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (x y : F) : ℂ :=
  if h : x ≠ 0 ∧ y ≠ 0 then iota3 ι (P.HS 𝔪 (Units.mk0 x h.1) (Units.mk0 y h.2)) else 1

section brk

variable {ι : F →+* ℂ} {P : CubicPkg F} {𝔪 : Ideal (𝓞 F)}

theorem brk_units (a b : Fˣ) : brk ι P 𝔪 (a : F) (b : F) = iota3 ι (P.HS 𝔪 a b) := by
  simp only [brk, dif_pos (And.intro a.ne_zero b.ne_zero), Units.mk0_val]

@[simp] theorem brk_zero_left (y : F) : brk ι P 𝔪 0 y = 1 := by simp [brk]

@[simp] theorem brk_zero_right (x : F) : brk ι P 𝔪 x 0 = 1 := by simp [brk]

theorem brk_pow_three (x y : F) : brk ι P 𝔪 x y ^ 3 = 1 := by
  unfold brk
  split_ifs
  · exact iota3_pow_three ι _
  · exact one_pow 3

theorem brk_ne_zero (x y : F) : brk ι P 𝔪 x y ≠ 0 := by
  intro h0
  have := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) x y
  rw [h0] at this
  norm_num at this

@[simp] theorem brk_self (x : F) : brk ι P 𝔪 x x = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  lift x to Fˣ using IsUnit.mk0 x hx
  rw [brk_units, P.HS_self, map_one]

theorem brk_skew (x y : F) : brk ι P 𝔪 x y = (brk ι P 𝔪 y x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [brk_units, brk_units, P.HS_skew', iota3_inv]

@[simp] theorem brk_neg_left (x y : F) : brk ι P 𝔪 (-x) y = brk ι P 𝔪 x y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_neg, brk_units, brk_units, P.HS_neg_left]

@[simp] theorem brk_neg_right (x y : F) : brk ι P 𝔪 x (-y) = brk ι P 𝔪 x y := by
  rw [brk_skew, brk_neg_left, ← brk_skew]

@[simp] theorem brk_one_left (y : F) : brk ι P 𝔪 1 y = 1 := by
  by_cases hy : y = 0
  · simp [hy]
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_one, brk_units, map_one, MonoidHom.one_apply, map_one]

@[simp] theorem brk_one_right (x : F) : brk ι P 𝔪 x 1 = 1 := by
  rw [brk_skew, brk_one_left, inv_one]

@[simp] theorem brk_pow_three_left (t y : F) : brk ι P 𝔪 (t ^ 3) y = 1 := by
  by_cases ht : t = 0
  · simp [ht]
  by_cases hy : y = 0
  · simp [hy]
  lift t to Fˣ using IsUnit.mk0 t ht
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_pow_eq_pow_val, brk_units, P.HS_pow_three_left, map_one]

@[simp] theorem brk_pow_three_right (x t : F) : brk ι P 𝔪 x (t ^ 3) = 1 := by
  rw [brk_skew, brk_pow_three_left, inv_one]

/-- `S`-units pair trivially. -/
theorem brk_sunit (hG : Good 𝔪) {x y : F}
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F x = 1)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F y = 1) :
    brk ι P 𝔪 x y = 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  lift x to Fˣ using IsUnit.mk0 x hx0
  lift y to Fˣ using IsUnit.mk0 y hy0
  rw [brk_units, P.HS_unit hG.ne_bot hG.three x y hx hy, map_one]

end brk

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-- `σ_S((c,d), [[a,b],[c',d']])` read through `ι`:
`⟨X((c,d)γ)/X(c,d), X((c,d)γ)/X(γ)⟩`. -/
def sig (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (c d a b c' d' : F) : ℂ :=
  brk ι P 𝔪 (Xs (c * a + d * c') (c * b + d * d') / Xs c d)
    (Xs (c * a + d * c') (c * b + d * d') / Xs c' d')

theorem Xs_of_ne {c : F} (d : F) (hc : c ≠ 0) : Xs c d = c := by
  simp [Xs, hc]

@[simp] theorem Xs_zero (d : F) : Xs 0 d = d := by simp [Xs]

theorem iota3_sigmaS (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F))
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F) :
    iota3 ι (sigmaS P 𝔪 g₁ g₂)
      = sig ι P 𝔪 (g₁.1 1 0) (g₁.1 1 1) (g₂.1 0 0) (g₂.1 0 1) (g₂.1 1 0) (g₂.1 1 1) := by
  have h3 : X (g₁ * g₂) = Xs (g₁.1 1 0 * g₂.1 0 0 + g₁.1 1 1 * g₂.1 1 0)
      (g₁.1 1 0 * g₂.1 0 1 + g₁.1 1 1 * g₂.1 1 1) := by
    simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  rw [sig, sigmaS, ← brk_units, Units.val_div_eq_div_val, Units.val_div_eq_div_val, coe_Xu,
    coe_Xu, coe_Xu, h3]
  rfl

/-! ### Primitive rows -/

variable {𝔪 : Ideal (𝓞 F)}

/-- Primitive pairs of `R = SInt 𝔪`: the bottom rows of `SL₂(R)`. -/
def Row (𝔪 : Ideal (𝓞 F)) : Type _ := {p : SInt 𝔪 × SInt 𝔪 // IsCoprime p.1 p.2}

namespace Row

/-- first entry -/
def c (p : Row 𝔪) : SInt 𝔪 := p.1.1

/-- second entry -/
def d (p : Row 𝔪) : SInt 𝔪 := p.1.2

@[ext] theorem ext {p q : Row 𝔪} (hc : p.c = q.c) (hd : p.d = q.d) : p = q :=
  Subtype.ext (Prod.ext hc hd)

/-- The bottom row of a matrix. -/
def bot (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) : Row 𝔪 :=
  ⟨(γ.1 1 0, γ.1 1 1), ⟨-γ.1 0 1, γ.1 0 0, by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    linear_combination h⟩⟩

@[simp] theorem bot_c (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) : (bot γ).c = γ.1 1 0 := rfl

@[simp] theorem bot_d (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) : (bot γ).d = γ.1 1 1 := rfl

/-- Right action of `SL₂(R)` on rows: `(c, d) ↦ (c, d) γ`. -/
def act (p : Row 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) : Row 𝔪 :=
  ⟨(p.c * γ.1 0 0 + p.d * γ.1 1 0, p.c * γ.1 0 1 + p.d * γ.1 1 1), by
    obtain ⟨u, v, h⟩ := p.2
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    refine ⟨u * γ.1 1 1 - v * γ.1 0 1, -u * γ.1 1 0 + v * γ.1 0 0, ?_⟩
    change _ * (p.1.1 * _ + p.1.2 * _) + _ * (p.1.1 * _ + p.1.2 * _) = 1
    linear_combination (u * p.1.1 + v * p.1.2) * hdet + h⟩

@[simp] theorem act_c (p : Row 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    (p.act γ).c = p.c * γ.1 0 0 + p.d * γ.1 1 0 := rfl

@[simp] theorem act_d (p : Row 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    (p.act γ).d = p.c * γ.1 0 1 + p.d * γ.1 1 1 := rfl

@[simp] theorem act_one (p : Row 𝔪) : p.act 1 = p := by
  ext <;> simp

theorem act_mul (p : Row 𝔪) (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    p.act (γ₁ * γ₂) = (p.act γ₁).act γ₂ := by
  ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem bot_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    bot (γ₁ * γ₂) = (bot γ₁).act γ₂ := by
  ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_bot (p : Row 𝔪) : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪), bot γ = p := by
  obtain ⟨u, v, h⟩ := p.2
  refine ⟨⟨!![v, -u; p.c, p.d], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    change v * p.1.2 - -u * p.1.1 = 1
    linear_combination h
  · ext <;> rfl

/-- A matrix with bottom row `p`. -/
def lift (p : Row 𝔪) : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪) := (exists_bot p).choose

@[simp] theorem bot_lift (p : Row 𝔪) : bot (lift p) = p := (exists_bot p).choose_spec

/-- Scaling by a unit of `R`. -/
instance instSMulUnitsSInt : SMul (SInt 𝔪)ˣ (Row 𝔪) where
  smul ε p := ⟨((ε : SInt 𝔪) * p.c, (ε : SInt 𝔪) * p.d), by
    obtain ⟨u, v, h⟩ := p.2
    refine ⟨((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * u, ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * v, ?_⟩
    have hε : ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * (ε : SInt 𝔪) = 1 := ε.inv_mul
    change _ * (_ * p.1.1) + _ * (_ * p.1.2) = 1
    linear_combination (u * p.1.1 + v * p.1.2) * hε + h⟩

@[simp] theorem smul_c (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) : (ε • p).c = (ε : SInt 𝔪) * p.c := rfl

@[simp] theorem smul_d (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) : (ε • p).d = (ε : SInt 𝔪) * p.d := rfl

theorem smul_act (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    (ε • p).act γ = ε • p.act γ := by
  ext <;> simp <;> ring

/-- A primitive row is primitive at every exterior place. -/
theorem val_or (p : Row 𝔪) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) :
    v.valuation F (p.c : F) = 1 ∨ v.valuation F (p.d : F) = 1 := by
  have := row_coprime (lift p) v hv
  rwa [← bot_c, ← bot_d, bot_lift] at this

theorem ne_zero (p : Row 𝔪) : (p.c : F) ≠ 0 ∨ (p.d : F) ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  obtain ⟨u, v, huv⟩ := p.2
  have h1 := congrArg (fun x : SInt 𝔪 => (x : F)) huv
  change ((u * p.c + v * p.d : SInt 𝔪) : F) = ((1 : SInt 𝔪) : F) at h1
  push_cast at h1
  rw [h.1, h.2] at h1
  simp at h1

end Row

/-! ### The Kubota symbol on rows -/

open Classical in
/-- `κ(c, d) = (d/c)⁻¹` for `c ≠ 0`, `κ(0, d) = 1`. -/
def kappaRow (ι : F →+* ℂ) (p : Row 𝔪) : ℂ :=
  if p.c = 0 then 1 else (cubicExt ι 𝔪 p.d p.c)⁻¹

theorem kappa_eq_kappaRow (ι : F →+* ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    kappa ι 𝔪 γ = kappaRow ι (Row.bot γ) := rfl

section kappa

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include P hG hz6

/-- **Lemma A5 on rows**: `κ(pγ) = κ(p) κ(γ) σ_S(p, γ)⁻¹`. -/
theorem kappaRow_act (p : Row 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    kappaRow ι (p.act γ) = kappaRow ι p * kappa ι 𝔪 γ *
      (sig ι P 𝔪 (p.c : F) (p.d : F) ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F)
        ((γ.1 1 0 : SInt 𝔪) : F) ((γ.1 1 1 : SInt 𝔪) : F))⁻¹ := by
  have h := kappa_mul ι P hG hz6 (Row.lift p) γ
  have hc : (Row.lift p).1 1 0 = p.c := congrArg Row.c (Row.bot_lift p)
  have hd : (Row.lift p).1 1 1 = p.d := congrArg Row.d (Row.bot_lift p)
  rw [kappa_eq_kappaRow, Row.bot_mul, Row.bot_lift, kappa_eq_kappaRow ι (Row.lift p),
    Row.bot_lift, iota3_sigmaS] at h
  rw [h]
  simp only [toF_apply, hc, hd]

theorem kappaRow_pow_three (p : Row 𝔪) : kappaRow ι p ^ 3 = 1 := by
  rw [← Row.bot_lift p, ← kappa_eq_kappaRow]
  exact kappa_pow_three ι P hG hz6 _

/-- **Homogeneity of `κ`** (the symbol factor forced by A5 for `diag(ε⁻¹, ε)`):
`κ(εc, εd) = ⟨c, ε⟩⁻¹ κ(c, d)` for `ε ∈ U_S`. -/
theorem kappaRow_smul (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) :
    kappaRow ι (ε • p) = (brk ι P 𝔪 (p.c : F) ((ε : SInt 𝔪) : F))⁻¹ * kappaRow ι p := by
  have hε := unit_val_eq_one ε
  have hε0 : (ε : SInt 𝔪) ≠ 0 := ε.ne_zero
  by_cases hc : p.c = 0
  · simp [kappaRow, hc]
  have hεc : (ε : SInt 𝔪) * p.c ≠ 0 := mul_ne_zero hε0 hc
  have hcF : (p.c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hεF : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => hε0 (Subtype.ext h)
  rw [kappaRow, if_neg (by simpa using hεc), kappaRow, if_neg hc, Row.smul_c, Row.smul_d,
    ← mul_inv]
  congr 1
  by_cases hcu : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (p.c : F) = 1
  · rw [cubicExt_of_unit_right ι _ _ hcu, cubicExt_of_unit_right ι _ _ (fun v hv => by
      push_cast; rw [map_mul, hε v hv, hcu v hv, one_mul]), brk_sunit hG hcu hε, one_mul]
  · push_neg at hcu
    obtain ⟨v₀, hv₀, hne⟩ := hcu
    have hd1 := (p.val_or v₀ hv₀).resolve_left hne
    have hd0 : p.d ≠ 0 := by
      rintro h
      rw [h] at hd1
      simp at hd1
    have hdc : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (p.c : F) ≠ 1 →
        v.valuation F (p.d : F) = 1 := fun v hv h => (p.val_or v hv).resolve_left h
    have hεd : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v.valuation F (p.c : F) ≠ 1 →
        v.valuation F (((ε : SInt 𝔪) * p.d : SInt 𝔪) : F) = 1 := fun v hv h => by
      push_cast; rw [map_mul, hε v hv, hdc v hv h, one_mul]
    rw [cubicExt_mul_right ι P hG hz6 (ε : SInt 𝔪) p.c ((ε : SInt 𝔪) * p.d) hε0 hc
        (mul_ne_zero hε0 hd0) (fun v hv h => absurd (hε v hv) h) hεd,
      cubicExt_of_unit_right ι _ _ hε, one_mul,
      cubicExt_mul_left ι P hG hz6 p.c (ε : SInt 𝔪) p.d hc (fun v hv _ => hε v hv) hdc,
      cubicExt_unit_left ι P hG hz6 p.c (ε : SInt 𝔪) (Units.mk0 _ hcF) (Units.mk0 _ hεF) rfl rfl
        hε, ← brk_units]
    rfl

end kappa

/-! ### The matrices `w` and `n(t)` -/

/-- `w = [[0, -1], [1, 0]]`; `(c, d) w = (d, -c)`. -/
def wMat (𝔪 : Ideal (𝓞 F)) : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- `n(t) = [[1, t], [0, 1]]`; `(c, d) n(t) = (c, d + ct)`. -/
def nMat (t : SInt 𝔪) : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem wMat_00 : (wMat 𝔪).1 0 0 = 0 := rfl
@[simp] theorem wMat_01 : (wMat 𝔪).1 0 1 = -1 := rfl
@[simp] theorem wMat_10 : (wMat 𝔪).1 1 0 = 1 := rfl
@[simp] theorem wMat_11 : (wMat 𝔪).1 1 1 = 0 := rfl
@[simp] theorem nMat_00 (t : SInt 𝔪) : (nMat t).1 0 0 = 1 := rfl
@[simp] theorem nMat_01 (t : SInt 𝔪) : (nMat t).1 0 1 = t := rfl
@[simp] theorem nMat_10 (t : SInt 𝔪) : (nMat t).1 1 0 = 0 := rfl
@[simp] theorem nMat_11 (t : SInt 𝔪) : (nMat t).1 1 1 = 1 := rfl

@[simp] theorem act_wMat_c (p : Row 𝔪) : (p.act (wMat 𝔪)).c = p.d := by simp

@[simp] theorem act_wMat_d (p : Row 𝔪) : (p.act (wMat 𝔪)).d = -p.c := by simp

@[simp] theorem act_nMat_c (p : Row 𝔪) (t : SInt 𝔪) : (p.act (nMat t)).c = p.c := by simp

@[simp] theorem act_nMat_d (p : Row 𝔪) (t : SInt 𝔪) : (p.act (nMat t)).d = p.c * t + p.d := by
  simp

/-- Entries of `γ ∈ Γ(𝔪^N)` are `S_f`-adically `N`-close to the identity. -/
theorem small_of_mem_Gamma {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)}
    (hγ : γ ∈ Gamma 𝔪 (𝔪 ^ N)) (i j : Fin 2) :
    Small 𝔪 N (((γ.1 i j : SInt 𝔪) : F) - (if i = j then 1 else 0)) := by
  obtain ⟨γ₀, h0, rfl⟩ := (mem_Gamma_iff γ).mp hγ
  intro v hv
  have hmem : γ₀.1 i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j ∈ v.asIdeal ^ N :=
    Ideal.pow_right_mono hv N (h0 i j)
  have := (v.intValuation_le_pow_iff_mem _ N).mpr hmem
  rw [← v.valuation_of_algebraMap (K := F)] at this
  have e : ((((Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪)) γ₀).1 i j : SInt 𝔪)) : F)
      - (if i = j then 1 else 0)
      = algebraMap (𝓞 F) F (γ₀.1 i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j) := by
    rw [map_sub, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  simpa using this

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Level
/-!
# WP-S, part 2: congruence subgroups under conjugation by `SL₂(R)`

* `mem_Gamma_iff'`: `γ ∈ Γ(𝔫)` iff every entry of `γ - 1` is (the image of) an element of `𝔫`.
* `exists_level_conj`: for `σ ∈ SL₂(R)` and `𝔫 ≠ 0` there is `𝔫' ≠ 0` with
  `σ Γ(𝔫') σ⁻¹ ⊆ Γ(𝔫)` and `κ(σγσ⁻¹) = κ(γ)` on `Γ(𝔫')`.  This is what makes the right
  translation action of `SL₂(R)` on twisted sections preserve "level".
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `x ∈ F` is the image of an element of the ideal `𝔫` of `𝓞 F`. -/
def InI (𝔫 : Ideal (𝓞 F)) (x : F) : Prop := ∃ y ∈ 𝔫, algebraMap (𝓞 F) F y = x

namespace InI

variable {𝔫 𝔫' : Ideal (𝓞 F)} {x y : F}

theorem add (hx : InI 𝔫 x) (hy : InI 𝔫 y) : InI 𝔫 (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, 𝔫.add_mem ha hb, map_add _ _ _⟩

theorem mono (h : 𝔫' ≤ 𝔫) (hx : InI 𝔫' x) : InI 𝔫 x := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, h ha, rfl⟩

end InI

theorem mem_Gamma_iff' {𝔫 : Ideal (𝓞 F)} (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    γ ∈ Gamma 𝔪 𝔫 ↔
      ∀ i j, InI 𝔫 (((γ.1 i j : SInt 𝔪) : F) - (if i = j then 1 else 0)) := by
  constructor
  · intro hγ i j
    obtain ⟨γ₀, h0, rfl⟩ := (mem_Gamma_iff γ).mp hγ
    refine ⟨_, h0 i j, ?_⟩
    rw [map_sub, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    choose y hy hyx using h
    set M₀ : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => y i j + (1 : Matrix _ _ (𝓞 F)) i j
      with hM₀
    have hent : ∀ i j, algebraMap (𝓞 F) F (M₀ i j) = ((γ.1 i j : SInt 𝔪) : F) := by
      intro i j
      rw [hM₀]
      simp only [map_add, hyx i j, Matrix.one_apply]
      split_ifs <;> simp
    have hdet : M₀.det = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, hent, hent, hent, hent, map_one]
      exact det_coe γ
    refine (mem_Gamma_iff γ).mpr ⟨⟨M₀, hdet⟩, fun i j => ?_, ?_⟩
    · simpa [hM₀] using hy i j
    · ext i j
      exact hent i j

theorem Gamma_mono {𝔫 𝔫' : Ideal (𝓞 F)} (h : 𝔫' ≤ 𝔫) : Gamma 𝔪 𝔫' ≤ Gamma 𝔪 𝔫 := by
  intro γ hγ
  rw [mem_Gamma_iff'] at hγ ⊢
  exact fun i j => (hγ i j).mono h

/-- Every element of `F` is bounded at the places of `S_f`. -/
theorem exists_small_neg (h𝔪 : 𝔪 ≠ ⊥) (x : F) : ∃ B : ℕ, Small 𝔪 (-(B : ℤ)) x := by
  classical
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ Small.zero⟩
  refine ⟨(CubicPkg.sFin 𝔪).sup fun v => (ordv v x).natAbs, fun v hv => ?_⟩
  rw [val_eq_exp_ordv v hx, WithZero.exp_le_exp, neg_neg]
  have h1 : (ordv v x).natAbs ≤ (CubicPkg.sFin 𝔪).sup fun v => (ordv v x).natAbs :=
    Finset.le_sup (f := fun v => (ordv v x).natAbs) ((CubicPkg.mem_sFin h𝔪 v).mpr hv)
  omega

/-- **Conjugation lemma.**  For `σ ∈ SL₂(R)` and `𝔫 ≠ 0` there is `𝔫' ≠ 0` such that
`σ Γ(𝔫') σ⁻¹ ⊆ Γ(𝔫)` and `κ(σ γ σ⁻¹) = κ(γ)` for `γ ∈ Γ(𝔫')`. -/
theorem exists_level_conj (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (𝔫 : Ideal (𝓞 F)) (h𝔫 : 𝔫 ≠ ⊥) :
    ∃ 𝔫' : Ideal (𝓞 F), 𝔫' ≠ ⊥ ∧ ∀ γ ∈ Gamma 𝔪 𝔫',
      σ * γ * σ⁻¹ ∈ Gamma 𝔪 𝔫 ∧ kappa ι 𝔪 (σ * γ * σ⁻¹) = kappa ι 𝔪 γ := by
  classical
  obtain ⟨N, hN1, hN⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot ((toF 𝔪 σ).1 1 1 / (toF 𝔪 σ).1 1 0)
  obtain ⟨m, hm0, hmσ, hmτ⟩ : ∃ m : 𝓞 F, m ≠ 0 ∧
      (∀ i j, InI ⊤ (algebraMap (𝓞 F) F m * (toF 𝔪 σ).1 i j)) ∧
      (∀ i j, InI ⊤ (algebraMap (𝓞 F) F m * (toF 𝔪 σ⁻¹).1 i j)) := by
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
      ((Finset.univ.image fun ij : Fin 2 × Fin 2 => (toF 𝔪 σ).1 ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Fin 2 × Fin 2 => (toF 𝔪 σ⁻¹).1 ij.1 ij.2))
    refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i j => ?_, fun i j => ?_⟩
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
      exact ⟨y, trivial, by rw [hy, Algebra.smul_def]⟩
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
      exact ⟨y, trivial, by rw [hy, Algebra.smul_def]⟩
  have h1 : Ideal.span {m ^ 2} ≠ (0 : Ideal (𝓞 F)) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero 2 hm0
  have h2 : 𝔫 * 𝔪 ^ (N + B) ≠ (0 : Ideal (𝓞 F)) :=
    mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact hG.ne_bot))
  refine ⟨Ideal.span {m ^ 2} * (𝔫 * 𝔪 ^ (N + B)), by
    rw [← Ideal.zero_eq_bot]; exact mul_ne_zero h1 h2, fun γ hγ => ?_⟩
  set A : Matrix (Fin 2) (Fin 2) F := (toF 𝔪 σ).1 with hA
  set G : Matrix (Fin 2) (Fin 2) F := (toF 𝔪 γ).1 with hGm
  set T : Matrix (Fin 2) (Fin 2) F := (toF 𝔪 σ⁻¹).1 with hT
  have hAT : A * T = 1 := by
    rw [hA, hT, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hprodM : (toF 𝔪 (σ * γ * σ⁻¹)).1 = A * G * T := by
    rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hγ' := (mem_Gamma_iff' γ).mp hγ
  -- membership
  have term : ∀ i k l j, InI 𝔫 (A i k * (G k l - (1 : Matrix (Fin 2) (Fin 2) F) k l) * T l j) := by
    intro i k l j
    obtain ⟨y, hy, hyx⟩ := hγ' k l
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    obtain ⟨s, -, hs⟩ := hmσ i k
    obtain ⟨t, -, ht⟩ := hmτ l j
    have hz' : z ∈ 𝔫 := (Ideal.mul_le_left (I := 𝔫) (J := 𝔪 ^ (N + B))) hz
    refine ⟨s * t * z, 𝔫.mul_mem_left _ hz', ?_⟩
    have e : G k l - (1 : Matrix (Fin 2) (Fin 2) F) k l
        = algebraMap (𝓞 F) F (m ^ 2 * z) := by
      have hGkl : G k l = ((γ.1 k l : SInt 𝔪) : F) := toF_apply 𝔪 γ k l
      rw [hyx, Matrix.one_apply, hGkl]
    rw [e]
    simp only [map_mul, hs, ht, map_pow]
    ring
  have hmem : σ * γ * σ⁻¹ ∈ Gamma 𝔪 𝔫 := by
    rw [mem_Gamma_iff']
    intro i j
    have key : (((σ * γ * σ⁻¹).1 i j : SInt 𝔪) : F) - (if i = j then 1 else 0)
        = (A * (G - 1) * T) i j := by
      have e1 : (if i = j then (1 : F) else 0) = (1 : Matrix (Fin 2) (Fin 2) F) i j := by
        rw [Matrix.one_apply]
      rw [← toF_apply, hprodM, e1, ← Matrix.sub_apply]
      congr 1
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAT]
    rw [key]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, add_mul]
    exact ((term i 0 0 j).add (term i 1 0 j)).add ((term i 0 1 j).add (term i 1 1 j))
  refine ⟨hmem, ?_⟩
  -- the symbol
  have hγN : γ ∈ Gamma 𝔪 (𝔪 ^ (N + B)) :=
    Gamma_mono (le_trans (Ideal.mul_le_right (J := 𝔫 * 𝔪 ^ (N + B)) (I := Ideal.span {m ^ 2}))
      (Ideal.mul_le_right (J := 𝔪 ^ (N + B)) (I := 𝔫))) hγ
  have ha : Small 𝔪 N (G 0 0 - 1) := by
    have := small_of_mem_Gamma hγN 0 0
    simp only [if_true] at this
    exact Small.mono (by push_cast; omega) this
  have hcγ : Small 𝔪 ((N + B : ℕ) : ℤ) (G 1 0) := by
    have h := small_of_mem_Gamma hγN 1 0
    rw [if_neg (by decide), sub_zero] at h
    exact h
  have hdγ : Small 𝔪 N (G 1 1 - 1) := by
    have := small_of_mem_Gamma hγN 1 1
    simp only [if_true] at this
    exact Small.mono (by push_cast; omega) this
  set γ'' := σ * γ * σ⁻¹ with hγ''
  have hprod : γ'' * σ = σ * γ := by simp [hγ'', mul_assoc]
  have k1 := kappa_mul ι P hG hz6 σ γ
  have k2 := kappa_mul ι P hG hz6 γ'' σ
  rw [hprod] at k2
  have hprodF : toF 𝔪 γ'' * toF 𝔪 σ = toF 𝔪 σ * toF 𝔪 γ := by
    rw [← map_mul, hprod, map_mul]
  have hX3 : X (toF 𝔪 σ * toF 𝔪 γ)
      = Xs (A 1 0 * G 0 0 + A 1 1 * G 1 0) (A 1 0 * G 0 1 + A 1 1 * G 1 1) := by
    simp [X, hA, hGm, Matrix.mul_apply, Fin.sum_univ_two]
  have hXσ : X (toF 𝔪 σ) = Xs (A 1 0) (A 1 1) := rfl
  have hXγ : X (toF 𝔪 γ) = Xs (G 1 0) (G 1 1) := rfl
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hN1' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN1
  have hsig : sigmaS P 𝔪 (toF 𝔪 γ'') (toF 𝔪 σ) = sigmaS P 𝔪 (toF 𝔪 σ) (toF 𝔪 γ) := by
    rw [sigmaS, sigmaS, hprodF]
    -- the generic case: `X(σγ)/X(σ)` is a deep unit
    have caseA : Small 𝔪 N (X (toF 𝔪 σ * toF 𝔪 γ) / X (toF 𝔪 σ) - 1) →
        P.HS 𝔪 (Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 γ'')) (Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 σ))
          = P.HS 𝔪 (Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 σ))
              (Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 γ)) := by
      intro hd
      have hd' : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
          v.valuation F (((Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 σ) : Fˣ) : F) - 1)
            ≤ WithZero.exp (-(N : ℤ)) := fun v hv => by
        rw [Units.val_div_eq_div_val, coe_Xu, coe_Xu]
        exact hd v hv
      rw [P.HS_deep_right hG.ne_bot hN _ _ hd', P.HS_deep_left hG.ne_bot hN _ _ hd']
    by_cases hc : A 1 0 = 0
    · have hdσ : A 1 1 ≠ 0 := by
        have := X_ne_zero (toF 𝔪 σ)
        rwa [hXσ, hc, Xs_zero] at this
      by_cases hcg : G 1 0 = 0
      · apply caseA
        rw [hX3, hXσ, hc, hcg]
        simp only [zero_mul, mul_zero, add_zero, zero_add, Xs_zero]
        rw [mul_div_cancel_left₀ _ hdσ]
        exact hdγ
      · -- `c_σ = 0`, `c_γ ≠ 0`
        have hc'' : (toF 𝔪 γ'').1 1 0 = A 1 1 ^ 2 * G 1 0 := by
          have hT00 : T 0 0 = A 1 1 := by
            simp [hT, hA, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
          have hT10 : T 1 0 = -A 1 0 := by
            simp [hT, hA, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
          rw [hγ'', hprodM]
          simp only [Matrix.mul_apply, Fin.sum_univ_two, hT00, hT10, hc]
          ring
        have hne'' : (toF 𝔪 γ'').1 1 0 ≠ 0 := by
          rw [hc'']; exact mul_ne_zero (pow_ne_zero 2 hdσ) hcg
        have hX'' : X (toF 𝔪 γ'') = A 1 1 ^ 2 * G 1 0 := by
          rw [X, Xs_of_ne _ hne'', hc'']
        have hX3' : X (toF 𝔪 σ * toF 𝔪 γ) = A 1 1 * G 1 0 := by
          rw [hX3, hc]
          simp only [zero_mul, zero_add]
          exact Xs_of_ne _ (mul_ne_zero hdσ hcg)
        have hXσ' : X (toF 𝔪 σ) = A 1 1 := by rw [hXσ, hc, Xs_zero]
        have hXγ' : X (toF 𝔪 γ) = G 1 0 := by rw [hXγ, Xs_of_ne _ hcg]
        have e1 : Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 γ'') = (Xu (toF 𝔪 σ))⁻¹ := by
          apply Units.ext
          rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, coe_Xu, coe_Xu, coe_Xu,
            hX3', hX'', hXσ']
          field_simp
        have e2 : Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 σ) = Xu (toF 𝔪 γ) := by
          apply Units.ext
          rw [Units.val_div_eq_div_val, coe_Xu, coe_Xu, coe_Xu, hX3', hXσ', hXγ']
          field_simp
        have e3 : Xu (toF 𝔪 σ * toF 𝔪 γ) / Xu (toF 𝔪 γ) = Xu (toF 𝔪 σ) := by
          apply Units.ext
          rw [Units.val_div_eq_div_val, coe_Xu, coe_Xu, coe_Xu, hX3', hXσ', hXγ']
          field_simp
        rw [e1, e2, e3, map_inv, MonoidHom.inv_apply]
        exact (P.HS_skew' 𝔪 _ _).symm
    · apply caseA
      set u : F := G 0 0 + A 1 1 / A 1 0 * G 1 0 with hu
      have hu1 : Small 𝔪 N (u - 1) := by
        have e : u - 1 = (G 0 0 - 1) + A 1 1 / A 1 0 * G 1 0 := by rw [hu]; ring
        rw [e]
        exact ha.add (Small.mono (by push_cast; omega) (hB.mul hcγ))
      have hu0 : u ≠ 0 := by
        intro h0
        have := hu1.val_eq_one hN1' v₀ hv₀
        rw [h0, map_zero] at this
        exact zero_ne_one this
      have e3 : A 1 0 * G 0 0 + A 1 1 * G 1 0 = A 1 0 * u := by
        rw [hu]; field_simp
      rw [hX3, hXσ, e3, Xs_of_ne _ (mul_ne_zero hc hu0), Xs_of_ne _ hc, mul_div_cancel_left₀ _ hc]
      exact hu1
  rw [hsig, k1] at k2
  have hσ0 := kappa_ne_zero ι P hG hz6 σ
  have hs0 := iota3_ne_zero ι (sigmaS P 𝔪 (toF 𝔪 σ) (toF 𝔪 γ))
  have k3 := mul_right_cancel₀ (inv_ne_zero hs0) k2
  exact mul_left_cancel₀ hσ0 (by rw [k3, mul_comm])

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Twisted
/-!
# WP-S, part 3: twisted sections on primitive rows

A *twisted section* (`TSection`) is MATH2's `Ψ_s = κ·Φ_s` restricted to primitive pairs of `R`:
a family `Ψ : ℂ → Row 𝔪 → ℂ`, entire in `s`, with

* `hom`: `Ψ_s(εp) = |ε|_{S_f}^{-s} Ψ_s(p)` for `ε ∈ U_S` (**no symbol**: the factor `⟨c, ε⟩` of the
  genuine section is cancelled by `κ(εp) = ⟨c, ε⟩⁻¹ κ(p)`, `kappaRow_smul`);
* `bound`: `|Ψ_s(p)| ≤ B ‖p‖^{-Re s}`, `B` uniform for `|s| ≤ M`;
* `level`: `Ψ_s(pγ) = κ(γ) Ψ_s(p)` for `γ ∈ Γ(𝔫)`, some `𝔫 ≠ 0`.

`SL₂(R)` acts by plain right translation (`TSection.translate`), with no cocycle; the
Eisenstein series `E_Ψ(P, s) = Σ_{p ∈ Row/U_S} Ψ_s(p) I_p(P)^s` then satisfies
`E_Ψ(γP) = E_{γ·Ψ}(P)` by reindexing `p ↦ pγ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Comparison of norms -/

theorem rpow_le_of_comparable {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 1 ≤ K)
    (h1 : a ≤ K * b) (h2 : b ≤ K * a) (σ : ℝ) : a ^ σ ≤ K ^ |σ| * b ^ σ := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rcases le_total 0 σ with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow hK0.le hb.le]
    exact Real.rpow_le_rpow ha.le h1 h
  · rw [abs_of_nonpos h]
    have h3 : K⁻¹ * b ≤ a := by
      rw [inv_mul_le_iff₀ hK0]; exact h2
    calc a ^ σ ≤ (K⁻¹ * b) ^ σ :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 h
      _ = K ^ (-σ) * b ^ σ := by
          rw [Real.mul_rpow (by positivity) hb.le, Real.inv_rpow hK0.le, Real.rpow_neg hK0.le]

open NumberField.HeightOneSpectrum in
/-- `∏_{v ∣ 𝔪} max |entries|_v` of a matrix `[[a,b],[c',d']]`. -/
def matS (𝔪 : Ideal (𝓞 F)) (a b c' d' : F) : ℝ :=
  ∏ v ∈ CubicPkg.sFin 𝔪, max (max (adicAbv F v a) (adicAbv F v b))
    (max (adicAbv F v c') (adicAbv F v d'))

open NumberField.HeightOneSpectrum in
theorem normS_act_le (c d a b c' d' : F) :
    normS 𝔪 (c * a + d * c') (c * b + d * d') ≤ normS 𝔪 c d * matS 𝔪 a b c' d' := by
  rw [normS, normS, matS, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => le_max_of_le_left ((adicAbv F v).nonneg _)) fun v _ => ?_
  have n := fun x : F => (adicAbv F v).nonneg x
  have hM : 0 ≤ max (adicAbv F v c) (adicAbv F v d) := le_max_of_le_left (n c)
  have t : ∀ x y z w : F, adicAbv F v x ≤ max (adicAbv F v c) (adicAbv F v d) →
      adicAbv F v z ≤ max (adicAbv F v c) (adicAbv F v d) →
      adicAbv F v y ≤ max (max (adicAbv F v a) (adicAbv F v b))
        (max (adicAbv F v c') (adicAbv F v d')) →
      adicAbv F v w ≤ max (max (adicAbv F v a) (adicAbv F v b))
        (max (adicAbv F v c') (adicAbv F v d')) →
      adicAbv F v (x * y + z * w) ≤ max (adicAbv F v c) (adicAbv F v d) *
        max (max (adicAbv F v a) (adicAbv F v b)) (max (adicAbv F v c') (adicAbv F v d')) := by
    intro x y z w hx hz hy hw
    refine (adicAbv_add_le_max F v _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_mul hx hy (n y) hM
    · rw [map_mul]; exact mul_le_mul hz hw (n w) hM
  refine max_le (t c a d c' (le_max_left _ _) (le_max_right _ _) ?_ ?_)
    (t c b d d' (le_max_left _ _) (le_max_right _ _) ?_ ?_)
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_of_le_right (le_max_right _ _)

/-- `‖p‖` for a row. -/
def Row.norm (p : Row 𝔪) : ℝ := normS 𝔪 (p.c : F) (p.d : F)

theorem Row.norm_pos (p : Row 𝔪) : 0 < p.norm := normS_pos p.ne_zero

/-- `‖pγ‖ ≍ ‖p‖` for `γ ∈ SL₂(R)` (not an equality unless `γ` is `S_f`-integral). -/
theorem Row.exists_norm_act (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ p : Row 𝔪, (p.act γ).norm ≤ K * p.norm ∧ p.norm ≤ K * (p.act γ).norm := by
  set m : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪) → ℝ := fun γ =>
    matS 𝔪 ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F)
      ((γ.1 1 1 : SInt 𝔪) : F) with hm
  have key : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (p : Row 𝔪),
      (p.act γ).norm ≤ p.norm * m γ := by
    intro γ p
    have := normS_act_le (𝔪 := 𝔪) (p.c : F) (p.d : F) ((γ.1 0 0 : SInt 𝔪) : F)
      ((γ.1 0 1 : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F) ((γ.1 1 1 : SInt 𝔪) : F)
    simpa [Row.norm] using this
  refine ⟨max 1 (max (m γ) (m γ⁻¹)), le_max_left _ _, fun p => ⟨?_, ?_⟩⟩
  · calc (p.act γ).norm ≤ p.norm * m γ := key γ p
      _ ≤ p.norm * max 1 (max (m γ) (m γ⁻¹)) :=
          mul_le_mul_of_nonneg_left (le_max_of_le_right (le_max_left _ _)) p.norm_pos.le
      _ = _ := mul_comm _ _
  · have h := key γ⁻¹ (p.act γ)
    rw [← Row.act_mul, mul_inv_cancel, Row.act_one] at h
    calc p.norm ≤ (p.act γ).norm * m γ⁻¹ := h
      _ ≤ (p.act γ).norm * max 1 (max (m γ) (m γ⁻¹)) :=
          mul_le_mul_of_nonneg_left (le_max_of_le_right (le_max_right _ _)) (p.act γ).norm_pos.le
      _ = _ := mul_comm _ _

/-! ### Twisted sections -/

/-- A **twisted section** of level some `𝔫 ≠ 0` (MATH2 `Ψ_s = κ Φ_s` on primitive pairs). -/
structure TSection (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) where
  /-- the family `s ↦ Ψ_s` -/
  toFun : ℂ → Row 𝔪 → ℂ
  hom : ∀ (s : ℂ) (ε : (SInt 𝔪)ˣ) (p : Row 𝔪),
    toFun s (ε • p) = ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s) * toFun s p
  holo : ∀ p : Row 𝔪, Differentiable ℂ fun s => toFun s p
  bound : ∀ M : ℝ, ∃ B : ℝ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ p : Row 𝔪, ‖toFun s p‖ ≤ B * p.norm ^ (-s.re)
  level : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ ∀ γ ∈ Gamma 𝔪 𝔫, ∀ (s : ℂ) (p : Row 𝔪),
    toFun s (p.act γ) = kappa ι 𝔪 γ * toFun s p

namespace TSection

variable {ι : F →+* ℂ}

instance instCoeFunForallComplexForallRow : CoeFun (TSection ι 𝔪) fun _ => ℂ → Row 𝔪 → ℂ := ⟨TSection.toFun⟩

@[ext] theorem ext {Ψ Ψ' : TSection ι 𝔪} (h : ∀ s p, Ψ s p = Ψ' s p) : Ψ = Ψ' := by
  cases Ψ; cases Ψ'
  congr
  funext s p
  exact h s p

instance instZero : Zero (TSection ι 𝔪) where
  zero :=
    { toFun := fun _ _ => 0
      hom := fun _ _ _ => by simp
      holo := fun _ => differentiable_const _
      bound := fun _ => ⟨0, fun _ _ _ => by simp⟩
      level := ⟨⊤, top_ne_bot, fun _ _ _ _ => by simp⟩ }

@[simp] theorem zero_apply (s : ℂ) (p : Row 𝔪) : (0 : TSection ι 𝔪) s p = 0 := rfl

instance instAdd : Add (TSection ι 𝔪) where
  add Ψ Ψ' :=
    { toFun := fun s p => Ψ s p + Ψ' s p
      hom := fun s ε p => by rw [Ψ.hom, Ψ'.hom, mul_add]
      holo := fun p => (Ψ.holo p).add (Ψ'.holo p)
      bound := fun M => by
        obtain ⟨B, hB⟩ := Ψ.bound M
        obtain ⟨B', hB'⟩ := Ψ'.bound M
        refine ⟨B + B', fun s hs p => (norm_add_le _ _).trans ?_⟩
        rw [add_mul]
        exact add_le_add (hB s hs p) (hB' s hs p)
      level := by
        obtain ⟨𝔫, h𝔫, h⟩ := Ψ.level
        obtain ⟨𝔫', h𝔫', h'⟩ := Ψ'.level
        refine ⟨𝔫 * 𝔫', ?_, fun γ hγ s p => ?_⟩
        · rw [← Ideal.zero_eq_bot] at h𝔫 h𝔫' ⊢
          exact mul_ne_zero h𝔫 h𝔫'
        · rw [h γ (Gamma_mono (Ideal.mul_le_left (I := 𝔫) (J := 𝔫')) hγ),
            h' γ (Gamma_mono (Ideal.mul_le_right (I := 𝔫) (J := 𝔫')) hγ), mul_add] }

@[simp] theorem add_apply (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) :
    (Ψ + Ψ') s p = Ψ s p + Ψ' s p := rfl

/-- Multiplication by an entire function of `s` (in particular by a constant). -/
def smulFun (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Ψ : TSection ι 𝔪) : TSection ι 𝔪 where
  toFun s p := f s * Ψ s p
  hom s ε p := by rw [Ψ.hom]; ring
  holo p := hf.mul (Ψ.holo p)
  bound M := by
    obtain ⟨B, hB⟩ := Ψ.bound M
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) M).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine ⟨C * B, fun s hs p => ?_⟩
    have hs' : s ∈ Metric.closedBall (0 : ℂ) M := by simpa using hs
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hC s hs') (hB s hs p) (norm_nonneg _) ((norm_nonneg _).trans (hC s hs'))
  level := by
    obtain ⟨𝔫, h𝔫, h⟩ := Ψ.level
    exact ⟨𝔫, h𝔫, fun γ hγ s p => by rw [h γ hγ]; ring⟩

@[simp] theorem smulFun_apply (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Ψ : TSection ι 𝔪) (s : ℂ)
    (p : Row 𝔪) : smulFun f hf Ψ s p = f s * Ψ s p := rfl

instance instSMulComplex : SMul ℂ (TSection ι 𝔪) where
  smul a Ψ := smulFun (fun _ => a) (differentiable_const a) Ψ

@[simp] theorem smul_apply (a : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) :
    (a • Ψ) s p = a * Ψ s p := rfl

section translate

variable (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **Right translation by `σ ∈ SL₂(R)`**: `(σ·Ψ)_s(p) = Ψ_s(pσ)`. -/
def translate (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (Ψ : TSection ι 𝔪) :
    TSection ι 𝔪 where
  toFun s p := Ψ s (p.act σ)
  hom s ε p := by rw [Row.smul_act, Ψ.hom]
  holo p := Ψ.holo _
  bound M := by
    obtain ⟨B, hB⟩ := Ψ.bound M
    obtain ⟨K, hK, hKp⟩ := Row.exists_norm_act σ
    refine ⟨|B| * K ^ M, fun s hs p => ?_⟩
    have h1 := hB s hs (p.act σ)
    have h2 := rpow_le_of_comparable (p.act σ).norm_pos p.norm_pos hK (hKp p).1 (hKp p).2 (-s.re)
    have h3 : K ^ |(-s.re)| ≤ K ^ M := by
      refine Real.rpow_le_rpow_of_exponent_le hK ?_
      rw [abs_neg]
      exact (Complex.abs_re_le_norm s).trans hs
    have hn : 0 ≤ p.norm ^ (-s.re) := Real.rpow_nonneg p.norm_pos.le _
    calc ‖Ψ s (p.act σ)‖ ≤ B * (p.act σ).norm ^ (-s.re) := h1
      _ ≤ |B| * (p.act σ).norm ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (le_abs_self B) (Real.rpow_nonneg (p.act σ).norm_pos.le _)
      _ ≤ |B| * (K ^ |(-s.re)| * p.norm ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
      _ ≤ |B| * (K ^ M * p.norm ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hn) (abs_nonneg B)
      _ = _ := by ring
  level := by
    obtain ⟨𝔫, h𝔫, h⟩ := Ψ.level
    obtain ⟨𝔫', h𝔫', h'⟩ := exists_level_conj ι P hG hz6 σ⁻¹ 𝔫 h𝔫
    refine ⟨𝔫', h𝔫', fun γ hγ s p => ?_⟩
    obtain ⟨hmem, hκ⟩ := h' γ hγ
    rw [inv_inv] at hmem hκ
    have e : (p.act γ).act σ = (p.act σ).act (σ⁻¹ * γ * σ) := by
      rw [← Row.act_mul, ← Row.act_mul]
      congr 1
      simp [mul_assoc]
    rw [e, h _ hmem, hκ]

@[simp] theorem translate_apply (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (Ψ : TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) :
    translate P hG hz6 σ Ψ s p = Ψ s (p.act σ) := rfl

end translate

end TSection

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

end ArtinKP.S
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

/-- The additive character `e(Tr z) = exp(2πi (z + z̄))` of `ℂ`. -/
def archChar (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))

theorem archChar_add (z w : ℂ) : archChar (z + w) = archChar z * archChar w := by
  unfold archChar
  rw [← Complex.exp_add, map_add]
  congr 1; ring

theorem archChar_eq_re (z : ℂ) :
    archChar z = Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)) := by
  unfold archChar
  rw [Complex.add_conj]

theorem archChar_norm (z : ℂ) : ‖archChar z‖ = 1 := by
  rw [archChar_eq_re, Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

/-! ## The Bessel form (ours, for `besselK`) -/

/-! ## The Jacquet integral -/

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.K_Char
/-! # WP-K, file 5: the global trace character factors into `archChar` at the complex places

For a totally complex number field `F` (e.g. cyclotomic with `12 ∣ n`) and `y : F`:
`Tr_{F/ℚ} y = ∑_w (σ_w y + conj (σ_w y))`, hence
`exp(−2πi Tr_{F/ℚ} y) = ∏_w archChar (−σ_w y)` — the right-hand side of the goal's `sAddChar`
(`Def_ArtinHeckeTheta`: `sAddChar 𝔪 x = exp(−2πi Tr y)` for an `S`-fractional part `y` of `x`) is
the product over the complex places of the character `archChar (−·)` used in `jacquet`.
-/

namespace ArtinKP.K

open NumberField ComplexConjugate

noncomputable section

open Classical in
theorem trace_eq_sum_places {F : Type*} [Field F] [NumberField F]
    (htc : ∀ w : InfinitePlace F, w.IsComplex) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding y + conj (w.embedding y)) := by
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ y := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ y)
      (fun σ : F →ₐ[ℚ] ℂ => σ y) (fun φ => rfl)).symm
  rw [h1, ← Finset.sum_fiberwise (Finset.univ) (fun φ : F →+* ℂ => InfinitePlace.mk φ)
    (fun φ => φ y)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    exact (InfinitePlace.isComplex_iff.1 (htc w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : (Finset.univ.filter fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at h
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [← h]
        ext x
        simp
    · rintro (h | h)
      · rw [h, InfinitePlace.mk_embedding]
      · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hfib, Finset.sum_pair hne]
  rfl

/-- `exp(−2πi Tr_{F/ℚ} y) = ∏_w archChar(−σ_w y)` for totally complex `F`. -/
theorem exp_trace_eq_prod_archChar {F : Type*} [Field F] [NumberField F]
    (htc : ∀ w : InfinitePlace F, w.IsComplex) (y : F) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) =
      ∏ w : InfinitePlace F, archChar (-(w.embedding y)) := by
  rw [trace_eq_sum_places htc, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold archChar
  congr 1
  rw [map_neg]
  ring

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_Genuine
/-!
# WP-S, part 4: genuine sections on `F² ∖ 0`

A *genuine section* (`GSection`) is MATH2's `Φ_s` (§0.2), a family of functions on pairs
`(c, d) ∈ F²`, with

* `hom` (S1): `Φ_s(εc, εd) = ⟨X(c,d), ε⟩ |ε|^{-s} Φ_s(c, d)` for `ε ∈ U_S`
  (`X(c,d) = c` if `c ≠ 0`, else `d`; on the cell `c = 0` the symbol is `⟨d, ε⟩`, which is `1` on
  primitive pairs but not on all of `F²` — this corrects MATH2 (S1) for `c = 0`);
* `cube` (S1³): `Φ_s(t³c, t³d) = |t|^{-3s} Φ_s(c, d)` for `t ∈ Fˣ`;
* `level` (S4, `S_f`-adic form): `Φ_s((c,d)γ) = σ_S((c,d), γ) Φ_s(c, d)` for all pairs and all
  `γ ∈ SL₂(F)` that are `S_f`-adically `N`-close to `1` (`IsK 𝔪 N`); the sign is the one forced
  by `kappa_mul` (exponent `-1` in A5 ⇒ exponent `+1` here);
* `holo`, `bound` as for twisted sections.

`GSection.twist : GSection → TSection` is `Ψ = κ Φ` on primitive rows.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `[[a, b], [c', d']] ∈ SL₂(F)` is `S_f`-adically `N`-close to the identity. -/
structure IsK (𝔪 : Ideal (𝓞 F)) (N : ℤ) (a b c' d' : F) : Prop where
  det : a * d' - b * c' = 1
  ha : Small 𝔪 N (a - 1)
  hb : Small 𝔪 N b
  hc : Small 𝔪 N c'
  hd : Small 𝔪 N (d' - 1)

theorem IsK.mono {N N' : ℤ} {a b c' d' : F} (h : N ≤ N') (hK : IsK 𝔪 N' a b c' d') :
    IsK 𝔪 N a b c' d' :=
  ⟨hK.det, hK.ha.mono h, hK.hb.mono h, hK.hc.mono h, hK.hd.mono h⟩

theorem isK_of_mem_Gamma {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)}
    (hγ : γ ∈ Gamma 𝔪 (𝔪 ^ N)) :
    IsK 𝔪 N ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F)
      ((γ.1 1 1 : SInt 𝔪) : F) := by
  refine ⟨det_coe γ, ?_, ?_, ?_, ?_⟩
  · have h := small_of_mem_Gamma hγ 0 0
    rwa [if_pos rfl] at h
  · have h := small_of_mem_Gamma hγ 0 1
    rwa [if_neg (by decide), sub_zero] at h
  · have h := small_of_mem_Gamma hγ 1 0
    rwa [if_neg (by decide), sub_zero] at h
  · have h := small_of_mem_Gamma hγ 1 1
    rwa [if_pos rfl] at h

/-- A **genuine section** (MATH2 §0.2, with the `S_f`-adic level condition). -/
structure GSection (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) where
  /-- the family `s ↦ Φ_s` on `F × F` -/
  toFun : ℂ → F → F → ℂ
  zero : ∀ s : ℂ, toFun s 0 0 = 0
  hom : ∀ (s : ℂ) (ε : (SInt 𝔪)ˣ) (c d : F),
    toFun s (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
      = brk ι P 𝔪 (Xs c d) ((ε : SInt 𝔪) : F) * ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s)
        * toFun s c d
  cube : ∀ (s : ℂ) (t : F), t ≠ 0 → ∀ c d : F,
    toFun s (t ^ 3 * c) (t ^ 3 * d) = ((absS 𝔪 t : ℝ) : ℂ) ^ (-(3 * s)) * toFun s c d
  level : ∃ N : ℕ, ∀ a b c' d' : F, IsK 𝔪 N a b c' d' → ∀ (s : ℂ) (c d : F),
    toFun s (c * a + d * c') (c * b + d * d') = sig ι P 𝔪 c d a b c' d' * toFun s c d
  holo : ∀ c d : F, Differentiable ℂ fun s => toFun s c d
  bound : ∀ M : ℝ, ∃ B : ℝ, ∀ s : ℂ, ‖s‖ ≤ M → ∀ c d : F,
    ‖toFun s c d‖ ≤ B * normS 𝔪 c d ^ (-s.re)

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

instance instCoeFunForallComplexForallForall : CoeFun (GSection ι P 𝔪) fun _ => ℂ → F → F → ℂ := ⟨GSection.toFun⟩

@[ext] theorem ext {Φ Φ' : GSection ι P 𝔪} (h : ∀ s c d, Φ s c d = Φ' s c d) : Φ = Φ' := by
  cases Φ; cases Φ'
  congr
  funext s c d
  exact h s c d

/-- Levels can be raised. -/
theorem level_ge (Φ : GSection ι P 𝔪) (N₀ : ℕ) : ∃ N : ℕ, N₀ ≤ N ∧
    ∀ a b c' d' : F, IsK 𝔪 N a b c' d' → ∀ (s : ℂ) (c d : F),
      Φ s (c * a + d * c') (c * b + d * d') = sig ι P 𝔪 c d a b c' d' * Φ s c d := by
  obtain ⟨N, hN⟩ := Φ.level
  exact ⟨max N N₀, le_max_right _ _, fun a b c' d' hK =>
    hN a b c' d' (hK.mono (by exact_mod_cast le_max_left N N₀))⟩

instance instZero : Zero (GSection ι P 𝔪) where
  zero :=
    { toFun := fun _ _ _ => 0
      zero := fun _ => rfl
      hom := fun _ _ _ _ => by simp
      cube := fun _ _ _ _ _ => by simp
      level := ⟨0, fun _ _ _ _ _ _ _ _ => by simp⟩
      holo := fun _ _ => differentiable_const _
      bound := fun _ => ⟨0, fun _ _ _ _ => by simp⟩ }

@[simp] theorem zero_apply (s : ℂ) (c d : F) : (0 : GSection ι P 𝔪) s c d = 0 := rfl

instance instAdd : Add (GSection ι P 𝔪) where
  add Φ Φ' :=
    { toFun := fun s c d => Φ s c d + Φ' s c d
      zero := fun s => by rw [Φ.zero, Φ'.zero, add_zero]
      hom := fun s ε c d => by rw [Φ.hom, Φ'.hom, mul_add]
      cube := fun s t ht c d => by rw [Φ.cube s t ht, Φ'.cube s t ht, mul_add]
      level := by
        obtain ⟨N, hN⟩ := Φ.level
        obtain ⟨N', -, hN'⟩ := Φ'.level_ge N
        obtain ⟨N'', hle, hN''⟩ := Φ.level_ge N'
        exact ⟨N'', fun a b c' d' hK s c d => by
          rw [hN'' a b c' d' hK, hN' a b c' d' (hK.mono (by exact_mod_cast hle)), mul_add]⟩
      holo := fun c d => (Φ.holo c d).add (Φ'.holo c d)
      bound := fun M => by
        obtain ⟨B, hB⟩ := Φ.bound M
        obtain ⟨B', hB'⟩ := Φ'.bound M
        refine ⟨B + B', fun s hs c d => (norm_add_le _ _).trans ?_⟩
        rw [add_mul]
        exact add_le_add (hB s hs c d) (hB' s hs c d) }

@[simp] theorem add_apply (Φ Φ' : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    (Φ + Φ') s c d = Φ s c d + Φ' s c d := rfl

/-- Multiplication by an entire function of `s` (in particular by a constant). -/
def smulFun (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 where
  toFun s c d := f s * Φ s c d
  zero s := by rw [Φ.zero, mul_zero]
  hom s ε c d := by rw [Φ.hom]; ring
  cube s t ht c d := by rw [Φ.cube s t ht]; ring
  level := by
    obtain ⟨N, hN⟩ := Φ.level
    exact ⟨N, fun a b c' d' hK s c d => by rw [hN a b c' d' hK]; ring⟩
  holo c d := hf.mul (Φ.holo c d)
  bound M := by
    obtain ⟨B, hB⟩ := Φ.bound M
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) M).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    refine ⟨C * B, fun s hs c d => ?_⟩
    have hs' : s ∈ Metric.closedBall (0 : ℂ) M := by simpa using hs
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hC s hs') (hB s hs c d) (norm_nonneg _) ((norm_nonneg _).trans (hC s hs'))

@[simp] theorem smulFun_apply (f : ℂ → ℂ) (hf : Differentiable ℂ f) (Φ : GSection ι P 𝔪) (s : ℂ)
    (c d : F) : smulFun f hf Φ s c d = f s * Φ s c d := rfl

instance instSMulComplex : SMul ℂ (GSection ι P 𝔪) where
  smul a Φ := smulFun (fun _ => a) (differentiable_const a) Φ

@[simp] theorem smul_apply (a : ℂ) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    (a • Φ) s c d = a * Φ s c d := rfl

/-- Bound for a section composed with an invertible linear substitution of the pair. -/
theorem bound_comp (Φ : GSection ι P 𝔪) (M : ℝ) (a b c' d' a₂ b₂ c₂ d₂ : F)
    (hinv : ∀ c d : F, (c * a + d * c') * a₂ + (c * b + d * d') * c₂ = c ∧
      (c * a + d * c') * b₂ + (c * b + d * d') * d₂ = d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ c d : F,
      ‖Φ s (c * a + d * c') (c * b + d * d')‖ ≤ B * normS 𝔪 c d ^ (-s.re) := by
  obtain ⟨B₀, hB₀⟩ := Φ.bound M
  set K : ℝ := max 1 (max (matS 𝔪 a b c' d') (matS 𝔪 a₂ b₂ c₂ d₂)) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  refine ⟨|B₀| * K ^ M, mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hK0.le _), fun s hs c d => ?_⟩
  by_cases h0 : c = 0 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [zero_mul, add_zero, Φ.zero, norm_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hK0.le _))
      (Real.rpow_nonneg (normS_nonneg _ _) _)
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
  have hcd' : c * a + d * c' ≠ 0 ∨ c * b + d * d' ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    obtain ⟨h1, h2⟩ := hinv c d
    rw [h.1, h.2] at h1 h2
    apply h0
    constructor
    · rw [← h1]; ring
    · rw [← h2]; ring
  have hp := normS_pos (𝔪 := 𝔪) hcd
  have hp' := normS_pos (𝔪 := 𝔪) hcd'
  have h1 : normS 𝔪 (c * a + d * c') (c * b + d * d') ≤ K * normS 𝔪 c d := by
    have hm : matS 𝔪 a b c' d' ≤ K := le_max_of_le_right (le_max_left _ _)
    exact ((normS_act_le c d a b c' d').trans (mul_le_mul_of_nonneg_left hm hp.le)).trans
      (le_of_eq (mul_comm _ _))
  have h2 : normS 𝔪 c d ≤ K * normS 𝔪 (c * a + d * c') (c * b + d * d') := by
    have := normS_act_le (𝔪 := 𝔪) (c * a + d * c') (c * b + d * d') a₂ b₂ c₂ d₂
    rw [(hinv c d).1, (hinv c d).2] at this
    have hm : matS 𝔪 a₂ b₂ c₂ d₂ ≤ K := le_max_of_le_right (le_max_right _ _)
    exact (this.trans (mul_le_mul_of_nonneg_left hm hp'.le)).trans (le_of_eq (mul_comm _ _))
  have h3 := rpow_le_of_comparable hp' hp hK1 h1 h2 (-s.re)
  have h4 : K ^ |(-s.re)| ≤ K ^ M := by
    refine Real.rpow_le_rpow_of_exponent_le hK1 ?_
    rw [abs_neg]
    exact (Complex.abs_re_le_norm s).trans hs
  have hn : 0 ≤ normS 𝔪 c d ^ (-s.re) := Real.rpow_nonneg hp.le _
  calc ‖Φ s (c * a + d * c') (c * b + d * d')‖
      ≤ B₀ * normS 𝔪 (c * a + d * c') (c * b + d * d') ^ (-s.re) := hB₀ s hs _ _
    _ ≤ |B₀| * normS 𝔪 (c * a + d * c') (c * b + d * d') ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (le_abs_self B₀) (Real.rpow_nonneg hp'.le _)
    _ ≤ |B₀| * (K ^ |(-s.re)| * normS 𝔪 c d ^ (-s.re)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg B₀)
    _ ≤ |B₀| * (K ^ M * normS 𝔪 c d ^ (-s.re)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hn) (abs_nonneg B₀)
    _ = _ := by ring

/-! ### The twisted section of a genuine section -/

section twist

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **`Ψ = κ·Φ` on primitive rows.**  The symbol in (S1) is exactly cancelled by
`κ(εp) = ⟨c, ε⟩⁻¹ κ(p)` (consistency of the homogeneity with A5), and the `σ_S` in the level
condition by `kappaRow_act` (A5). -/
def twist (Φ : GSection ι P 𝔪) : TSection ι 𝔪 where
  toFun s p := kappaRow ι p * Φ s (p.c : F) (p.d : F)
  hom s ε p := by
    have hc : (((ε • p).c : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (p.c : F) := by
      rw [Row.smul_c]; push_cast; rfl
    have hd : (((ε • p).d : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * (p.d : F) := by
      rw [Row.smul_d]; push_cast; rfl
    rw [hc, hd, Φ.hom, kappaRow_smul ι P hG hz6]
    have key : (brk ι P 𝔪 (p.c : F) ((ε : SInt 𝔪) : F))⁻¹
        * brk ι P 𝔪 (Xs (p.c : F) (p.d : F)) ((ε : SInt 𝔪) : F) = 1 := by
      by_cases h : (p.c : F) = 0
      · rw [h, brk_zero_left, inv_one, one_mul, Xs_zero]
        refine brk_sunit hG (fun v hv => ?_) (unit_val_eq_one ε)
        refine (p.val_or v hv).resolve_left ?_
        rw [h, map_zero]
        exact zero_ne_one
      · rw [Xs_of_ne _ h, inv_mul_cancel₀ (brk_ne_zero _ _)]
    linear_combination (kappaRow ι p * ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s)
      * Φ s (p.c : F) (p.d : F)) * key
  holo p := (differentiable_const _).mul (Φ.holo _ _)
  bound M := by
    obtain ⟨B, hB⟩ := Φ.bound M
    refine ⟨B, fun s hs p => ?_⟩
    have h1 : ‖kappaRow ι p‖ = 1 := by
      have h := congrArg norm (kappaRow_pow_three ι P hG hz6 p)
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h
    rw [norm_mul, h1, one_mul]
    exact hB s hs _ _
  level := by
    obtain ⟨N, hN⟩ := Φ.level
    refine ⟨𝔪 ^ N, pow_ne_zero N hG.ne_bot, fun γ hγ s p => ?_⟩
    have hK := isK_of_mem_Gamma hγ
    have hc : (((p.act γ).c : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)
        + (p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F) := by
      rw [Row.act_c]; push_cast; rfl
    have hd : (((p.act γ).d : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 1 : SInt 𝔪) : F)
        + (p.d : F) * ((γ.1 1 1 : SInt 𝔪) : F) := by
      rw [Row.act_d]; push_cast; rfl
    rw [hc, hd, hN _ _ _ _ hK, kappaRow_act ι P hG hz6]
    have h0 : sig ι P 𝔪 (p.c : F) (p.d : F) ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F)
        ((γ.1 1 0 : SInt 𝔪) : F) ((γ.1 1 1 : SInt 𝔪) : F) ≠ 0 := brk_ne_zero _ _
    field_simp

@[simp] theorem twist_apply (Φ : GSection ι P 𝔪) (s : ℂ) (p : Row 𝔪) :
    Φ.twist hG hz6 s p = kappaRow ι p * Φ s (p.c : F) (p.d : F) := rfl

end twist

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Ops
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

theorem Xs_add_mul (c d t : F) : Xs c (d + c * t) = Xs c d := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [Xs_of_ne _ hc, Xs_of_ne _ hc]

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Unipotent translation -/

/-- `(n(t)·Φ)_s(c, d) = Φ_s(c, d + ct)` for `t ∈ F`. -/
def nT (hG : Good 𝔪) (t : F) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 where
  toFun s c d := Φ s c (d + c * t)
  zero s := by simp [Φ.zero]
  hom s ε c d := by
    have e : ((ε : SInt 𝔪) : F) * d + ((ε : SInt 𝔪) : F) * c * t
        = ((ε : SInt 𝔪) : F) * (d + c * t) := by ring
    rw [e, Φ.hom, Xs_add_mul]
  cube s u hu c d := by
    have e : u ^ 3 * d + u ^ 3 * c * t = u ^ 3 * (d + c * t) := by ring
    rw [e, Φ.cube s u hu]
  level := by
    obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot t
    obtain ⟨N, hN⟩ := Φ.level
    refine ⟨N + 2 * B, fun a b c' d' hK s c d => ?_⟩
    have hN' : ((N + 2 * B : ℕ) : ℤ) = N + 2 * B := by push_cast; ring
    rw [hN'] at hK
    have hK₁ : IsK 𝔪 N (a - t * c') ((a - 1) * t - t * c' * t + b - t * (d' - 1)) c'
        (d' + c' * t) := by
      refine ⟨by have := hK.det; linear_combination this, ?_, ?_, hK.hc.mono (by omega), ?_⟩
      · have e : a - t * c' - 1 = (a - 1) - t * c' := by ring
        rw [e]
        exact (hK.ha.mono (by omega)).sub (Small.mono (by omega) (hB.mul hK.hc))
      · refine (((Small.mono (by omega) (hK.ha.mul hB)).sub
          (Small.mono (by omega) ((hB.mul hK.hc).mul hB))).add (hK.hb.mono (by omega))).sub
          (Small.mono (by omega) (hB.mul hK.hd))
      · have e : d' + c' * t - 1 = (d' - 1) + c' * t := by ring
        rw [e]
        exact (hK.hd.mono (by omega)).add (Small.mono (by omega) (hK.hc.mul hB))
    have h := hN _ _ _ _ hK₁ s c (d + c * t)
    have e1 : c * (a - t * c') + (d + c * t) * c' = c * a + d * c' := by ring
    have e2 : c * ((a - 1) * t - t * c' * t + b - t * (d' - 1)) + (d + c * t) * (d' + c' * t)
        = (c * b + d * d') + (c * a + d * c') * t := by ring
    have e3 : sig ι P 𝔪 c (d + c * t) (a - t * c')
        ((a - 1) * t - t * c' * t + b - t * (d' - 1)) c' (d' + c' * t)
        = sig ι P 𝔪 c d a b c' d' := by
      rw [sig, sig, e1, e2, Xs_add_mul, Xs_add_mul, Xs_add_mul]
    rw [e1, e2, e3] at h
    exact h
  holo c d := Φ.holo _ _
  bound M := by
    obtain ⟨B, -, hB⟩ := Φ.bound_comp M 1 t 0 1 1 (-t) 0 1 (fun c d => by constructor <;> ring)
    refine ⟨B, fun s hs c d => ?_⟩
    have e : Φ s c (d + c * t) = Φ s (c * 1 + d * 0) (c * t + d * 1) := by
      congr 1 <;> ring
    rw [e]
    exact hB s hs c d

@[simp] theorem nT_apply (hG : Good 𝔪) (t : F) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.nT hG t s c d = Φ s c (d + c * t) := rfl

end GSection

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

end ArtinKP.S
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

/-- A unitary additive character of `F`, continuous for the `S_f`-adic topology
(e.g. `ψ_{S_f} = ∏_{v ∣ 𝔪} ψ_v`). -/
structure SfChar (𝔪 : Ideal (𝓞 F)) where
  /-- the character -/
  toFun : F → ℂ
  map_add : ∀ x y : F, toFun (x + y) = toFun x * toFun y
  norm_one : ∀ x : F, ‖toFun x‖ = 1
  cont : ∃ M₀ : ℤ, ∀ x : F, Small 𝔪 M₀ x → toFun x = 1

instance instCoeFunSfCharForallComplex : CoeFun (SfChar 𝔪) fun _ => F → ℂ := ⟨SfChar.toFun⟩

/-- The lattice `𝔩_M = {x ∈ F : v(x) ≤ exp(-M) ∀ v ∣ 𝔪}`. -/
def lat (𝔪 : Ideal (𝓞 F)) (M : ℤ) : AddSubgroup F where
  carrier := {x | Small 𝔪 M x}
  zero_mem' := Small.zero
  add_mem' := fun hx hy => hx.add hy
  neg_mem' := fun hx => hx.neg

/-- `vol(𝔩_M) = ∏_{v ∣ 𝔪} q_v^{-M}` (Haar measure with `vol(𝓞_v) = 1`). -/
def vol (𝔪 : Ideal (𝓞 F)) (M : ℤ) : ℝ :=
  ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ (-M)

/-- The finite Fourier–Jacquet functional of a function on `F/𝔩_M`. -/
def jac (ψ : SfChar 𝔪) (M : ℤ) (f : F → ℂ) (ν : F) : ℂ :=
  (vol 𝔪 M : ℂ) * ∑' u : F ⧸ lat 𝔪 M, f u.out * (starRingEnd ℂ) (ψ (ν * u.out))

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

theorem SfChar.map_zero : ψ 0 = 1 := by
  have h := ψ.map_add 0 0
  rw [add_zero] at h
  have h0 : ψ 0 ≠ 0 := by
    intro h0
    have := ψ.norm_one 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact (mul_left_cancel₀ h0 (by rw [mul_one]; exact h)).symm

end jac

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- Every section is invariant under `n(b)` for `b` in a lattice (MATH2 (S2), uniformly in `c`). -/
theorem GSection.exists_unip (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ b : F, Small 𝔪 N b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d := by
  obtain ⟨N, hN⟩ := Φ.level
  refine ⟨N, fun b hb s c d => ?_⟩
  have hK : IsK 𝔪 N 1 b 0 1 :=
    ⟨by ring, by rw [sub_self]; exact Small.zero, hb, Small.zero, by rw [sub_self]; exact Small.zero⟩
  have h := hN 1 b 0 1 hK s c d
  have e1 : c * 1 + d * 0 = c := by ring
  have e2 : c * b + d * 1 = d + c * b := by ring
  have hsig : sig ι P 𝔪 c d 1 b 0 1 = 1 := by
    rw [sig, e1, e2, Xs_add_mul]
    by_cases hX : Xs c d = 0
    · rw [hX, zero_div, brk_zero_left]
    · rw [div_self hX, brk_one_left]
  rw [e1, e2, hsig, one_mul] at h
  exact h

/-- **The finite Jacquet functional** `λ_η(Φ_s; ν) = |η|^s ∫ Φ_s(η, ηu) conj ψ(νu) du`
(`M` must be deep enough for `Φ` and `ν`: `u ↦ Φ_s(η, ηu)` and `ψ(ν·)` are `𝔩_M`-periodic). -/
def lam (ψ : SfChar 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) (η ν : F) (s : ℂ) : ℂ :=
  ((absS 𝔪 η : ℝ) : ℂ) ^ s * jac ψ M (fun u => Φ s η (η * u)) ν

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

/-- `e_∞(x) = ∏_w archChar (-x_w)`; on `F` it is `exp(-2πi Tr)`. -/
def eInf (x : InfinitePlace F → ℂ) : ℂ := ∏ w, archChar (-(x w))

theorem eInf_add (x y : InfinitePlace F → ℂ) : eInf (x + y) = eInf x * eInf y := by
  simp only [eInf, Pi.add_apply, neg_add, archChar_add, Finset.prod_mul_distrib]

theorem norm_eInf (x : InfinitePlace F → ℂ) : ‖eInf x‖ = 1 := by
  simp only [eInf, norm_prod, archChar_norm, Finset.prod_const_one]

theorem eInf_mul_conj (x : InfinitePlace F → ℂ) : eInf x * conj (eInf x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_eInf]
  simp

theorem eInf_emb [IsTotallyComplex F] (a : F) :
    eInf (emb a) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F a : ℚ) : ℂ)) :=
  (exp_trace_eq_prod_archChar (fun w => IsTotallyComplex.isComplex w) a).symm

/-! ### The `S_f`-character -/

theorem norm_sAddChar (h𝔪 : 𝔪 ≠ ⊥) (x : F) : ‖sAddChar 𝔪 x‖ = 1 := by
  obtain ⟨y, h1, h2⟩ := B7.hasWit_all h𝔪 x
  rw [C3I.sAddChar_eq_of_wit h1 h2, Complex.norm_exp]
  simp

/-- `ψ_{S_f} = sAddChar · conj e_∞` on `F`: the product of the local characters at `v ∣ 𝔪`. -/
def psiS [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) : SfChar 𝔪 where
  toFun x := sAddChar 𝔪 x * conj (eInf (emb x))
  map_add x y := by
    rw [B7.sAddChar_add_all h𝔪, map_add, eInf_add, map_mul]
    ring
  norm_one x := by rw [norm_mul, norm_sAddChar h𝔪, RCLike.norm_conj, norm_eInf, mul_one]
  cont := ⟨0, fun x hx => by
    have h2 : ∀ v ∈ placesOf 𝔪, v.valuation F x ≤ 1 := fun v hv => by
      have := hx v hv
      simpa using this
    rw [C3I.sAddChar_eq_of_wit (y := x) (by simp) h2, ← eInf_emb, eInf_mul_conj]⟩

/-! ### The archimedean kernel -/

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.E_Series
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

/-- Nonzero classes of `R` modulo units: the index set `(R∖0)/Rˣ` of the Kubota series. -/
abbrev Cls (R : Type*) [CommRing R] : Type _ := {a : Associates R // a ≠ 0}

/-- A chosen representative of a class. -/
noncomputable def rp (a : Associates R) : R := Quot.out a

lemma mk_rp (a : Associates R) : Associates.mk (rp a) = a := Associates.quot_out a

lemma rp_ne_zero {a : Associates R} (ha : a ≠ 0) : rp a ≠ 0 := by
  intro h
  apply ha
  rw [← mk_rp a, h]
  exact Associates.mk_zero

/-! ### The norm `N(c) = #(R/cR)` -/

/-- `N(c) = #(R/cR)` as a complex number. -/
noncomputable def nrm (c : R) : ℂ := (Nat.card (R ⧸ Ideal.span {c}) : ℂ)

/-! ### Symbols -/

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

/-! ### The prime datum and the splitting (4.1′) -/

end ArtinKP.E
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

theorem small_pow_of_mem {b : 𝓞 F} (hb : b ∈ 𝔪) (n : ℕ) : Small 𝔪 n ((b : F) ^ n) := by
  intro v hv
  have hmem : b ^ n ∈ v.asIdeal ^ n := Ideal.pow_mem_pow (hv hb) n
  have := (v.intValuation_le_pow_iff_mem _ n).mpr hmem
  rw [← v.valuation_of_algebraMap (K := F)] at this
  simpa using this

/-- **Strong approximation** `F = R + 𝔩_M`. -/
theorem exists_sInt_sub_small (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) (x : F) :
    ∃ r : SInt 𝔪, Small 𝔪 M (x - (r : F)) := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  set n := M.toNat with hn
  have hβ0 : ((b : 𝓞 F) : F) ^ n ≠ 0 :=
    pow_ne_zero _ (by simpa using hb0)
  obtain ⟨y, hy1, hy2⟩ := B7.hasWit_all h𝔪 (x / ((b : 𝓞 F) : F) ^ n)
  have hβR : ((b : 𝓞 F) : F) ^ n ∈ (placesOf 𝔪).integer F := by
    have := (algebraMap (𝓞 F) (SInt 𝔪) (b ^ n)).2
    simpa using this
  refine ⟨⟨((b : 𝓞 F) : F) ^ n * (x / ((b : 𝓞 F) : F) ^ n - y), mul_mem hβR hy1⟩, ?_⟩
  have e : x - ((b : 𝓞 F) : F) ^ n * (x / ((b : 𝓞 F) : F) ^ n - y) = ((b : 𝓞 F) : F) ^ n * y := by
    field_simp
    ring
  change Small 𝔪 M (x - ((b : 𝓞 F) : F) ^ n * (x / ((b : 𝓞 F) : F) ^ n - y))
  rw [e]
  have hy : Small 𝔪 0 y := fun v hv => by
    have := hy2 v hv
    simpa using this
  have h1 : Small 𝔪 ((n : ℤ) + 0) (((b : 𝓞 F) : F) ^ n * y) := (small_pow_of_mem hb n).mul hy
  exact h1.mono (by rw [add_zero, hn]; exact Int.self_le_toNat M)

/-! ### The translation lattice -/

/-- `R ∩ 𝔩_M`. -/
def latR (𝔪 : Ideal (𝓞 F)) (M : ℤ) : AddSubgroup (SInt 𝔪) where
  carrier := {b | Small 𝔪 M (b : F)}
  zero_mem' := Small.zero
  add_mem' := fun hx hy => by
    change Small 𝔪 M _
    rw [Subalgebra.coe_add]
    exact hx.add hy
  neg_mem' := fun hx => by
    change Small 𝔪 M _
    rw [Subalgebra.coe_neg]
    exact hx.neg

/-- The embedding `R → ℂ^r`. -/
def embR : SInt 𝔪 →+ (InfinitePlace F → ℂ) where
  toFun b := emb (b : F)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem embR_apply (b : SInt 𝔪) : embR b = emb (b : F) := rfl

theorem embR_injective : Function.Injective (embR : SInt 𝔪 → InfinitePlace F → ℂ) := by
  intro a b h
  have h0 : emb ((a : F) - (b : F)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  exact Subtype.ext (sub_eq_zero.mp (emb_eq_zero h0))

/-- The translation lattice `Λ_M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`. -/
def transLat (𝔪 : Ideal (𝓞 F)) (M : ℤ) : AddSubgroup (InfinitePlace F → ℂ) :=
  (latR 𝔪 M).map (embR (𝔪 := 𝔪))

/-- `R ∩ 𝔩_M ≃ Λ_M`. -/
def latREquiv (𝔪 : Ideal (𝓞 F)) (M : ℤ) : latR 𝔪 M ≃ transLat 𝔪 M :=
  ((latR 𝔪 M).equivMapOfInjective (embR (𝔪 := 𝔪)) embR_injective).toEquiv

@[simp] theorem coe_latREquiv (M : ℤ) (b : latR 𝔪 M) :
    ((latREquiv 𝔪 M b : transLat 𝔪 M) : InfinitePlace F → ℂ) = emb ((b : SInt 𝔪) : F) := rfl

/-! ### The section -/

section sec

variable (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {c : SInt 𝔪}

include h𝔪 in
theorem exists_sec (hc : c ≠ 0) (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) :
    ∃ d : SInt 𝔪, Ideal.Quotient.mk (Ideal.span {c}) d = α ∧
      (QuotientAddGroup.mk ((d : F) / (c : F)) : F ⧸ lat 𝔪 M) = u := by
  obtain ⟨d₁, rfl⟩ := Ideal.Quotient.mk_surjective α
  obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨r, hr⟩ := exists_sInt_sub_small h𝔪 M (u₀ - (d₁ : F) / (c : F))
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  refine ⟨d₁ + c * r, ?_, ?_⟩
  · rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mem_span_singleton'.mpr ⟨r, mul_comm _ _⟩
  · rw [QuotientAddGroup.eq]
    have e : -(((d₁ + c * r : SInt 𝔪) : F) / (c : F)) + u₀ = u₀ - (d₁ : F) / (c : F) - (r : F) := by
      push_cast
      field_simp
      ring
    rw [e]
    exact hr

open Classical in
/-- A section of `d ↦ (d mod c, d/c mod 𝔩_M)` (junk for `c = 0`). -/
def sec (c : SInt 𝔪) (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) : SInt 𝔪 :=
  if hc : c = 0 then 0 else (exists_sec h𝔪 M hc α u).choose

theorem mk_sec (hc : c ≠ 0) (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) :
    Ideal.Quotient.mk (Ideal.span {c}) (sec h𝔪 M c α u) = α := by
  rw [sec, dif_neg hc]
  exact (exists_sec h𝔪 M hc α u).choose_spec.1

theorem mk_sec_div (hc : c ≠ 0) (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) :
    (QuotientAddGroup.mk ((sec h𝔪 M c α u : F) / (c : F)) : F ⧸ lat 𝔪 M) = u := by
  rw [sec, dif_neg hc]
  exact (exists_sec h𝔪 M hc α u).choose_spec.2

theorem sec_add_inj (hc : c ≠ 0) {α α' : SInt 𝔪 ⧸ Ideal.span {c}} {u u' : F ⧸ lat 𝔪 M}
    {b b' : latR 𝔪 M}
    (h : sec h𝔪 M c α u + c * (b : SInt 𝔪) = sec h𝔪 M c α' u' + c * (b' : SInt 𝔪)) :
    α = α' ∧ u = u' ∧ b = b' := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have hmk : ∀ (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) (b : latR 𝔪 M),
      Ideal.Quotient.mk (Ideal.span {c}) (sec h𝔪 M c α u + c * (b : SInt 𝔪)) = α := by
    intro α u b
    rw [← mk_sec h𝔪 M hc α u, Ideal.Quotient.eq, mk_sec h𝔪 M hc α u, add_sub_cancel_left]
    exact Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩
  have hmu : ∀ (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) (b : latR 𝔪 M),
      (QuotientAddGroup.mk (((sec h𝔪 M c α u + c * (b : SInt 𝔪) : SInt 𝔪) : F) / (c : F))
        : F ⧸ lat 𝔪 M) = u := by
    intro α u b
    have e : ((sec h𝔪 M c α u + c * (b : SInt 𝔪) : SInt 𝔪) : F) / (c : F)
        = (sec h𝔪 M c α u : F) / (c : F) + ((b : SInt 𝔪) : F) := by
      push_cast
      field_simp
    rw [e, QuotientAddGroup.mk_add, mk_sec_div h𝔪 M hc α u,
      (QuotientAddGroup.eq_zero_iff _).mpr (show ((b : SInt 𝔪) : F) ∈ lat 𝔪 M from b.2), add_zero]
  have h1 : α = α' := by rw [← hmk α u b, h, hmk α' u' b']
  have h2 : u = u' := by rw [← hmu α u b, h, hmu α' u' b']
  subst h1 h2
  exact ⟨rfl, rfl, Subtype.ext (mul_left_cancel₀ hc (add_left_cancel h))⟩

theorem sec_add_surj (hc : c ≠ 0) (d : SInt 𝔪) :
    ∃ (α : SInt 𝔪 ⧸ Ideal.span {c}) (u : F ⧸ lat 𝔪 M) (b : latR 𝔪 M),
      sec h𝔪 M c α u + c * (b : SInt 𝔪) = d := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  set α := Ideal.Quotient.mk (Ideal.span {c}) d with hα
  set u : F ⧸ lat 𝔪 M := QuotientAddGroup.mk ((d : F) / (c : F)) with hu
  have h1 := mk_sec h𝔪 M hc α u
  have h2 := mk_sec_div h𝔪 M hc α u
  rw [hα, Ideal.Quotient.eq] at h1
  obtain ⟨b₀, hb₀⟩ := Ideal.mem_span_singleton'.mp h1
  rw [hu, QuotientAddGroup.eq] at h2
  have hb : -b₀ ∈ latR 𝔪 M := by
    change Small 𝔪 M ((-b₀ : SInt 𝔪) : F)
    have e : ((-b₀ : SInt 𝔪) : F) = -((sec h𝔪 M c α u : F) / (c : F)) + (d : F) / (c : F) := by
      have h3 := congrArg (fun z : SInt 𝔪 => (z : F)) hb₀
      simp only [Subalgebra.coe_mul, Subalgebra.coe_sub] at h3
      rw [Subalgebra.coe_neg]
      field_simp
      linear_combination -h3
    rw [e]
    exact h2
  refine ⟨α, u, ⟨-b₀, hb⟩, ?_⟩
  change sec h𝔪 M c α u + c * -b₀ = d
  linear_combination -hb₀

end sec

/-! ### The index equivalence -/

/-- The index set of the unfolded sum: `(c mod units, d mod c, d/c mod 𝔩_M)`. -/
abbrev IdxI (𝔪 : Ideal (𝓞 F)) (M : ℤ) : Type _ :=
  (Σ a : Cls (SInt 𝔪), SInt 𝔪 ⧸ Ideal.span {rp a.1}) × (F ⧸ lat 𝔪 M)

/-- `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)`. -/
def thetaFun (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) (p : IdxI 𝔪 M × latR 𝔪 M) : Cls (SInt 𝔪) × SInt 𝔪 :=
  (p.1.1.1, sec h𝔪 M (rp p.1.1.1.1) p.1.1.2 p.1.2 + rp p.1.1.1.1 * (p.2 : SInt 𝔪))

theorem thetaFun_bijective (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) : Function.Bijective (thetaFun h𝔪 M) := by
  constructor
  · rintro ⟨⟨⟨a, α⟩, u⟩, b⟩ ⟨⟨⟨a', α'⟩, u'⟩, b'⟩ h
    simp only [thetaFun, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := sec_add_inj h𝔪 M (rp_ne_zero a.2) h2
    rfl
  · rintro ⟨a, d⟩
    obtain ⟨α, u, b, h⟩ := sec_add_surj h𝔪 M (rp_ne_zero a.2) d
    exact ⟨⟨⟨⟨a, α⟩, u⟩, b⟩, by simp only [thetaFun, h]⟩

/-- MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`, for all `c` at once. -/
def thetaEquiv (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) : IdxI 𝔪 M × latR 𝔪 M ≃ Cls (SInt 𝔪) × SInt 𝔪 :=
  Equiv.ofBijective _ (thetaFun_bijective h𝔪 M)

@[simp] theorem thetaEquiv_apply (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) (p : IdxI 𝔪 M × latR 𝔪 M) :
    thetaEquiv h𝔪 M p = thetaFun h𝔪 M p := rfl

/-! ### Rows with `c ≠ 0` modulo units -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Symbol
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply
/-!
# WP-S2, part 4: the cubic symbol of `R = SInt 𝔪` as a `B7.CubicSymbol`, and its `E.Pairing`

* `isCoprime_of_val`: elements of `R` without a common exterior prime are coprime
  (`E.val_of_isCoprime` is the converse).
* `cubicExt_eq_zero_iff`: `(d/c) = 0 ↔ ¬ IsCoprime d c` for `c ≠ 0`.
* `cubicSymbol ι P hG hz6 : B7.CubicSymbol (SInt 𝔪)` with `sym d c = A.cubicExt ι 𝔪 d c`
  (WP-E open issue 1), `cubicSymbol_gen` (the hypothesis `hS` of `E_Link`), and
  `pairing : E.Pairing (cubicSymbol …)` (`E.pairingHS`).
* `span_rowElt` (WP-E open issue 5).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section symbol

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **WP-A's exterior cubic symbol as a `B7.CubicSymbol (SInt 𝔪)`** (WP-E open issue 1). -/
def cubicSymbol : CubicSymbol (SInt 𝔪) where
  sym := cubicExt ι 𝔪
  sym_mul_left d d' c hc := by
    by_cases h : IsCoprime d c ∧ IsCoprime d' c
    · exact cubicExt_mul_left ι P hG hz6 c d d' hc
        (fun v hv hne => (val_of_isCoprime h.1 v hv).resolve_right hne)
        (fun v hv hne => (val_of_isCoprime h.2 v hv).resolve_right hne)
    · have h0 : cubicExt ι 𝔪 (d * d') c = 0 :=
        (cubicExt_eq_zero_iff ι P hG hz6 _ c hc).mpr fun hcop =>
          h ⟨IsCoprime.of_mul_left_left hcop, IsCoprime.of_mul_left_right hcop⟩
      rw [h0]
      rw [not_and_or] at h
      rcases h with h | h
      · rw [(cubicExt_eq_zero_iff ι P hG hz6 d c hc).mpr h, zero_mul]
      · rw [(cubicExt_eq_zero_iff ι P hG hz6 d' c hc).mpr h, mul_zero]
  sym_mul_right d c c' hc hc' := by
    by_cases h : IsCoprime d c ∧ IsCoprime d c'
    · by_cases hd : d = 0
      · have hu : IsUnit c := by have := h.1; rwa [hd, isCoprime_zero_left] at this
        have hu' : IsUnit c' := by have := h.2; rwa [hd, isCoprime_zero_left] at this
        rw [cubicExt_of_unit_right ι d c (val_eq_one_of_isUnit hu),
          cubicExt_of_unit_right ι d c' (val_eq_one_of_isUnit hu'),
          cubicExt_of_unit_right ι d (c * c') (val_eq_one_of_isUnit (hu.mul hu')), one_mul]
      · exact cubicExt_mul_right ι P hG hz6 c c' d hc hc' hd
          (fun v hv hne => (val_of_isCoprime h.1 v hv).resolve_right hne)
          (fun v hv hne => (val_of_isCoprime h.2 v hv).resolve_right hne)
    · have h0 : cubicExt ι 𝔪 d (c * c') = 0 :=
        (cubicExt_eq_zero_iff ι P hG hz6 d _ (mul_ne_zero hc hc')).mpr fun hcop =>
          h ⟨IsCoprime.of_mul_right_left hcop, IsCoprime.of_mul_right_right hcop⟩
      rw [h0]
      rw [not_and_or] at h
      rcases h with h | h
      · rw [(cubicExt_eq_zero_iff ι P hG hz6 d c hc).mpr h, zero_mul]
      · rw [(cubicExt_eq_zero_iff ι P hG hz6 d c' hc').mpr h, mul_zero]
  sym_congr d d' c hc hdvd :=
    cubicExt_congr ι hG c d d' hc (Ideal.mem_span_singleton.mpr hdvd)
  sym_eq_zero_iff d c hc := cubicExt_eq_zero_iff ι P hG hz6 d c hc
  sym_pow_three d c hc hcop := by
    by_cases hd : d = 0
    · have hu : IsUnit c := by rwa [hd, isCoprime_zero_left] at hcop
      rw [cubicExt_of_unit_right ι d c (val_eq_one_of_isUnit hu), one_pow]
    · exact cubicExt_pow_three ι P hG hz6 c d hc hd
        (fun v hv hne => (val_of_isCoprime hcop v hv).resolve_right hne)
  sym_unit_right d c hu := cubicExt_of_unit_right ι d c (val_eq_one_of_isUnit hu)

@[simp] theorem cubicSymbol_sym (d c : SInt 𝔪) :
    (cubicSymbol ι P hG hz6).sym d c = cubicExt ι 𝔪 d c := rfl

end symbol

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.RO_Ring
/-! # WP-RO, file 1: the ring of `S`-integers is a PID; `SBezout`

`SOf 𝔪 : Finset (FinitePlace F)` is the set of finite places dividing `𝔪`, in the form used by
WP-B1.  For `𝔪 ≠ ⊥`, `B1.IsSInt (SOf 𝔪)` is membership in `SInt 𝔪` (`isSInt_SOf_iff`), so
`B1.SIntRing (SOf 𝔪) ≃+* SInt 𝔪` (`sIntEquiv`).

* `isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪)`: every ideal of `SInt 𝔪`
  is extended from `𝓞 F` (clear denominators by an `S`-unit, `B1.exists_unit_rescale`), and extended
  ideals are principal (`Good.principal`).
* `isPrincipalIdealRing_SIntRing`, `sBezout (hG : Good 𝔪) : B1.SBezout (SOf 𝔪)`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

open scoped Classical in
/-- The finite places dividing `𝔪`, as a finset of `FinitePlace F` (the `S` of WP-B1). -/
def SOf (𝔪 : Ideal (𝓞 F)) : Finset (FinitePlace F) := (CubicPkg.sFin 𝔪).image FinitePlace.mk

theorem coe_sFin (h𝔪 : 𝔪 ≠ ⊥) :
    ((CubicPkg.sFin 𝔪 : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))) =
      placesOf 𝔪 := by
  ext v
  rw [Finset.mem_coe, CubicPkg.mem_sFin h𝔪]
  rfl

/-- `B1.IsSInt (SOf 𝔪)` is membership in `SInt 𝔪`. -/
theorem isSInt_SOf_iff (h𝔪 : 𝔪 ≠ ⊥) (a : F) :
    IsSInt (SOf 𝔪) a ↔ a ∈ (placesOf 𝔪).integer F := by
  rw [SOf, isSInt_image_iff, coe_sFin h𝔪]

theorem isSInt_coe (h𝔪 : 𝔪 ≠ ⊥) (a : SInt 𝔪) : IsSInt (SOf 𝔪) (a : F) :=
  (isSInt_SOf_iff h𝔪 _).mpr a.2

/-- The identification of the two models of `R = 𝓞_S`. -/
def sIntEquiv (h𝔪 : 𝔪 ≠ ⊥) : SInt 𝔪 ≃+* SIntRing (SOf 𝔪) where
  toFun a := ⟨(a : F), isSInt_coe h𝔪 a⟩
  invFun a := ⟨(a : F), (isSInt_SOf_iff h𝔪 _).mp a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_sIntEquiv (h𝔪 : 𝔪 ≠ ⊥) (a : SInt 𝔪) : ((sIntEquiv h𝔪 a : SIntRing (SOf 𝔪)) : F) = a :=
  rfl

@[simp] theorem coe_sIntEquiv_symm (h𝔪 : 𝔪 ≠ ⊥) (a : SIntRing (SOf 𝔪)) :
    (((sIntEquiv h𝔪).symm a : SInt 𝔪) : F) = a := rfl

/-- Conversely an `S`-unit of `F` is (the coercion of) a unit of `SInt 𝔪`. -/
theorem exists_unit_of_isSUnit (h𝔪 : 𝔪 ≠ ⊥) {u : F} (hu : IsSUnit (SOf 𝔪) u) :
    ∃ ε : (SInt 𝔪)ˣ, ((ε : SInt 𝔪) : F) = u := by
  refine ⟨⟨⟨u, (isSInt_SOf_iff h𝔪 _).mp hu.isSInt⟩, ⟨u⁻¹, (isSInt_SOf_iff h𝔪 _).mp hu.inv.isSInt⟩,
    ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hu.1)
  · exact Subtype.ext (inv_mul_cancel₀ hu.1)

/-- Every element of `SInt 𝔪` is an integer divided by an integer which is an `S`-unit. -/
theorem exists_unit_mul_eq_int (h𝔪 : 𝔪 ≠ ⊥) (x : SInt 𝔪) :
    ∃ (ε : (SInt 𝔪)ˣ) (a : 𝓞 F), (ε : SInt 𝔪) * x = algebraMap (𝓞 F) (SInt 𝔪) a := by
  by_cases hx : (x : F) = 0
  · refine ⟨1, 0, ?_⟩
    have : x = 0 := Subtype.ext hx
    simp [this]
  obtain ⟨_, _, hres⟩ := exists_unit_rescale (SOf 𝔪)
  obtain ⟨u, hu0, huS, ⟨c', -, hc', -⟩, -⟩ := hres (x : F) 0 (Or.inl hx) (isSInt_coe h𝔪 x)
    (fun v _ => by simp)
  obtain ⟨ε, hε⟩ := exists_unit_of_isSUnit h𝔪 (u := u) ⟨hu0, huS⟩
  refine ⟨ε, c', Subtype.ext ?_⟩
  change ((ε : SInt 𝔪) : F) * (x : F) = algebraMap (𝓞 F) F c'
  rw [hε]
  exact hc'.symm

/-- Every ideal of `SInt 𝔪` is extended from `𝓞 F`. -/
theorem map_comap_eq (h𝔪 : 𝔪 ≠ ⊥) (J : Ideal (SInt 𝔪)) :
    (J.comap (algebraMap (𝓞 F) (SInt 𝔪))).map (algebraMap (𝓞 F) (SInt 𝔪)) = J := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  obtain ⟨ε, a, ha⟩ := exists_unit_mul_eq_int h𝔪 x
  have hmem : a ∈ J.comap (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.mem_comap, ← ha]
    exact J.mul_mem_left _ hx
  have hx' : x = ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * algebraMap (𝓞 F) (SInt 𝔪) a := by
    rw [← ha, ← mul_assoc, ε.inv_mul, one_mul]
  rw [hx']
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)

end

end ArtinKP.RO
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

theorem exists_ext (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    ∃ 𝔄 : Ideal (𝓞 F), IsExterior 𝔪 𝔄 ∧
      𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {c} := by
  have hJ := RO.map_comap_eq h𝔪 (Ideal.span {c})
  have h0 : (Ideal.span {c}).comap (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hJ
    exact hc (Ideal.span_singleton_eq_bot.mp hJ.symm)
  obtain ⟨𝔄, hE, hmap⟩ := B7.exists_exterior_map_eq 𝔪 h𝔪 _ h0
  exact ⟨𝔄, hE, by rw [← hmap, hJ]⟩

/-- The exterior ideal of a nonzero `S`-integer. -/
def extOf (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) : Ideal (𝓞 F) := (exists_ext h𝔪 hc).choose

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

/-! ### Depth -/

open Classical in
/-- The pole order of `x` at `v` (`0` if `x` is `v`-integral). -/
def dep (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℕ := if x = 0 then 0 else (-ordv v x).toNat

end ArtinKP.RF
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

/-- `#(R/cR)` as a real number. -/
def nrmR (c : SInt 𝔪) : ℝ := (Nat.card (SInt 𝔪 ⧸ Ideal.span {c}) : ℝ)

/-! ### The integral of one member of the family -/

/-! ### Summation -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Lattice
/-!
# WP-S2, part 5: lattices with a depth function; the Kirillov function as a Jacquet functional

* `SmallD 𝔪 k x`: `v(x) ≤ exp(-k v)` at every `v ∣ 𝔪`, for a depth function
  `k : HeightOneSpectrum (𝓞 F) → ℤ`; `latD 𝔪 k`, `volD 𝔪 k`, `jacD ψ k f ν`, `lamD`.
  For a constant depth these are `Small`, `lat`, `vol`, `jac`, `lam` of WP-S, by `rfl`.
* `smallD_mul_iff`: `β · 𝔩_k = 𝔩_{k + ord β}`; `absS_eq_prod`: `|β|_{S_f} = ∏ q_v^{-ord_v β}`.
* `jacD_subst`: the substitution `u = β u'`,
  `∫ g(u/β) conj ψ(νu) du = |β| ∫ g(u') conj ψ(νβu') du'`.
* `kir_eq_lamD` (**MATH2 Lemma 6.1 (iii)** / §6.3): `kir ψ M Φ η β s = λ_η((Ã(β)Φ)_s; 1)`, the
  functional on the right taken on the lattice `β 𝔩_M` (depth `M + ord_v β`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `v(x) ≤ exp(-k v)` at every finite place `v` of `S`. -/
def SmallD (𝔪 : Ideal (𝓞 F)) (k : HeightOneSpectrum (𝓞 F) → ℤ) (x : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F x ≤ WithZero.exp (-(k v))

namespace SmallD

variable {k k' : HeightOneSpectrum (𝓞 F) → ℤ} {x y : F}

theorem zero : SmallD 𝔪 k (0 : F) := fun v _ => by simp

theorem add (hx : SmallD 𝔪 k x) (hy : SmallD 𝔪 k y) : SmallD 𝔪 k (x + y) := fun v hv =>
  (Valuation.map_add _ x y).trans (max_le (hx v hv) (hy v hv))

theorem neg (hx : SmallD 𝔪 k x) : SmallD 𝔪 k (-x) := fun v hv => by
  rw [Valuation.map_neg]; exact hx v hv

theorem mono (h : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → k v ≤ k' v)
    (hx : SmallD 𝔪 k' x) : SmallD 𝔪 k x := fun v hv =>
  (hx v hv).trans (WithZero.exp_le_exp.mpr (by have := h v hv; omega))

end SmallD

/-- The lattice `𝔩_k = {x ∈ F : v(x) ≤ exp(-k v) ∀ v ∣ 𝔪}`. -/
def latD (𝔪 : Ideal (𝓞 F)) (k : HeightOneSpectrum (𝓞 F) → ℤ) : AddSubgroup F where
  carrier := {x | SmallD 𝔪 k x}
  zero_mem' := SmallD.zero
  add_mem' := fun hx hy => hx.add hy
  neg_mem' := fun hx => hx.neg

/-- `vol(𝔩_k) = ∏_{v ∣ 𝔪} q_v^{-k v}`. -/
def volD (𝔪 : Ideal (𝓞 F)) (k : HeightOneSpectrum (𝓞 F) → ℤ) : ℝ :=
  ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k v))

/-- The finite Fourier–Jacquet functional on `F/𝔩_k`. -/
def jacD (ψ : SfChar 𝔪) (k : HeightOneSpectrum (𝓞 F) → ℤ) (f : F → ℂ) (ν : F) : ℂ :=
  (volD 𝔪 k : ℂ) * ∑' u : F ⧸ latD 𝔪 k, f u.out * (starRingEnd ℂ) (ψ (ν * u.out))

theorem jacD_const (ψ : SfChar 𝔪) (M : ℤ) (f : F → ℂ) (ν : F) :
    jacD ψ (fun _ => M) f ν = jac ψ M f ν := rfl

section jacD

variable (ψ : SfChar 𝔪) {k : HeightOneSpectrum (𝓞 F) → ℤ} {f : F → ℂ} {ν : F}

theorem outD_spec (x : F) :
    ∃ h : F, SmallD 𝔪 k h ∧ (QuotientAddGroup.mk x : F ⧸ latD 𝔪 k).out = x + h := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (latD 𝔪 k) x
  exact ⟨h.1, h.2, hh⟩

/-- The summand of `jacD` on the class of `x`, for periodic data. -/
theorem jacD_term (hf : ∀ x h : F, SmallD 𝔪 k h → f (x + h) = f x)
    (hψ : ∀ h : F, SmallD 𝔪 k h → ψ (ν * h) = 1) (x : F) :
    f (QuotientAddGroup.mk x : F ⧸ latD 𝔪 k).out
        * (starRingEnd ℂ) (ψ (ν * (QuotientAddGroup.mk x : F ⧸ latD 𝔪 k).out))
      = f x * (starRingEnd ℂ) (ψ (ν * x)) := by
  obtain ⟨h, hh, he⟩ := outD_spec (𝔪 := 𝔪) (k := k) x
  rw [he, hf x h hh, mul_add, ψ.map_add, hψ h hh, mul_one]

end jacD

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- `λ_η(Φ_s; ν)` on the lattice of depth function `k`. -/
def lamD (ψ : SfChar 𝔪) (k : HeightOneSpectrum (𝓞 F) → ℤ) (Φ : GSection ι P 𝔪) (η ν : F)
    (s : ℂ) : ℂ :=
  ((absS 𝔪 η : ℝ) : ℂ) ^ s * jacD ψ k (fun u => Φ s η (η * u)) ν

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Index
/-!
# WP-S2, part 7: the index of `𝔩_{k'}` in `𝔩_k`; independence of the valid depth

* `exists_val_eq`: an element of `F` with prescribed valuations at the places of `S_f` (CRT).
* `exists_approx`: an `S_f`-integral `x ∈ F` is approximated by integers of `F` at the places of
  `S_f` (through `L2B.exists_sub_mem_map` for the auxiliary modulus `∏_{w : pole of x} w`).
* `card_latD_quot`: `[𝔩_k : 𝔩_{k'}] = ∏_{v ∣ 𝔪} q_v^{k' v - k v}` for `k ≤ k'`
  (`𝔩_k/𝔩_{k'} ≅ 𝓞/∏ v^{k'-k}`).
* `jacD_eq_of_le`: **the finite Jacquet functional does not depend on the valid depth**
  (unconditionally: if the series diverges both sides are `0`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Prescribed valuations -/

theorem exists_int_val (𝔪 : Ideal (𝓞 F)) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ y : 𝓞 F, y ≠ 0 ∧ ∀ v ∈ CubicPkg.sFin 𝔪, v.intValuation y = WithZero.exp (-(n v : ℤ)) := by
  classical
  by_cases hE : CubicPkg.sFin 𝔪 = ∅
  · exact ⟨1, one_ne_zero, fun v hv => by rw [hE] at hv; simp at hv⟩
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  choose ϖ hϖ using fun v : HeightOneSpectrum (𝓞 F) => v.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := CubicPkg.sFin 𝔪)
    (fun v => v.asIdeal) (fun v => n v + 1) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => ϖ v.1 ^ n v.1)
  have key : ∀ v ∈ CubicPkg.sFin 𝔪, v.intValuation y = WithZero.exp (-(n v : ℤ)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).mpr (hy v hv)
    have h2 : v.intValuation (ϖ v ^ n v) = WithZero.exp (-(n v : ℤ)) := by
      rw [map_pow, hϖ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have h3 : v.intValuation (y - ϖ v ^ n v) < v.intValuation (ϖ v ^ n v) := by
      rw [h2]
      refine h1.trans_lt ?_
      rw [WithZero.exp_lt_exp]
      push_cast
      omega
    have e : y = (y - ϖ v ^ n v) + ϖ v ^ n v := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ h3, h2]
  refine ⟨y, ?_, key⟩
  rintro rfl
  have := key v₀ hv₀
  rw [map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- An element of `F` with `v(t) = exp(-k v)` at every `v ∣ 𝔪`. -/
theorem exists_val_eq (𝔪 : Ideal (𝓞 F)) (k : HeightOneSpectrum (𝓞 F) → ℤ) :
    ∃ t : F, t ≠ 0 ∧ ∀ v ∈ CubicPkg.sFin 𝔪, v.valuation F t = WithZero.exp (-(k v)) := by
  obtain ⟨y₁, hy₁0, hy₁⟩ := exists_int_val 𝔪 fun v => (k v).toNat
  obtain ⟨y₂, hy₂0, hy₂⟩ := exists_int_val 𝔪 fun v => (-(k v)).toNat
  have h1 : algebraMap (𝓞 F) F y₁ ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have h2 : algebraMap (𝓞 F) F y₂ ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  refine ⟨algebraMap (𝓞 F) F y₁ / algebraMap (𝓞 F) F y₂, div_ne_zero h1 h2, fun v hv => ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, hy₁ v hv, hy₂ v hv, ← WithZero.exp_sub]
  congr 1
  omega

/-! ### Approximation by integers -/

theorem val_le_of_mem_map_pow {𝔪' : Ideal (𝓞 F)} (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ 𝔪' ≤ v.asIdeal) (n : ℕ) {z : SInt 𝔪'}
    (hz : z ∈ (v.asIdeal ^ n).map (algebraMap (𝓞 F) (SInt 𝔪'))) :
    v.valuation F (z : F) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt, HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem a n).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ ≤ _ := by rw [one_mul]; exact hx

/-- **Approximation at `S_f`**: an element of `F` integral at the places of `S_f` is congruent
to an integer of `F` modulo any prescribed powers of these places. -/
theorem exists_approx (h𝔪 : 𝔪 ≠ ⊥) (x : F)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F x ≤ 1)
    (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ a : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F (x - algebraMap (𝓞 F) F a) ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨0, fun v _ => by simp [hx0]⟩
  set T := CubicPkg.extSupp 𝔪 x with hTdef
  set 𝔪' : Ideal (𝓞 F) := ∏ w ∈ T, w.asIdeal with h𝔪'
  set 𝔞 : Ideal (𝓞 F) := ∏ v ∈ CubicPkg.sFin 𝔪, v.asIdeal ^ n v with h𝔞
  have hT : ∀ w ∈ T, ¬ 𝔪 ≤ w.asIdeal := fun w hw => ((CubicPkg.mem_extSupp hx0 w).mp hw).1
  have hle : ∀ w ∈ T, 𝔪' ≤ w.asIdeal := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hw)
  have hnot : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → ¬ 𝔪' ≤ v.asIdeal := by
    intro v hv hle'
    obtain ⟨w, hw, hwv⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp hle'
    have e : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hwv
    exact hT w hw (e ▸ hv)
  have hxint : x ∈ (placesOf 𝔪').integer F := by
    intro w hw
    by_cases hS : 𝔪 ≤ w.asIdeal
    · exact hx w hS
    · by_contra hne
      have hwT : w ∈ T := (CubicPkg.mem_extSupp hx0 w).mpr ⟨hS, fun h1 => hne (le_of_eq h1)⟩
      exact hw (hle w hwT)
  have hcop : 𝔞 ⊔ 𝔪' = ⊤ := by
    by_contra hne
    obtain ⟨Mx, hMx, hJ⟩ := Ideal.exists_le_maximal _ hne
    haveI hp : Mx.IsPrime := hMx.isPrime
    obtain ⟨v, hv, hvM⟩ := (Ideal.IsPrime.prod_le hp).mp (le_sup_left.trans hJ)
    obtain ⟨w, hw, hwM⟩ := (Ideal.IsPrime.prod_le hp).mp (le_sup_right.trans hJ)
    have hv' : v.asIdeal ≤ Mx := Ideal.IsPrime.le_of_pow_le hvM
    have e1 : v.asIdeal = Mx := v.isMaximal.eq_of_le hMx.ne_top hv'
    have e2 : w.asIdeal = Mx := w.isMaximal.eq_of_le hMx.ne_top hwM
    refine hT w hw ?_
    rw [e2, ← e1]
    exact (CubicPkg.mem_sFin h𝔪 v).mp hv
  obtain ⟨c, hc⟩ := L2B.exists_sub_mem_map (𝔪 := 𝔪') 𝔞 hcop ⟨x, hxint⟩
  refine ⟨c, fun v hv => ?_⟩
  have hvs := (CubicPkg.mem_sFin h𝔪 v).mpr hv
  have h𝔞v : 𝔞 ≤ v.asIdeal ^ n v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hvs)
  exact val_le_of_mem_map_pow v (hnot v hv) (n v) (Ideal.map_mono h𝔞v hc)

/-! ### The index -/

/-- **`[𝔩_k : 𝔩_{k'}] = ∏_{v ∣ 𝔪} q_v^{k' v - k v}`** for `k ≤ k'`. -/
theorem card_latD_quot (h𝔪 : 𝔪 ≠ ⊥) {k k' : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → k v ≤ k' v) :
    Nat.card (latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k))
      = ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (k' v - k v).toNat := by
  classical
  obtain ⟨t, ht0, ht⟩ := exists_val_eq 𝔪 k
  have ht' : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F t = WithZero.exp (-(k v)) := fun v hv => ht v ((CubicPkg.mem_sFin h𝔪 v).mpr hv)
  set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (k' v - k v).toNat with hn
  set 𝔞 : Ideal (𝓞 F) := ∏ v ∈ CubicPkg.sFin 𝔪, v.asIdeal ^ n v with h𝔞
  have hmem : ∀ a : 𝓞 F, algebraMap (𝓞 F) F a * t ∈ latD 𝔪 k := by
    intro a v hv
    rw [map_mul, ht' v hv]
    exact mul_le_of_le_one_left' (v.valuation_le_one a)
  let θ₀ : 𝓞 F →+ latD 𝔪 k :=
    { toFun := fun a => ⟨algebraMap (𝓞 F) F a * t, hmem a⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [add_mul] }
  let θ : 𝓞 F →+ latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k) :=
    (QuotientAddGroup.mk' _).comp θ₀
  have h𝔞inf : 𝔞 = (CubicPkg.sFin 𝔪).inf fun v => v.asIdeal ^ n v :=
    (IsDedekindDomain.inf_pow_eq_prod_of_prime _ _ _ (fun v _ => v.prime)
      (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))).symm
  have hker : ∀ a : 𝓞 F, θ a = 0 ↔ a ∈ 𝔞 := by
    intro a
    have e1 : θ a = 0 ↔ algebraMap (𝓞 F) F a * t ∈ latD 𝔪 k' := by
      change (QuotientAddGroup.mk (θ₀ a) : latD 𝔪 k ⧸ _) = 0 ↔ _
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact Iff.rfl
    rw [e1, h𝔞inf, Submodule.mem_finsetInf]
    by_cases ha : a = 0
    · subst ha
      simp [(latD 𝔪 k').zero_mem]
    have haF : algebraMap (𝓞 F) F a ≠ 0 := by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    have hone : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
        (v.valuation F (algebraMap (𝓞 F) F a * t) ≤ WithZero.exp (-(k' v))
          ↔ a ∈ v.asIdeal ^ n v) := by
      intro v hv
      rw [← v.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
        map_mul, ht' v hv, val_eq_exp_ordv v haF, ← WithZero.exp_add, WithZero.exp_le_exp,
        WithZero.exp_le_exp]
      have := hk v hv
      constructor <;> intro h <;> simp only [hn] at h ⊢ <;> omega
    constructor
    · intro h v hv
      exact (hone v ((CubicPkg.mem_sFin h𝔪 v).mp hv)).mp (h v ((CubicPkg.mem_sFin h𝔪 v).mp hv))
    · intro h v hv
      exact (hone v hv).mpr (h v ((CubicPkg.mem_sFin h𝔪 v).mpr hv))
  have hsurj : Function.Surjective θ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H l =>
      have hl : SmallD 𝔪 k (l : F) := l.2
      have hx : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
          v.valuation F ((l : F) / t) ≤ 1 := by
        intro v hv
        rw [div_eq_mul_inv, map_mul, map_inv₀, ht' v hv, ← WithZero.exp_neg, neg_neg]
        calc v.valuation F (l : F) * WithZero.exp (k v)
            ≤ WithZero.exp (-(k v)) * WithZero.exp (k v) := mul_le_mul_left (hl v hv) _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      obtain ⟨a, ha⟩ := exists_approx h𝔪 ((l : F) / t) hx n
      refine ⟨a, ?_⟩
      change (QuotientAddGroup.mk (θ₀ a) : latD 𝔪 k ⧸ _) = QuotientAddGroup.mk l
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      intro v hv
      have e : ((-(θ₀ a) + l : latD 𝔪 k) : F) = t * ((l : F) / t - algebraMap (𝓞 F) F a) := by
        change -(algebraMap (𝓞 F) F a * t) + (l : F) = _
        field_simp
        ring
      rw [e, map_mul, ht' v hv]
      have h2 := ha v hv
      have h3 : WithZero.exp (-(k' v)) = WithZero.exp (-(k v)) * WithZero.exp (-(n v : ℤ)) := by
        rw [← WithZero.exp_add]
        congr 1
        have := hk v hv
        simp only [hn]
        omega
      rw [h3]
      exact mul_le_mul_right h2 _
  have hkereq : θ.ker = 𝔞.toAddSubgroup := by
    ext a
    rw [AddMonoidHom.mem_ker, hker]
    rfl
  have e1 : Nat.card (latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k))
      = Nat.card (𝓞 F ⧸ θ.ker) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective θ hsurj).symm.toEquiv
  have e2 : Nat.card (𝓞 F ⧸ θ.ker) = Nat.card (𝓞 F ⧸ 𝔞.toAddSubgroup) :=
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hkereq).toEquiv
  have e3 : Nat.card (𝓞 F ⧸ 𝔞.toAddSubgroup) = Ideal.absNorm 𝔞 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e1, e2, e3, h𝔞, map_prod]
  exact Finset.prod_congr rfl fun v _ => map_pow _ _ _

/-! ### Independence of the valid depth -/

theorem tsum_prod_const_snd {α β : Type*} [Fintype β] [Nonempty β] (G : α → ℂ) :
    ∑' p : α × β, G p.1 = (Fintype.card β : ℂ) * ∑' a, G a := by
  by_cases hG : Summable G
  · have hn : Summable (fun p : α × β => ‖G p.1‖) := by
      rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
      refine ⟨fun x => (hasSum_fintype _).summable, ?_⟩
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact (summable_norm_iff.mpr hG).mul_left _
    have hs : Summable (fun p : α × β => G p.1) := Summable.of_norm hn
    rw [hs.tsum_prod]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [tsum_mul_left]
  · rw [tsum_eq_zero_of_not_summable hG, mul_zero]
    apply tsum_eq_zero_of_not_summable
    intro hs
    obtain ⟨b₀⟩ := ‹Nonempty β›
    exact hG (hs.comp_injective (i := fun a : α => (a, b₀)) fun a a' h => (Prod.mk.inj h).1)

/-- **Independence of the valid depth**: for `k ≤ k'`, data periodic under `𝔩_k` have the same
functional on `F/𝔩_{k'}` as on `F/𝔩_k`. -/
theorem jacD_eq_of_le (ψ : SfChar 𝔪) (h𝔪 : 𝔪 ≠ ⊥) {k k' : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → k v ≤ k' v) {f : F → ℂ} {ν : F}
    (hf : ∀ x h : F, SmallD 𝔪 k h → f (x + h) = f x)
    (hψ : ∀ h : F, SmallD 𝔪 k h → ψ (ν * h) = 1) :
    jacD ψ k' f ν = jacD ψ k f ν := by
  classical
  have h_le : latD 𝔪 k' ≤ latD 𝔪 k := fun x hx => SmallD.mono hk hx
  have hcard := card_latD_quot h𝔪 hk
  have hpos : 0 < ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (k' v - k v).toNat :=
    Finset.prod_pos fun v _ => pow_pos (by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega) _
  haveI hfin : Finite (latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
  haveI := Fintype.ofFinite (latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k))
  set e := AddSubgroup.quotientEquivProdOfLE h_le with he
  set G : F ⧸ latD 𝔪 k → ℂ := fun y => f y.out * (starRingEnd ℂ) (ψ (ν * y.out)) with hGdef
  have key : ∀ x : F ⧸ latD 𝔪 k', f x.out * (starRingEnd ℂ) (ψ (ν * x.out)) = G (e x).1 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x₀ =>
      have e1 : (e (QuotientAddGroup.mk x₀)).1 = (QuotientAddGroup.mk x₀ : F ⧸ latD 𝔪 k) := rfl
      rw [e1, hGdef]
      simp only
      rw [jacD_term ψ hf hψ x₀,
        jacD_term ψ (fun x h hh => hf x h (SmallD.mono hk hh))
          (fun h hh => hψ h (SmallD.mono hk hh)) x₀]
  rw [jacD, jacD]
  simp only [key]
  rw [show (∑' x : F ⧸ latD 𝔪 k', G (e x).1) = ∑' p : (F ⧸ latD 𝔪 k) ×
      (latD 𝔪 k ⧸ (latD 𝔪 k').addSubgroupOf (latD 𝔪 k)), G p.1 from e.tsum_eq fun p => G p.1,
    tsum_prod_const_snd, ← Nat.card_eq_fintype_card, hcard]
  have hvol : (volD 𝔪 k' : ℂ)
      * ((∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (k' v - k v).toNat : ℕ) : ℂ)
      = (volD 𝔪 k : ℂ) := by
    rw [volD, volD]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega
    have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast h0
    have hkv := hk v ((CubicPkg.mem_sFin h𝔪 v).mp hv)
    rw [← zpow_natCast, ← zpow_add₀ hq]
    congr 1
    omega
  rw [← mul_assoc, hvol]

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
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

/-- The depth function `k` is *valid* for `Φ` and the frequency `ν`: `Φ` is `n(b)`-invariant for
`b ∈ 𝔩_k` and `ψ(ν ·)` is trivial on `𝔩_k`. -/
def Valid (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) (ν : F) (k : HeightOneSpectrum (𝓞 F) → ℤ) : Prop :=
  (∀ b : F, SmallD 𝔪 k b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d) ∧
    ∀ h : F, SmallD 𝔪 k h → ψ (ν * h) = 1

theorem exists_valid (hG : Good 𝔪) (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) (ν : F) :
    ∃ M : ℤ, Valid ψ Φ ν (fun _ => M) := by
  obtain ⟨N, hN⟩ := Φ.exists_unip
  obtain ⟨M₀, hM₀⟩ := ψ.cont
  obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot ν
  refine ⟨max (N : ℤ) (M₀ + B), fun b hb => hN b (Small.mono (le_max_left _ _) hb),
    fun h hh => hM₀ _ ?_⟩
  have hh' : Small 𝔪 (M₀ + B) h := Small.mono (le_max_right _ _) hh
  exact (hB.mul hh').mono (by omega)

/-- **Independence of the valid depth.** -/
theorem lamD_eq_of_valid (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F}
    {k k' : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (h' : Valid ψ Φ ν k') (c : F)
    (s : ℂ) : lamD ψ k Φ c ν s = lamD ψ k' Φ c ν s := by
  have e1 := jacD_eq_of_le ψ hG.ne_bot (k := k) (k' := fun v => max (k v) (k' v))
    (fun v _ => le_max_left _ _) (f := fun u => Φ s c (c * u)) (ν := ν)
    (fun x b hb => by rw [mul_add]; exact h.1 b hb s c _) h.2
  have e2 := jacD_eq_of_le ψ hG.ne_bot (k := k') (k' := fun v => max (k v) (k' v))
    (fun v _ => le_max_right _ _) (f := fun u => Φ s c (c * u)) (ν := ν)
    (fun x b hb => by rw [mul_add]; exact h'.1 b hb s c _) h'.2
  rw [lamD, lamD, ← e1, ← e2]

/-- A valid uniform depth for `Φ` and `ν`. -/
def depth (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (ν : F) : ℤ :=
  (exists_valid hG ψ Φ ν).choose

theorem valid_depth (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (ν : F) :
    Valid ψ Φ ν (fun _ => depth ψ hG Φ ν) :=
  (exists_valid hG ψ Φ ν).choose_spec

/-- **The normalized finite Jacquet functional** `Lam Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)`
(WP-E §0), at a valid depth. -/
def Lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (c ν : F) (s : ℂ) : ℂ :=
  lam ψ (depth ψ hG Φ ν) Φ c ν s

theorem Lam_eq_lamD (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lamD ψ k Φ c ν s :=
  lamD_eq_of_valid ψ hG Φ (valid_depth ψ hG Φ ν) h c s

/-! ### The interface `E.Kubota` -/

section instance_

open ArtinKP.B7 ArtinKP.E

variable (ψ : SfChar 𝔪) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- `Lam` on `R`. -/
def LamR (Φ : GSection ι P 𝔪) (c ν : SInt 𝔪) (s : ℂ) : ℂ := Lam ψ hG Φ (c : F) (ν : F) s

end instance_

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

/-- The summand of the Kubota series. -/
def kTerm (a : Cls (SInt 𝔪)) (s : ℂ) : ℂ :=
  gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
    * S2.LamR (psiS hG.ne_bot) hG Φ (rp a.1) ν s * nrm (rp a.1) ^ (-s)

end ArtinKP.B
end
end


