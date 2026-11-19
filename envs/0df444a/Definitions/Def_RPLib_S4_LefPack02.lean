-- Prove2me | Definitions.Def_RPLib_S4_LefPack02
-- name    : RPLib_S4_LefPack02
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T20:20:20.135365+00:00
-- url     : https://prove2.me/theorems/24454ec9-33cd-47b7-861e-99f70dff4038
-- title:
--   Lefschetz trace formula library (Grothendieck–Lefschetz trace formula mod ℓⁿ on curves over finite fields), part 2 of 32
-- statement:
--   Part 2 of 32 of the Lefschetz trace formula library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
--   * `Def_RP_CP4a_HypC`: S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`
--   * `Def_RP_CP4a_HypD`: S4-CP4a, part g4: the genus of `y² = x⁵ + 1` is 2
--
--   **Formalization note.** Library package of a formalization of the Grothendieck–Lefschetz trace formula modulo $\ell^n$ for a lisse sheaf of free $\mathbb Z/\ell^n$-modules on an affine curve over a finite field, on the compactly supported cochain complex of the geometric fundamental group. The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib
import Definitions.Def_RPLib_S4_LefPack01

/-!
# Lefschetz trace formula library package, part 2 of 32

Library modules of the formalization of the Grothendieck-Lefschetz trace formula mod `l^n` for lisse sheaves on an
affine curve over a finite field (`RamanujanPetersson.Lefschetz.lefschetz_main`). Each module below is copied
verbatim (import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
* `Def_RP_CP4a_HypC`: S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`
* `Def_RP_CP4a_HypD`: S4-CP4a, part g4: the genus of `y² = x⁵ + 1` is 2
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Main =====
section

/-!
# S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)

For a function field `F/𝔽_q` with full constant field (`hk`), its affine chart `U = Spec Rfin` (the complement of
the places over `∞` of `𝔽_q(x)`) and every prime `l ∤ q`, `n > 0`, ASSUMING the Core B statement `CoreBHyp hk l`:
* `lefschetz_point_count`: for EVERY lift `φ` of the arithmetic Frobenius to `π₁(U)` and every `m ≥ 1`,
  `Tr(F^m | H²_c(Ū, ℤ/l^n)) - Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #U(𝔽_{q^m})` in `ℤ/l^n`, where
  `#U(𝔽_{q^m}) := #Hom_{𝔽_q}(Rfin, L)` for any finite `L/𝔽_q` of degree `m`, the cohomology is the S4-CurveCoh
  cohomology with the canonical boundary data over `∞` and `F` is geometric Frobenius (`φ⁻¹`).
* `cp4a_lefschetz`: the same with a Frobenius lift that exists (`exists_frobLift`), so the statement is not vacuous;
  `finite_bdryS` / `nonempty_bdryS`: the canonical boundary is a nonempty finite set.
No hypothesis other than Core B is left: the Frobenius lift, the roots of unity, the units `N` in the charts,
the boundary data and the inertia lifting are all constructed (parts f1-f4).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The canonical boundary data of `U` over `∞` (one prime of the pro-chart per `π₁^geo`-orbit). -/
abbrev bdryInf (Fq F : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Field F] [Algebra Fq F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F] [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] :
    BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  bdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)

include hq he in
/-- The geometric boundary of `U` is finite. -/
theorem finite_bdryS : Finite (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  finite_bdry hq he (exists_zeta_level he) (bdryInf Fq F) (bdryData_B _ _ _ _)

/-- The geometric boundary of `U` is nonempty. -/
theorem nonempty_bdryS : Nonempty (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  nonempty_bdry (bdryInf Fq F) (bdryData_B _ _ _ _)

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Lefschetz point count for `U`** (Core B as a hypothesis), for every Frobenius lift `φ`. -/
theorem lefschetz_point_count [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F) (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (m : ℕ) (hm : 1 ≤ m) (L : Type) [Field L] [Algebra Fq L] [Finite L] (hL : Module.finrank Fq L = m) :
    LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
        (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
      LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) (bdryInf Fq F))
        (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq))
          (bdryInf Fq F).inertia φ⁻¹ (trueTau (bdryInf Fq F) φ⁻¹) (trueH (bdryInf Fq F) φ⁻¹)
          (trueCompat (bdryInf Fq F) φ⁻¹) ^ m) =
      (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) := by
  have hNF : (N : F) ≠ 0 := by
    rw [hN]
    exact cast_ne_zero_of_not_dvd hq he hlq n
  obtain ⟨ζ, hζ, hζΓ⟩ := exists_zeta_geo hq he hNF
  have := nonempty_bdryS (Fq := Fq) (F := F)
  exact lefschetz_count hk hq he (isUnit_cast_Rfin hNF) (isUnit_cast_Rinf hNF) hζ hζΓ (bdryInf Fq F)
    (bdryData_B _ _ _ _) (bdryLift) hNF (exists_zeta_level he) l n hn hN hlq hB φ hφ m hm L hL

include hk hq he in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **CP4a** (Core B as a hypothesis): a Frobenius lift `φ` exists, and for it and every `m ≥ 1`,
`Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n`. -/
theorem cp4a_lefschetz [Fintype (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    [DecidableEq (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F))]
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} [NeZero N] (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) :
    ∃ φ : Pi1 (Rfin Fq F) F, IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ (L : Type) [Field L] [Algebra Fq L] [Finite L], Module.finrank Fq L = m →
      LinearMap.trace (ZMod N) (curveH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N))
          (geomFrobH2c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ ^ m) -
        LinearMap.trace (ZMod N) (curveH1c (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) (bdryInf Fq F))
          (frobH1c (triv F (maxUnram (Rfin Fq F) F) N) (pi1geo (Rfin Fq F) F (Fintype.card Fq))
            (bdryInf Fq F).inertia φ⁻¹ (trueTau (bdryInf Fq F) φ⁻¹) (trueH (bdryInf Fq F) φ⁻¹)
            (trueCompat (bdryInf Fq F) φ⁻¹) ^ m) =
        (Nat.card (Rfin Fq F →ₐ[Fq] L) : ZMod N) := by
  obtain ⟨φ, hφ⟩ := exists_frobLift hk hq he
  exact ⟨φ, hφ, fun m hm L _ _ _ hL => lefschetz_point_count hk hq he l n hn hN hlq hB φ hφ m hm L hL⟩

end Main

end

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CP4a_HypC =====
section

/-!
# S4-CP4a, part g3: the place at infinity of `y² = x⁵ + 1`

For `F = Fq(x, y)`, `y² = x⁵ + 1` (`2 ≠ 0` in `Fq`):
* `ord_tF_eq_two`, `deg_infPlace_eq_one`: every place over `x = ∞` has `ord(1/x) = 2` and degree one
  (`w = y/x³` has `w² = (1/x)(1 + 1/x⁵)`, so `ord(1/x)` is even, and `Σ ord(1/x) deg P = 2`);
* `infPlace_eq`: there is exactly one such place; `constField_hyp`: the full constant field is `Fq`;
* `ord_poly`: `ord_∞ a(x) = -2 deg a`; `ord_yF`: `ord_∞ y = -5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.CP4a.Hyp2

open Places ZetaSB

noncomputable section

section Gen

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [FiniteQuot S] {K : Type*} [Field K] [Algebra S K]
  [IsFractionRing S K]

theorem ord_one' (P : HeightOneSpectrum S) : Places.ord P (1 : K) = 0 := by
  simp [Places.ord]

theorem ord_pow' (P : HeightOneSpectrum S) {f : K} (hf : f ≠ 0) (k : ℕ) :
    Places.ord P (f ^ k) = k * Places.ord P f := by
  induction k with
  | zero => rw [pow_zero, ord_one', Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, Places.ord_mul P (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem ord_alg_nonneg (P : HeightOneSpectrum S) (a : S) : 0 ≤ Places.ord P (algebraMap S K a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero, Places.ord_zero]
  · rw [Places.ord_algebraMap P ha]; exact Int.natCast_nonneg _

theorem ord_alg_unit (P : HeightOneSpectrum S) {a : S} (ha : IsUnit a) :
    Places.ord P (algebraMap S K a) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hinj := IsFractionRing.injective S K
  have hne : ∀ b : Sˣ, algebraMap S K (b : S) ≠ 0 := fun b h => b.ne_zero ((map_eq_zero_iff _ hinj).mp h)
  have h1 : algebraMap S K (u : S) * algebraMap S K ((u⁻¹ : Sˣ) : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 := Places.ord_mul P (hne u) (hne u⁻¹)
  rw [h1, ord_one'] at h2
  have h3 := ord_alg_nonneg (K := K) P (u : S)
  have h4 := ord_alg_nonneg (K := K) P ((u⁻¹ : Sˣ) : S)
  omega

theorem one_le_ord_of_mem (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) (hP : a ∈ P.asIdeal) :
    1 ≤ Places.ord P (algebraMap S K a) := by
  rw [Places.ord_algebraMap P ha]
  have h : Places.cnt P a ≠ 0 := by
    rw [Places.cnt, Associates.count_ne_zero_iff_dvd
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]) P.irreducible, Ideal.dvd_span_singleton]
    exact hP
  omega

theorem ord_add_eq_of_lt (P : HeightOneSpectrum S) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : Places.ord P f < Places.ord P g) : Places.ord P (f + g) = Places.ord P f := by
  have hvf : P.valuation K f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have hvg : P.valuation K g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg
  have hlt : P.valuation K g < P.valuation K f := by
    rw [← WithZero.exp_log hvf, ← WithZero.exp_log hvg, WithZero.exp_lt_exp]
    simp only [Places.ord] at h
    omega
  simp only [Places.ord]
  rw [Valuation.map_add_eq_of_lt_left _ hlt]

end Gen

section Hyp

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

/-- `1/x` in `F`. -/
abbrev tF : HypF Fq := algebraMap (RatFunc Fq) (HypF Fq) (1 / RatFunc.X)

theorem alg_Oinf (a : Oinf Fq) : algebraMap (Rinf Fq (HypF Fq)) (HypF Fq)
    (algebraMap (Oinf Fq) (Rinf Fq (HypF Fq)) a) = algebraMap (RatFunc Fq) (HypF Fq) (a : RatFunc Fq) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Oinf Fq) (RatFunc Fq) (HypF Fq)]
  rfl

theorem tF_eq : algebraMap (Rinf Fq (HypF Fq)) (HypF Fq) (piInfR Fq (HypF Fq)) = tF Fq := by
  rw [piInfR, alg_Oinf]; rfl

theorem tF_ne_zero : tF Fq ≠ 0 := by
  rw [← tF_eq]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (Rinf Fq (HypF Fq)) (HypF Fq))).mpr piInfR_ne_zero

theorem ratFunc_ne_zero {r : RatFunc Fq} (hr : r ≠ 0) : algebraMap (RatFunc Fq) (HypF Fq) r ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap (RatFunc Fq) (HypF Fq)).injective).mpr hr

/-- Elements of `Fq(x)` of degree `0` have order `0` at every place over `∞`. -/
theorem ord_ratFunc_eq_zero {r : RatFunc Fq} (hr : r ≠ 0) (h0 : r.intDegree = 0)
    (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) : Places.ord P (algebraMap (RatFunc Fq) (HypF Fq) r) = 0 := by
  have hr1 : r ∈ Oinf Fq := (mem_Oinf_iff' Fq hr).mpr h0.le
  have hri : r⁻¹ ≠ 0 := inv_ne_zero hr
  have hdeg : r⁻¹.intDegree = 0 := by rw [RatFunc.intDegree_inv, h0, neg_zero]
  have hr2 : r⁻¹ ∈ Oinf Fq := (mem_Oinf_iff' Fq hri).mpr hdeg.le
  have hu : IsUnit (⟨r, hr1⟩ : Oinf Fq) :=
    isUnit_iff_exists_inv.mpr ⟨⟨r⁻¹, hr2⟩, Subtype.ext (mul_inv_cancel₀ hr)⟩
  have := ord_alg_unit (K := HypF Fq) P (hu.map (algebraMap (Oinf Fq) (Rinf Fq (HypF Fq))))
  rwa [alg_Oinf] at this

theorem invX_pow (n : ℕ) : (1 / RatFunc.X : RatFunc Fq) ^ n =
    algebraMap Fq[X] (RatFunc Fq) 1 / algebraMap Fq[X] (RatFunc Fq) (X ^ n) := by
  rw [map_one, map_pow, RatFunc.algebraMap_X, one_div_pow]

/-- `w = y/x³` with `w² = (1/x)(1 + 1/x⁵)`. -/
abbrev wF : HypF Fq := yF Fq * tF Fq ^ 3

theorem wF_sq : wF Fq ^ 2 = tF Fq * algebraMap (RatFunc Fq) (HypF Fq) (1 + (1 / RatFunc.X) ^ 5) := by
  have hX : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  simp only [wF, tF]
  rw [mul_pow, hy, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  rw [f0K, f0, map_add, map_pow, RatFunc.algebraMap_X, map_one]
  field_simp

theorem ord_tF_even (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    Places.ord P (tF Fq) = 2 * Places.ord P (wF Fq) := by
  have hX : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  have hw : wF Fq ≠ 0 := mul_ne_zero (yF_ne_zero Fq) (pow_ne_zero _ (tF_ne_zero Fq))
  have he : (1 + (1 / RatFunc.X) ^ 5 : RatFunc Fq) =
      algebraMap Fq[X] (RatFunc Fq) (X ^ 5 + 1) / algebraMap Fq[X] (RatFunc Fq) (X ^ 5) := by
    rw [map_add, map_pow, RatFunc.algebraMap_X, map_one]; field_simp
  have hu0 : (1 + (1 / RatFunc.X) ^ 5 : RatFunc Fq) ≠ 0 := by
    rw [he]; exact div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr
      (f0_ne_zero Fq)) ((map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr
      (pow_ne_zero _ X_ne_zero))
  have hdeg : (1 + (1 / RatFunc.X) ^ 5 : RatFunc Fq).intDegree = 0 := by
    rw [he, intDegree_div_polys Fq (f0_ne_zero Fq) (pow_ne_zero _ X_ne_zero), natDegree_f0, natDegree_X_pow]
    simp
  have hu := ord_ratFunc_eq_zero Fq hu0 hdeg P
  calc Places.ord P (tF Fq)
      = Places.ord P (tF Fq) + Places.ord P (algebraMap (RatFunc Fq) (HypF Fq) (1 + (1 / RatFunc.X) ^ 5)) := by
        rw [hu, add_zero]
    _ = Places.ord P (tF Fq * algebraMap (RatFunc Fq) (HypF Fq) (1 + (1 / RatFunc.X) ^ 5)) :=
        (Places.ord_mul P (tF_ne_zero Fq) (ratFunc_ne_zero Fq hu0)).symm
    _ = Places.ord P (wF Fq ^ 2) := by rw [wF_sq]
    _ = 2 * Places.ord P (wF Fq) := by rw [ord_pow' P hw 2]; norm_num

theorem two_le_ord_tF (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) : 2 ≤ Places.ord P (tF Fq) := by
  have h1 := one_le_ord_of_mem (K := HypF Fq) P piInfR_ne_zero (piInfR_mem P)
  rw [tF_eq] at h1
  have h2 := ord_tF_even Fq P
  omega

theorem norm_tF : Algebra.norm (RatFunc Fq) (tF Fq) = (1 / RatFunc.X) ^ 2 := by
  rw [tF, Algebra.norm_algebraMap, finrank_hypF]

/-- `Σ_{P | ∞} ord_P(1/x) deg P = 2`. -/
theorem degS_tF : degS Fq (divS (Rinf Fq (HypF Fq)) (tF Fq)) = 2 := by
  have h := degS_inf Fq (HypF Fq) (piInfR_ne_zero (Fq := Fq) (F := HypF Fq))
  rw [tF_eq, norm_tF, invX_pow, intDegree_div_polys Fq one_ne_zero (pow_ne_zero _ X_ne_zero)] at h
  simpa using h

theorem mem_support_tF (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    P ∈ (divS (Rinf Fq (HypF Fq)) (tF Fq)).support := by
  rw [Finsupp.mem_support_iff, divS_apply]
  have := two_le_ord_tF Fq P
  omega

theorem term_nonneg (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    0 ≤ (divS (Rinf Fq (HypF Fq)) (tF Fq)) P * (Places.deg Fq P : ℤ) := by
  rw [divS_apply]
  have := two_le_ord_tF Fq P
  exact mul_nonneg (by omega) (Int.natCast_nonneg _)

theorem ord_deg_le (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    Places.ord P (tF Fq) * (Places.deg Fq P : ℤ) ≤ 2 := by
  have h := degS_tF Fq
  rw [degS, Finsupp.sum] at h
  rw [← h]
  exact Finset.single_le_sum (f := fun Q => (divS (Rinf Fq (HypF Fq)) (tF Fq)) Q * (Places.deg Fq Q : ℤ))
    (fun Q _ => term_nonneg Fq Q) (mem_support_tF Fq P)

/-- Every place over `∞` has `ord(1/x) = 2` and degree one. -/
theorem ord_tF_eq_two (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    Places.ord P (tF Fq) = 2 ∧ Places.deg Fq P = 1 := by
  have h1 := ord_deg_le Fq P
  have h2 := two_le_ord_tF Fq P
  have h3 : (1 : ℤ) ≤ Places.deg Fq P := by exact_mod_cast Places.deg_pos Fq P
  have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℤ) ≤ Places.ord P (tF Fq) by omega)
  have h5 := mul_le_mul_of_nonneg_right h2 (show (0 : ℤ) ≤ Places.deg Fq P by omega)
  constructor
  · linarith
  · have : (Places.deg Fq P : ℤ) ≤ 1 := by linarith
    omega

/-- There is exactly one place over `∞`. -/
theorem infPlace_eq (P P' : HeightOneSpectrum (Rinf Fq (HypF Fq))) : P = P' := by
  classical
  by_contra hne
  have h := degS_tF Fq
  rw [degS, Finsupp.sum] at h
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun Q => (divS (Rinf Fq (HypF Fq)) (tF Fq)) Q * (Places.deg Fq Q : ℤ))
    (s := {P, P'}) (t := (divS (Rinf Fq (HypF Fq)) (tF Fq)).support)
    (fun Q _ => mem_support_tF Fq Q) (fun Q _ _ => term_nonneg Fq Q)
  rw [Finset.sum_pair hne, h] at hle
  simp only [divS_apply] at hle
  rw [(ord_tF_eq_two Fq P).1, (ord_tF_eq_two Fq P).2, (ord_tF_eq_two Fq P').1, (ord_tF_eq_two Fq P').2] at hle
  norm_num at hle

instance : Subsingleton (HeightOneSpectrum (Rinf Fq (HypF Fq))) := ⟨infPlace_eq Fq⟩

/-- The place at infinity. -/
noncomputable def Pinf : HeightOneSpectrum (Rinf Fq (HypF Fq)) := (nonempty_infPlace Fq (HypF Fq)).some

/-- **The full constant field of `Fq(x, y)` is `Fq`.** -/
theorem constField_hyp : constField Fq (HypF Fq) = ⊥ :=
  constField_eq_bot_of_deg_one Fq (HypF Fq) (P := Sum.inr (Pinf Fq))
    (by rw [Place.deg_inr]; exact (ord_tF_eq_two Fq _).2)

theorem polyF_ne_zero {b : Fq[X]} (hb : b ≠ 0) : algebraMap Fq[X] (HypF Fq) b ≠ 0 := by
  rw [algebraMap_poly]
  exact ratFunc_ne_zero Fq ((map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).mpr hb)

theorem ord_X (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) :
    Places.ord P (algebraMap Fq[X] (HypF Fq) X) = -2 := by
  have hX : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  have h1 : algebraMap Fq[X] (HypF Fq) X * tF Fq = 1 := by
    rw [algebraMap_poly, RatFunc.algebraMap_X, tF, ← map_mul, mul_one_div_cancel hX, map_one]
  have h2 := Places.ord_mul P (polyF_ne_zero Fq X_ne_zero) (tF_ne_zero Fq)
  rw [h1, ord_one', (ord_tF_eq_two Fq P).1] at h2
  omega

/-- `ord_∞ a(x) = -2 deg a`. -/
theorem ord_poly (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) {a : Fq[X]} (ha : a ≠ 0) :
    Places.ord P (algebraMap Fq[X] (HypF Fq) a) = -2 * a.natDegree := by
  have hd : (X ^ a.natDegree : Fq[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hinj := IsFractionRing.injective Fq[X] (RatFunc Fq)
  have hr0 : algebraMap Fq[X] (RatFunc Fq) a / algebraMap Fq[X] (RatFunc Fq) (X ^ a.natDegree) ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ hinj).mpr ha) ((map_ne_zero_iff _ hinj).mpr hd)
  have h0 := ord_ratFunc_eq_zero Fq hr0 (by rw [intDegree_div_polys Fq ha hd, natDegree_X_pow, sub_self]) P
  rw [map_div₀, ← algebraMap_poly, ← algebraMap_poly, Places.ord_div P (polyF_ne_zero Fq ha)
    (polyF_ne_zero Fq hd), map_pow, ord_pow' P (polyF_ne_zero Fq X_ne_zero), ord_X] at h0
  omega

/-- `ord_∞ y = -5`. -/
theorem ord_yF (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) : Places.ord P (yF Fq) = -5 := by
  have h := ord_pow' P (yF_ne_zero Fq) 2
  rw [hy, show f0K Fq = algebraMap Fq[X] (RatFunc Fq) (f0 Fq) from rfl, ← algebraMap_poly,
    ord_poly Fq P (f0_ne_zero Fq), natDegree_f0] at h
  push_cast at h
  omega

end Hyp

end

end RamanujanPetersson.CP4a.Hyp2

end

-- ===== S4.Def_RP_CP4a_HypD =====
section

/-!
# S4-CP4a, part g4: the genus of `y² = x⁵ + 1` is 2

For `D_k = 2k P_∞` (`k ≥ 2`), `L(D_k) = {a + b y : deg a ≤ k, deg b ≤ k - 3}` (`range_cPlin`), so `ℓ(D_k) = 2k - 1`
(`ellF_Dk`); Riemann-Roch (`ellF_eq_of_deg`, S3-RR) at `k = g + 3` gives `genus_hyp : g = 2` (`char ≠ 2, 5`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.CP4a.Hyp2

open Places ZetaSB RR

noncomputable section

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)]

/-- `ord_∞ (a + b y) ≥ -2k` iff `deg a ≤ k` and `deg b ≤ k - 3`. -/
theorem ord_cP_ge (P : HeightOneSpectrum (Rinf Fq (HypF Fq))) (k : ℕ) {a b : Fq[X]} (hab : cP Fq a b ≠ 0) :
    -2 * (k : ℤ) ≤ Places.ord P (cP Fq a b) ↔
      (a = 0 ∨ a.natDegree ≤ k) ∧ (b = 0 ∨ b.natDegree + 3 ≤ k) := by
  have hby : ∀ {b : Fq[X]}, b ≠ 0 →
      Places.ord P (algebraMap Fq[X] (HypF Fq) b * yF Fq) = -2 * b.natDegree - 5 := fun hb => by
    rw [Places.ord_mul P (polyF_ne_zero Fq hb) (yF_ne_zero Fq), ord_poly Fq P hb, ord_yF]; ring
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by rintro rfl; apply hab; simp [cP]
    have e : cP Fq 0 b = algebraMap Fq[X] (HypF Fq) b * yF Fq := by simp [cP]
    rw [e, hby hb]
    simp only [true_or, hb, false_or, true_and]
    constructor <;> intro h <;> omega
  by_cases hb : b = 0
  · subst hb
    have e : cP Fq a 0 = algebraMap Fq[X] (HypF Fq) a := by simp [cP]
    rw [e, ord_poly Fq P ha]
    simp only [ha, false_or, true_or, and_true]
    constructor <;> intro h <;> omega
  simp only [ha, false_or, hb]
  have hA := ord_poly Fq P ha
  have hB := hby hb
  have hne : Places.ord P (algebraMap Fq[X] (HypF Fq) a) ≠ Places.ord P (algebraMap Fq[X] (HypF Fq) b * yF Fq) := by
    rw [hA, hB]; omega
  unfold cP
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ord_add_eq_of_lt P (polyF_ne_zero Fq ha) (mul_ne_zero (polyF_ne_zero Fq hb) (yF_ne_zero Fq)) h]
    rw [hA, hB] at h; rw [hA]
    constructor <;> intro h' <;> omega
  · rw [add_comm, ord_add_eq_of_lt P (mul_ne_zero (polyF_ne_zero Fq hb) (yF_ne_zero Fq)) (polyF_ne_zero Fq ha) h]
    rw [hA, hB] at h; rw [hB]
    constructor <;> intro h' <;> omega

omit [Fintype Fq] [DecidableEq (RatFunc Fq)] [Fact ((2 : Fq) ≠ 0)] in
/-- `(a, b) ↦ a + b y` on `deg a ≤ k`, `deg b < k - 2`. -/
def cPlin (k : ℕ) : (degreeLT Fq (k + 1) × degreeLT Fq (k - 2)) →ₗ[Fq] HypF Fq :=
  ((IsScalarTower.toAlgHom Fq Fq[X] (HypF Fq)).toLinearMap ∘ₗ (degreeLT Fq (k + 1)).subtype).coprod
    (LinearMap.mulRight Fq (yF Fq) ∘ₗ (IsScalarTower.toAlgHom Fq Fq[X] (HypF Fq)).toLinearMap ∘ₗ
      (degreeLT Fq (k - 2)).subtype)

theorem cPlin_apply (k : ℕ) (ab : degreeLT Fq (k + 1) × degreeLT Fq (k - 2)) :
    cPlin Fq k ab = cP Fq ab.1 ab.2 := rfl

theorem cPlin_injective (k : ℕ) : Function.Injective (cPlin Fq k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ab h
  rw [cPlin_apply] at h
  have h0 : cP Fq ab.1 ab.2 = cP Fq 0 0 := by rw [h]; simp [cP]
  obtain ⟨h1, h2⟩ := cP_inj Fq h0
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

instance finite_degreeLT (n : ℕ) : Module.Finite Fq (degreeLT Fq n) :=
  Module.Finite.equiv (degreeLTEquiv Fq n).symm

theorem finrank_degreeLT' (n : ℕ) : Module.finrank Fq (degreeLT Fq n) = n := by
  rw [(degreeLTEquiv Fq n).finrank_eq, Module.finrank_fin_fun]

/-- The divisor `2k P_∞`. -/
abbrev Dk (k : ℕ) : Places.Divisor Fq (HypF Fq) := Finsupp.single (Sum.inr (Pinf Fq)) (2 * (k : ℤ))

theorem nonneg_div_add_Dk_iff (k : ℕ) (f : HypF Fq) :
    0 ≤ Places.div f + Dk Fq k ↔ (∀ Q : HeightOneSpectrum (Rfin Fq (HypF Fq)), 0 ≤ Places.ord Q f) ∧
      -2 * (k : ℤ) ≤ Places.ord (Pinf Fq) f := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    refine ⟨fun Q => ?_, ?_⟩
    · simpa [Dk] using h (Sum.inl Q)
    · have := h (Sum.inr (Pinf Fq)); simp [Dk] at this; omega
  · rintro ⟨h1, h2⟩ (Q | Q)
    · simpa [Dk] using h1 Q
    · rw [Subsingleton.elim Q (Pinf Fq)]; simp [Dk]; omega

theorem ord_fin_nonneg_cP (Q : HeightOneSpectrum (Rfin Fq (HypF Fq))) (a b : Fq[X]) :
    0 ≤ Places.ord Q (cP Fq a b) :=
  ord_alg_nonneg (K := HypF Fq) Q
    (⟨cP Fq a b, (mem_integralClosure_iff _ _).mpr (isIntegral_cP Fq a b)⟩ : Rfin Fq (HypF Fq))

theorem isIntegral_of_ord {f : HypF Fq} (hf : f ≠ 0)
    (h : ∀ Q : HeightOneSpectrum (Rfin Fq (HypF Fq)), 0 ≤ Places.ord Q f) : IsIntegral Fq[X] f := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := Rfin Fq (HypF Fq))
    (K := HypF Fq) f (fun Q => by
      have h1 := h Q
      have hv : Q.valuation (HypF Fq) f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
      rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp only [Places.ord] at h1
      omega)
  rw [← hr]
  exact (mem_integralClosure_iff _ _).mp r.2

/-- `L(2k P_∞) = {a + b y : deg a ≤ k, deg b < k - 2}`. -/
theorem range_cPlin (k : ℕ) (h5 : (5 : Fq) ≠ 0) :
    LinearMap.range (cPlin Fq k) = LF Fq (HypF Fq) (Dk Fq k) := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [cPlin_apply]
    by_cases h0 : cP Fq a b = 0
    · rw [h0]; exact zero_mem _
    rw [mem_LF h0, nonneg_div_add_Dk_iff]
    refine ⟨fun Q => ord_fin_nonneg_cP Fq Q a b, (ord_cP_ge Fq (Pinf Fq) k h0).2 ⟨?_, ?_⟩⟩
    · by_cases ha0 : (a : Fq[X]) = 0
      · exact Or.inl ha0
      · have ha := mem_degreeLT.mp a.2
        rw [degree_eq_natDegree ha0] at ha
        have : (a : Fq[X]).natDegree < k + 1 := by exact_mod_cast ha
        right; omega
    · by_cases hb0 : (b : Fq[X]) = 0
      · exact Or.inl hb0
      · have hb := mem_degreeLT.mp b.2
        rw [degree_eq_natDegree hb0] at hb
        have : (b : Fq[X]).natDegree < k - 2 := by exact_mod_cast hb
        right; omega
  · intro f hf
    by_cases h0 : f = 0
    · rw [h0]; exact zero_mem _
    rw [mem_LF h0, nonneg_div_add_Dk_iff] at hf
    obtain ⟨a, b, rfl⟩ := (isIntegral_iff Fq Fact.out h5 f).mp (isIntegral_of_ord Fq h0 hf.1)
    have hd := (ord_cP_ge Fq (Pinf Fq) k h0).1 hf.2
    refine ⟨(⟨a, mem_degreeLT.mpr ?_⟩, ⟨b, mem_degreeLT.mpr ?_⟩), cPlin_apply Fq k _⟩
    · by_cases ha' : a = 0
      · rw [ha', degree_zero]; exact WithBot.bot_lt_coe _
      rw [degree_eq_natDegree ha']
      have : a.natDegree < k + 1 := by rcases hd.1 with h | h; exacts [absurd h ha', by omega]
      exact_mod_cast this
    · by_cases hb' : b = 0
      · rw [hb', degree_zero]; exact WithBot.bot_lt_coe _
      rw [degree_eq_natDegree hb']
      have : b.natDegree < k - 2 := by rcases hd.2 with h | h; exacts [absurd h hb', by omega]
      exact_mod_cast this

/-- `ℓ(2k P_∞) = 2k - 1` for `k ≥ 2`. -/
theorem ellF_Dk (k : ℕ) (hk : 2 ≤ k) (h5 : (5 : Fq) ≠ 0) : ellF Fq (HypF Fq) (Dk Fq k) = 2 * k - 1 := by
  show Module.finrank Fq (LF Fq (HypF Fq) (Dk Fq k)) = _
  rw [← range_cPlin Fq k h5, LinearMap.finrank_range_of_inj (cPlin_injective Fq k), Module.finrank_prod,
    finrank_degreeLT', finrank_degreeLT']
  omega

theorem deg_Dk (k : ℕ) : (Dk Fq k).deg = 2 * k := by
  rw [Places.Divisor.deg_single, Place.deg_inr, (ord_tF_eq_two Fq _).2]
  simp

/-- **The genus of `y² = x⁵ + 1` is 2** (`char Fq ≠ 2, 5`). -/
theorem genus_hyp (h5 : (5 : Fq) ≠ 0) : genusF Fq (HypF Fq) = 2 := by
  have h := ellF_eq_of_deg (constField_hyp Fq) (D := Dk Fq (genusF Fq (HypF Fq) + 3))
    (by rw [deg_Dk]; push_cast; omega)
  rw [ellF_Dk Fq _ (by omega) h5, deg_Dk] at h
  push_cast at h
  omega

end

end RamanujanPetersson.CP4a.Hyp2

end


