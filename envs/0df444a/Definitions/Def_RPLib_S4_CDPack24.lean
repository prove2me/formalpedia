-- Prove2me | Definitions.Def_RPLib_S4_CDPack24
-- name    : RPLib_S4_CDPack24
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:16:34.208216+00:00
-- url     : https://prove2.me/theorems/cda6bc9f-e97c-4245-acbf-62b2f3adfb69
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 24 of 71
-- statement:
--   Part 24 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_RRk`: S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`
--   * `Def_RP_JacLaw_Exact`: S4-JacLaw, file O6a: exact poles from hyperplane conditions
--   * `Def_RP_JacLaw_RRkH`: S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)
--   * `Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
--   * `Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
--   * `Def_RP_PicDescent`: S4-PicDescent: class numbers `h_m = L_m(1)`, F. K. Schmidt, Galois descent for `Pic⁰` (G1-2 rest, G1-3, review R7)
--   * `Def_RP_JacFrob_Setup`: S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`
--   * `Def_RP_JacFrob_FF`: S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`
--   * `Def_RP_JacFrob_Sig`: S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`
--   * `Def_RP_JacFrob_Phi`: S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack23
import Definitions.Def_RPLib_S4_CDPack20
import Definitions.Def_RPLib_S4_CDPack13
import Definitions.Def_RPLib_S4_PicDescentA
import Definitions.Def_RPLib_S4_PicDescentB4
import Definitions.Def_RPLib_S4_CDPack11
import Definitions.Def_RPLib_S4_CDPack12

/-!
# Curve-duality library package, part 24 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_RRk`: S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`
* `Def_RP_JacLaw_Exact`: S4-JacLaw, file O6a: exact poles from hyperplane conditions
* `Def_RP_JacLaw_RRkH`: S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)
* `Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
* `Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
* `Def_RP_PicDescent`: S4-PicDescent: class numbers `h_m = L_m(1)`, F. K. Schmidt, Galois descent for `Pic⁰` (G1-2 rest, G1-3, review R7)
* `Def_RP_JacFrob_Setup`: S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`
* `Def_RP_JacFrob_FF`: S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`
* `Def_RP_JacFrob_Sig`: S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`
* `Def_RP_JacFrob_Phi`: S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_RRk =====
section

/-!
# S4-JacLaw, file O4c: the Riemann-Roch dictionary for the chart ring `B = Rfin K F`

* `IsInf H`: `H` vanishes at the finite places. `Linf H := L(H) ∩ B` as a `K`-subspace of `B`;
  `finrank_Linf` (`= ℓ(H)`, since `L(H) ⊆ B`), `finrank_Linf_eq` (`= deg H + 1 - g` for `deg H ≥ 2g - 1`).
* `mul_mem_Linf`, `poleDiv f = (-div f) ⊔ 0`, `mem_Linf_poleDiv`.
* `ExactPole s Pinf N`: `ord_P s = -N` at `Pinf` and `0` at the other infinite places. Then
  `s ∈ Linf (N • ptInf Pinf)`, `L(H) ∩ s B = s L(H - N Pinf)` (`mem_Linf_sub_of_mul`) and `dim_K B/(s) = N`
  (`finrank_quot_of_exactPole`, when `deg Pinf = 1`).
* `deg_eq_one`: over an algebraically closed `K` every place has degree one; `constField_eq_bot'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section RRk

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- `H` vanishes at the finite places. -/
def IsInf (H : Places.Divisor K F) : Prop := ∀ P : HeightOneSpectrum (Places.Rfin K F), H (Sum.inl P) = 0

theorem IsInf.add {H H' : Places.Divisor K F} (h : IsInf H) (h' : IsInf H') : IsInf (H + H') := fun P => by
  simp [h P, h' P]

theorem IsInf.sub {H H' : Places.Divisor K F} (h : IsInf H) (h' : IsInf H') : IsInf (H - H') := fun P => by
  simp [h P, h' P]

theorem IsInf.nsmul {H : Places.Divisor K F} (h : IsInf H) (n : ℕ) : IsInf (n • H) := fun P => by
  simp [h P]

/-- The divisor `1 · P` of an infinite place. -/
noncomputable def ptInf (P : HeightOneSpectrum (Places.Rinf K F)) : Places.Divisor K F :=
  Finsupp.single (Sum.inr P) 1

theorem isInf_ptInf (P : HeightOneSpectrum (Places.Rinf K F)) : IsInf (ptInf P) := fun Q => by
  simp [ptInf]

variable (K F) in
/-- The inclusion `B → F` as a `K`-algebra map. -/
noncomputable def incB : Places.Rfin K F →ₐ[K] F := IsScalarTower.toAlgHom K (Places.Rfin K F) F

theorem incB_apply (b : Places.Rfin K F) : incB K F b = algebraMap (Places.Rfin K F) F b := rfl

theorem incB_injective : Function.Injective (incB K F) := fun a b h => Subtype.ext h

variable (K F) in
/-- `L(H) ∩ B` as a `K`-subspace of `B`. -/
noncomputable def Linf (H : Places.Divisor K F) : Submodule K (Places.Rfin K F) :=
  (LFK K F H).comap (incB K F).toLinearMap

theorem mem_Linf {H : Places.Divisor K F} {b : Places.Rfin K F} : b ∈ Linf K F H ↔ incB K F b ∈ LFK K F H :=
  Iff.rfl

theorem ord_incB_nonneg (P : HeightOneSpectrum (Places.Rfin K F)) (b : Places.Rfin K F) :
    0 ≤ Places.ord P (incB K F b) := by
  by_cases hb : b = 0
  · subst hb; simp [Places.ord]
  · rw [incB_apply, PlacesK.ord_algebraMap P hb]; exact Nat.cast_nonneg _

theorem exists_incB_eq {H : Places.Divisor K F} (hH : IsInf H) {f : F} (hf : f ∈ LFK K F H) :
    ∃ b, incB K F b = f := by
  have : f ∈ (algebraMap (Places.Rfin K F) F).range := by
    rw [mem_range_iff_valuation_le_oneK]
    intro P
    have h := (Data.mem_LD (ffDataK K F)).mp hf (Sum.inl P)
    rw [hH P, exp_zero] at h
    exact h
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb⟩

theorem finrank_Linf {H : Places.Divisor K F} (hH : IsInf H) : finrank K (Linf K F H) = ellFK K F H := by
  let φ : Linf K F H →ₗ[K] LFK K F H :=
    ((incB K F).toLinearMap.domRestrict (Linf K F H)).codRestrict (LFK K F H) fun b => b.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => ?_, fun f => ?_⟩
    · have h' := congrArg Subtype.val h
      exact Subtype.ext (incB_injective h')
    obtain ⟨b, hb⟩ := exists_incB_eq hH f.2
    exact ⟨⟨b, show incB K F b ∈ LFK K F H from hb ▸ f.2⟩, Subtype.ext hb⟩
  exact (LinearEquiv.ofBijective φ hφ).finrank_eq

theorem finrank_Linf_eq (hk : Places.constField K F = ⊥) {H : Places.Divisor K F} (hH : IsInf H)
    (hd : 2 * (genusFK K F : ℤ) - 1 ≤ H.deg) :
    (finrank K (Linf K F H) : ℤ) = H.deg + 1 - genusFK K F := by
  rw [finrank_Linf hH]; exact ellFK_eq_of_deg hk hd

theorem mul_mem_Linf {D₁ D₂ : Places.Divisor K F} {s y : Places.Rfin K F} (hs : s ∈ Linf K F D₁)
    (hy : y ∈ Linf K F D₂) : s * y ∈ Linf K F (D₁ + D₂) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have hy' : incB K F y ≠ 0 := fun h => hy0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hs'] at hs
  rw [mem_Linf, mem_LFK hy'] at hy
  rw [mem_Linf, map_mul, mem_LFK (mul_ne_zero hs' hy'), PlacesK.div_mul hs' hy']
  have := add_nonneg hs hy
  rwa [add_add_add_comm] at this

/-- The pole divisor `(-div f) ⊔ 0`. -/
noncomputable def poleDiv (f : F) : Places.Divisor K F := (-PlacesK.div f) ⊔ 0

theorem isInf_poleDiv (b : Places.Rfin K F) : IsInf (poleDiv (K := K) (incB K F b)) := fun P => by
  have := ord_incB_nonneg P b
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inl,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_right.mpr (by omega)

theorem mem_Linf_poleDiv (b : Places.Rfin K F) : b ∈ Linf K F (poleDiv (K := K) (incB K F b)) := by
  by_cases hb : b = 0
  · simp [hb]
  have hb' : incB K F b ≠ 0 := fun h => hb (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hb', Finsupp.le_def]
  intro P
  simp only [poleDiv, Finsupp.coe_add, Pi.add_apply, Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  omega

theorem deg_nonneg_of_nonneg {D : Places.Divisor K F} (hD : 0 ≤ D) : 0 ≤ D.deg := by
  unfold Places.Divisor.deg
  exact Finsupp.sum_nonneg fun P _ => mul_nonneg (hD P) (Nat.cast_nonneg _)

theorem deg_poleDiv_nonneg (f : F) : 0 ≤ (poleDiv (K := K) f).deg :=
  deg_nonneg_of_nonneg le_sup_right

/-- `s` has an exact pole of order `N` at `Pinf` and no other zero or pole at infinity. -/
def ExactPole (s : Places.Rfin K F) (Pinf : HeightOneSpectrum (Places.Rinf K F)) (N : ℕ) : Prop :=
  ∀ P : HeightOneSpectrum (Places.Rinf K F), Places.ord P (incB K F s) = if P = Pinf then -(N : ℤ) else 0

variable {s : Places.Rfin K F} {Pinf : HeightOneSpectrum (Places.Rinf K F)} {N : ℕ}

theorem mem_Linf_of_exactPole (hs : ExactPole s Pinf N) : s ∈ Linf K F (N • ptInf Pinf) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P s
    simp [ptInf, this]
  · have := hs P
    by_cases hP : P = Pinf
    · subst hP; simp [ptInf, this]
    · simp [ptInf, this, hP, Ne.symm hP]

theorem mem_Linf_sub_of_mul (hs0 : s ≠ 0) (hs : ExactPole s Pinf N) {H : Places.Divisor K F} (hH : IsInf H)
    {y : Places.Rfin K F} (hz : s * y ∈ Linf K F H) : y ∈ Linf K F (H - N • ptInf Pinf) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have hy' : incB K F y ≠ 0 := fun h => hy0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, map_mul, mem_LFK (mul_ne_zero hs' hy'), PlacesK.div_mul hs' hy', Finsupp.le_def] at hz
  rw [mem_Linf, mem_LFK hy', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P y
    simp [ptInf, hH P, this]
  · have h1 := hz (Sum.inr P)
    have h2 := hs P
    simp only [Finsupp.coe_add, Pi.add_apply, PlacesK.div_apply, Places.Place.ord_inr, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    by_cases hP : P = Pinf
    · subst hP
      have h2' : Places.ord P (incB K F s) = -(N : ℤ) := by rw [h2]; simp
      simp [ptInf]; omega
    · simp only [if_neg hP] at h2; simp [ptInf, hP, Ne.symm hP]; omega

theorem finrank_quot_of_exactPole (hs0 : s ≠ 0) (hs : ExactPole s Pinf N) (hdeg : Places.deg K Pinf = 1) :
    finrank K (Places.Rfin K F ⧸ Ideal.span {s}) = N := by
  have h1 := PlacesK.finrank_quot_span (K := K) hs0
  have h2 := PlacesK.degS_divS_algebraMap (K := K) (L := F) hs0
  have h3 := PlacesK.degS_fin_add_degS_inf (K := K) (F := F)
    (f := algebraMap (Places.Rfin K F) F s) (fun h => hs0 (incB_injective (h.trans (map_zero _).symm)))
  have h4 : PlacesK.divS (Places.Rinf K F) (algebraMap (Places.Rfin K F) F s) = Finsupp.single Pinf (-(N : ℤ)) := by
    ext P
    rw [PlacesK.divS_apply, Finsupp.single_apply, ← incB_apply, hs P]
    by_cases hP : P = Pinf
    · simp [hP]
    · simp [hP, Ne.symm hP]
  rw [h4] at h3
  unfold Places.degS at h3
  rw [Finsupp.sum_single_index (by simp), hdeg, ← Places.degS, h2, ← h1] at h3
  push_cast at h3
  omega

end RRk

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem deg_eq_one {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra K S] [PlacesK.FDQ K S]
    (P : HeightOneSpectrum S) : Places.deg K P = 1 := by
  haveI := PlacesK.moduleFinite_residue (K := K) P
  haveI := P.isPrime
  have hs : Function.Surjective (algebraMap K (S ⧸ P.asIdeal)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)).2
  have hb : Function.Bijective (Algebra.linearMap K (S ⧸ P.asIdeal)) :=
    ⟨(algebraMap K (S ⧸ P.asIdeal)).injective, hs⟩
  rw [Places.deg, ← (LinearEquiv.ofBijective _ hb).finrank_eq, finrank_self]

variable [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem constField_eq_bot' : Places.constField K F = ⊥ := by
  obtain ⟨P⟩ := PlacesK.nonempty_infPlace K F
  exact PlacesK.constField_eq_bot_of_deg_one K F (P := Sum.inr P) (deg_eq_one P)

end AlgClosed

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Exact =====
section

/-!
# S4-JacLaw, file O6a: exact poles from hyperplane conditions

* The places at infinity are finitely many (each contains `1/x`): `Finite` instance.
* `Linf_mono`.
* `exactPole_of_not_mem`: a nonzero `s ∈ L(N P∞) ∩ B` outside every hyperplane `L(N P∞ - P')`
  (`P'` at infinity) has an exact pole of order `N` at `P∞` and no other zero or pole at infinity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section Exact

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The image of `1/x` in `Rinf`. -/
noncomputable abbrev piR : Places.Rinf K F :=
  algebraMap (Places.Oinf K) (Places.Rinf K F) (Places.piInf K)

theorem piR_ne_zero : piR K F ≠ 0 := by
  intro h
  have h2 : algebraMap (Places.Oinf K) F (Places.piInf K) = 0 := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Places.Oinf K) (RatFunc K) F] at h2
  have h3 : ((Places.piInf K : Places.Oinf K) : RatFunc K) = 0 :=
    (FaithfulSMul.algebraMap_injective (RatFunc K) F) (h2.trans (map_zero _).symm)
  exact Places.piInf_ne_zero K (Subtype.ext h3)

/-- Every place over `x = ∞` contains `1/x`. -/
theorem piR_mem (P : HeightOneSpectrum (Places.Rinf K F)) : piR K F ∈ P.asIdeal := by
  have := P.isMaximal
  have h1 : (P.asIdeal.comap (algebraMap (Places.Oinf K) (Places.Rinf K F))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have h2 := IsLocalRing.eq_maximalIdeal h1
  have h3 := IsLocalRing.eq_maximalIdeal (Places.span_piInf_isMaximal K)
  have h4 : Places.piInf K ∈ P.asIdeal.comap (algebraMap (Places.Oinf K) (Places.Rinf K F)) := by
    rw [h2, ← h3]; exact Ideal.mem_span_singleton_self _
  exact h4

instance finite_infPlaces : Finite (HeightOneSpectrum (Places.Rinf K F)) := by
  have hfin : {P : HeightOneSpectrum (Places.Rinf K F) | P.asIdeal ∣ Ideal.span {piR K F}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact piR_ne_zero)
  refine Set.finite_univ_iff.mp (hfin.subset fun P _ => ?_)
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (piR_mem P))

theorem Linf_mono {H H' : Places.Divisor K F} (h : H ≤ H') : Linf K F H ≤ Linf K F H' := by
  intro b hb
  by_cases hb0 : b = 0
  · rw [hb0]; exact Submodule.zero_mem _
  have hb' : incB K F b ≠ 0 := fun h => hb0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hb'] at hb ⊢
  exact hb.trans (add_le_add le_rfl h)

variable {s : Places.Rfin K F} {Pinf : HeightOneSpectrum (Places.Rinf K F)} {N : ℕ}

/-- **Exact pole from hyperplane conditions.** -/
theorem exactPole_of_not_mem (hs0 : s ≠ 0) (hs : s ∈ Linf K F (N • ptInf Pinf))
    (hP : ∀ P' : HeightOneSpectrum (Places.Rinf K F), s ∉ Linf K F (N • ptInf Pinf - ptInf P')) :
    ExactPole s Pinf N := by
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  intro P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def] at hs
  have h1 := hs (Sum.inr P)
  by_contra hne
  apply hP P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (Q | Q)
  · have h2 := hs (Sum.inl Q)
    simpa [ptInf] using h2
  · have h2 := hs (Sum.inr Q)
    by_cases hQ : Q = P
    · subst hQ
      by_cases hP' : Q = Pinf
      · subst hP'
        simp [ptInf] at h1 hne ⊢
        omega
      · simp [ptInf, hP'] at h1 hne ⊢
        omega
    · simp [ptInf, hQ] at h2 ⊢
      exact h2

end Exact

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_RRkH =====
section

/-!
# S4-JacLaw, file X2: exact pole divisors `Hn` at infinity (generalising `N • P∞`)

* `ExactPoleH s Hn`: `ord_P s = -Hn(P)` at every infinite place `P`.
* `mem_Linf_of_exactPoleH`, `mem_Linf_sub_of_mulH` (`L(H) ∩ s B = s L(H - Hn)`),
  `finrank_quot_of_exactPoleH` (`dim_K B/(s) = deg Hn`, no degree hypothesis on the places),
  `exactPoleH_of_not_mem` (exact poles from hyperplane conditions).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section RRkH

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- `s` has pole divisor exactly `Hn` at infinity (and no zeros there). -/
def ExactPoleH (s : Places.Rfin K F) (Hn : Places.Divisor K F) : Prop :=
  ∀ P : HeightOneSpectrum (Places.Rinf K F), Places.ord P (incB K F s) = -Hn (Sum.inr P)

variable {s : Places.Rfin K F} {Hn : Places.Divisor K F}

theorem mem_Linf_of_exactPoleH (hHn : IsInf Hn) (hs : ExactPoleH s Hn) : s ∈ Linf K F Hn := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P s
    simp [hHn P, this]
  · have := hs P
    simp [this]

theorem mem_Linf_sub_of_mulH (hs0 : s ≠ 0) (hs : ExactPoleH s Hn) (hHn : IsInf Hn) {H : Places.Divisor K F}
    (hH : IsInf H) {y : Places.Rfin K F} (hz : s * y ∈ Linf K F H) : y ∈ Linf K F (H - Hn) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have hy' : incB K F y ≠ 0 := fun h => hy0 (incB_injective (h.trans (map_zero _).symm))
  rw [mem_Linf, map_mul, mem_LFK (mul_ne_zero hs' hy'), PlacesK.div_mul hs' hy', Finsupp.le_def] at hz
  rw [mem_Linf, mem_LFK hy', Finsupp.le_def]
  rintro (P | P)
  · have := ord_incB_nonneg P y
    simp [hH P, hHn P, this]
  · have h1 := hz (Sum.inr P)
    have h2 := hs P
    simp only [Finsupp.coe_add, Pi.add_apply, PlacesK.div_apply, Places.Place.ord_inr, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, PlacesK.div_apply,
      Places.Place.ord_inr, Finsupp.coe_zero, Pi.zero_apply]
    omega

/-- `dim_K B/(s) = deg Hn` (product formula). -/
theorem finrank_quot_of_exactPoleH (hs0 : s ≠ 0) (hHn : IsInf Hn) (hs : ExactPoleH s Hn) :
    (finrank K (Places.Rfin K F ⧸ Ideal.span {s}) : ℤ) = Hn.deg := by
  have h1 := PlacesK.finrank_quot_span (K := K) hs0
  have h2 := PlacesK.degS_divS_algebraMap (K := K) (L := F) hs0
  have hs' : algebraMap (Places.Rfin K F) F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  have e : Hn + PlacesK.div (algebraMap (Places.Rfin K F) F s) =
      (PlacesK.divS (Places.Rfin K F) (algebraMap (Places.Rfin K F) F s)).sumElim 0 := by
    ext (P | P)
    · simp [PlacesK.div, hHn P]
    · have this : Places.ord P (s : F) = -Hn (Sum.inr P) := hs P
      simp [PlacesK.div]
      omega
  have h3 := congrArg Places.Divisor.deg e
  rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hs', PlacesK.Divisor.deg_sumElim] at h3
  have h4 : Places.degS K (0 : HeightOneSpectrum (Places.Rinf K F) →₀ ℤ) = 0 := by
    unfold Places.degS; simp
  rw [h4, h2, ← h1] at h3
  omega

/-- **Exact pole divisor from hyperplane conditions.** -/
theorem exactPoleH_of_not_mem (hs0 : s ≠ 0) (hs : s ∈ Linf K F Hn)
    (hP : ∀ P' : HeightOneSpectrum (Places.Rinf K F), s ∉ Linf K F (Hn - ptInf P')) : ExactPoleH s Hn := by
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  intro P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def] at hs
  have h1 := hs (Sum.inr P)
  by_contra hne
  apply hP P
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def]
  rintro (Q | Q)
  · have h2 := hs (Sum.inl Q)
    simpa [ptInf] using h2
  · have h2 := hs (Sum.inr Q)
    by_cases hQ : Q = P
    · subst hQ
      simp [ptInf] at h1 ⊢
      omega
    · simp [ptInf, hQ] at h2 ⊢
      exact h2

end RRkH

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_GenFib =====
section

/-!
# S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets

`xB = x ∈ B` (the chart coordinate), `n = rank_{K[X]} B = [F : K(x)]`.
* `finrank_quot_poly`: `dim_K B/(q(x)) = deg q · n`.
* `exactPoleH_poly`: `q(x)` has exact pole divisor `poleDiv q(x)` at infinity (no zeros there).
* `exists_fib_card`: for all but finitely many `c` the fibre `x = c` has exactly `n` points (IsogDegA).
* `exists_fib_data`: for a finset `Λ` of good values, `s = ∏_{c∈Λ} (x - c)` has exact pole divisor of degree
  `|Λ| n` and exactly `|Λ| n` zeros, namely the points with `x ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section Fib

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (K F) in
/-- The chart coordinate `x ∈ B`. -/
noncomputable abbrev xB : Places.Rfin K F := algebraMap K[X] (Places.Rfin K F) X

theorem algebraMap_poly_injective : Function.Injective (algebraMap K[X] (Places.Rfin K F)) := by
  intro p q h
  apply FaithfulSMul.algebraMap_injective K[X] F
  rw [IsScalarTower.algebraMap_apply K[X] (Places.Rfin K F) F, h, ← IsScalarTower.algebraMap_apply]

/-- `dim_K B/(q(x)) = deg q · n`. -/
theorem finrank_quot_poly {q : K[X]} (hq : q ≠ 0) :
    finrank K (Places.Rfin K F ⧸ Ideal.span {algebraMap K[X] (Places.Rfin K F) q}) =
      q.natDegree * finrank K[X] (Places.Rfin K F) := by
  have hf : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis K[X] (Places.Rfin K F)) hf,
    Algebra.norm_algebraMap, natDegree_pow, mul_comm]

theorem incB_poly (q : K[X]) :
    incB K F (algebraMap K[X] (Places.Rfin K F) q) =
      algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) q) := by
  rw [incB_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K[X] (RatFunc K) F]

/-- `q(x)` has no zero at infinity. -/
theorem ord_inf_poly_nonpos {q : K[X]} (hq : q ≠ 0) (P : HeightOneSpectrum (Places.Rinf K F)) :
    Places.ord P (incB K F (algebraMap K[X] (Places.Rfin K F) q)) ≤ 0 := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hq
  set r : RatFunc K := (algebraMap K[X] (RatFunc K) q)⁻¹ with hr
  have hr0 : r ≠ 0 := inv_ne_zero hq'
  have hrO : r ∈ Places.Oinf K := by
    rw [Places.mem_Oinf_iff' K hr0, hr, RatFunc.intDegree_inv, RatFunc.intDegree_polynomial]
    omega
  set t : Places.Rinf K F := algebraMap (Places.Oinf K) (Places.Rinf K F) ⟨r, hrO⟩ with ht
  have ht0 : t ≠ 0 := by
    intro h
    apply hr0
    have h1 : (⟨r, hrO⟩ : Places.Oinf K) = 0 :=
      PlacesK.algebraMap_Oinf_Rinf_injective K F (h.trans (map_zero _).symm)
    exact congrArg Subtype.val h1
  have htF : algebraMap (Places.Rinf K F) F t = algebraMap (RatFunc K) F r := by
    rw [ht, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Places.Oinf K) (RatFunc K) F]
    rfl
  have hprod : incB K F (algebraMap K[X] (Places.Rfin K F) q) * algebraMap (Places.Rinf K F) F t = 1 := by
    rw [incB_poly, htF, hr, ← map_mul, mul_inv_cancel₀ hq', map_one]
  have hs0 : incB K F (algebraMap K[X] (Places.Rfin K F) q) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have htF0 : algebraMap (Places.Rinf K F) F t ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have h1 := PlacesK.ord_mul P hs0 htF0
  rw [hprod, PlacesK.ord_algebraMap P ht0] at h1
  have h2 : Places.ord P (1 : F) = 0 := by simp [Places.ord]
  rw [h2] at h1
  omega

/-- `q(x)` has exact pole divisor `poleDiv q(x)` at infinity. -/
theorem exactPoleH_poly {q : K[X]} (hq : q ≠ 0) :
    ExactPoleH (algebraMap K[X] (Places.Rfin K F) q)
      (poleDiv (K := K) (incB K F (algebraMap K[X] (Places.Rfin K F) q))) := by
  intro P
  have := ord_inf_poly_nonpos (F := F) hq P
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inr,
    Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem deg_poleDiv_poly {q : K[X]} (hq : q ≠ 0) :
    (poleDiv (K := K) (incB K F (algebraMap K[X] (Places.Rfin K F) q))).deg =
      ((q.natDegree * finrank K[X] (Places.Rfin K F) : ℕ) : ℤ) := by
  have hf : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq
  rw [← finrank_quot_poly hq]
  exact (finrank_quot_of_exactPoleH hf (isInf_poleDiv _) (exactPoleH_poly hq)).symm

theorem apply_poly (φ : Places.Rfin K F →ₐ[K] K) (q : K[X]) :
    φ (algebraMap K[X] (Places.Rfin K F) q) = q.eval (φ (xB K F)) := by
  have e : φ.comp (IsScalarTower.toAlgHom K K[X] (Places.Rfin K F)) = Polynomial.aeval (φ (xB K F)) :=
    Polynomial.algHom_ext (by simp)
  have := congrArg (fun ψ : K[X] →ₐ[K] K => ψ q) e
  simpa [coe_aeval_eq_eval] using this

section AlgClosed

variable [IsAlgClosed K]

theorem fib_iff (c : K) (φ : Places.Rfin K F →ₐ[K] K) :
    φ.comp (IsScalarTower.toAlgHom K K[X] (Places.Rfin K F)) = Polynomial.aeval c ↔ φ (xB K F) = c := by
  constructor
  · intro h
    have := congrArg (fun ψ : K[X] →ₐ[K] K => ψ X) h
    simpa using this
  · intro h
    exact Polynomial.algHom_ext (by simpa using h)

/-- **Generic fibres of `x`.** For all `c` off the roots of some `a ≠ 0` the fibre `x = c` has `n` points. -/
theorem exists_fib_card : ∃ a : K[X], a ≠ 0 ∧ ∀ c : K, a.eval c ≠ 0 →
    {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) = c}.Finite ∧
      Nat.card {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} = finrank K[X] (Places.Rfin K F) := by
  obtain ⟨a, ha, h⟩ := IsogDegA.exists_card_fiber_eq_finSepDegree (R := K[X]) (B := Places.Rfin K F)
    (RatFunc K) F K
  refine ⟨a, ha, fun c hc => ?_⟩
  have hχ : (Polynomial.aeval c : K[X] →ₐ[K] K) a ≠ 0 := by rwa [coe_aeval_eq_eval]
  obtain ⟨hfin, hcard⟩ := h (Polynomial.aeval c) hχ
  let E : IsogDegA.fiber K (Places.Rfin K F) (Polynomial.aeval c) ≃
      {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} := Equiv.subtypeEquivRight (fib_iff c)
  have hrank : Field.finSepDegree (RatFunc K) F = finrank K[X] (Places.Rfin K F) := by
    rw [Field.finSepDegree_eq_finrank_of_isSeparable]
    exact (IsIntegralClosure.rank K[X] (RatFunc K) F (Places.Rfin K F)).symm
  refine ⟨?_, ?_⟩
  · have : Finite {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} := Finite.of_equiv _ E
    exact Set.finite_coe_iff.1 this
  · rw [← Nat.card_congr E, hcard, hrank]

/-- **Sections `∏ (x - c)` over good values.** -/
theorem exists_fib_data : ∃ a : K[X], a ≠ 0 ∧ ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) →
    ∃ s : Places.Rfin K F, ∃ Z : Finset (Places.Rfin K F →ₐ[K] K),
      s ≠ 0 ∧ ExactPoleH s (poleDiv (K := K) (incB K F s)) ∧
      (poleDiv (K := K) (incB K F s)).deg = ((Λ.card * finrank K[X] (Places.Rfin K F) : ℕ) : ℤ) ∧
      (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ (∀ φ, φ ∈ Z ↔ φ (xB K F) ∈ Λ) ∧
      Z.card = Λ.card * finrank K[X] (Places.Rfin K F) := by
  obtain ⟨a, ha, h⟩ := exists_fib_card (K := K) (F := F)
  refine ⟨a, ha, fun Λ hΛ => ?_⟩
  set q : K[X] := ∏ c ∈ Λ, (X - C c) with hq
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c
  have hqdeg : q.natDegree = Λ.card := by
    rw [hq, natDegree_prod _ _ fun c _ => X_sub_C_ne_zero c]
    simp
  have hs0 : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq0
  have hzero : ∀ φ : Places.Rfin K F →ₐ[K] K,
      φ (algebraMap K[X] (Places.Rfin K F) q) = 0 ↔ φ (xB K F) ∈ Λ := by
    intro φ
    rw [apply_poly, hq, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hfinΛ : {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) ∈ Λ}.Finite := by
    have : {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) ∈ Λ} =
        ⋃ c ∈ Λ, {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) = c} := by
      ext φ; simp
    rw [this]
    exact Set.Finite.biUnion Λ.finite_toSet fun c hc => (h c (hΛ c hc)).1
  set Z := hfinΛ.toFinset with hZ
  have hmem : ∀ φ, φ ∈ Z ↔ φ (xB K F) ∈ Λ := fun φ => by rw [hZ, Set.Finite.mem_toFinset]; rfl
  refine ⟨algebraMap K[X] (Places.Rfin K F) q, Z, hs0, exactPoleH_poly hq0, ?_, fun φ => by rw [hmem, hzero],
    hmem, ?_⟩
  · rw [deg_poleDiv_poly hq0, hqdeg]
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun φ : Places.Rfin K F →ₐ[K] K => φ (xB K F)) (t := Λ)
      (fun φ hφ => (hmem φ).1 hφ)]
    refine Finset.sum_const_nat fun c hc => ?_
    have hc' := h c (hΛ c hc)
    have e2 : Nat.card {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} = hc'.1.toFinset.card :=
      Nat.card_eq_card_finite_toFinset hc'.1
    rw [← hc'.2, e2]
    congr 1
    ext φ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hmem]
    constructor
    · rintro ⟨-, e⟩; exact e
    · intro e; exact ⟨e ▸ hc, e⟩

end AlgClosed

end Fib

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_PicDescent_E4 =====
section

/-!
# S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`

For a function field `F / Fq` with full constant field `K = constField Fq F` (`#K = q ^ d`, `d = [K : Fq]`,
`card_constField`), `F` is rebased as a function field over `K` with the same separating element `x`:
* instances `Algebra K[X] F` (`x ↦ xF Fq F`), `Algebra (RatFunc K) F`, the towers, `FunctionField K F`,
  `Algebra.IsSeparable (RatFunc K) F`; `xF_constField : xF K F = xF Fq F`;
* `constField_K : constField K F = ⊥` (`F / K` is geometrically connected),
  `exists_deg_one_K` (F. K. Schmidt over `K`), `finite_Pic0_K`;
so parts A–E apply over `K` with `q ^ d` in place of `q`; the `K`-Frobenius is `π ^ d` (`mem_Lc_K`).
Restated over `K`: `picBarEquivK`, `pic0BarEquivK`, `picBaseEquivK`, `pic0BaseEquivK`, `classNumber_barK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Rebase

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

noncomputable instance fintype_constField : Fintype (constField Fq F) :=
  @Fintype.ofFinite _ (Module.finite_of_finite Fq)

/-- `#K = q ^ d` with `d = [K : Fq]`. -/
theorem card_constField :
    Fintype.card (constField Fq F) = Fintype.card Fq ^ Module.finrank Fq (constField Fq F) :=
  Module.card_eq_pow_finrank

noncomputable instance decEq_ratK : DecidableEq (RatFunc (constField Fq F)) := Classical.decEq _

/-- `K[X] → F`, `X ↦ x`. -/
noncomputable instance algebra_polyK : Algebra (constField Fq F)[X] F :=
  (aeval (RR.xF Fq F)).toRingHom.toAlgebra

theorem algebraMap_polyK (p : (constField Fq F)[X]) :
    algebraMap (constField Fq F)[X] F p = aeval (RR.xF Fq F) p := rfl

instance isScalarTower_polyK : IsScalarTower (constField Fq F) (constField Fq F)[X] F :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (RR.xF Fq F) a).symm

theorem transcendental_xK : Transcendental (constField Fq F) (RR.xF Fq F) :=
  (transcendental_xF Fq F).extendScalars (constField Fq F)

theorem aeval_xK_injective : Function.Injective (aeval (R := constField Fq F) (RR.xF Fq F)) :=
  transcendental_iff_injective.1 (transcendental_xK Fq F)

/-- `K(X) → F`, `X ↦ x`. -/
noncomputable instance algebra_ratK : Algebra (RatFunc (constField Fq F)) F :=
  (RatFunc.liftAlgHom (aeval (RR.xF Fq F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (aeval_xK_injective Fq F))).toRingHom.toAlgebra

theorem algebraMap_ratK (g : RatFunc (constField Fq F)) :
    algebraMap (RatFunc (constField Fq F)) F g = RatFunc.liftAlgHom (aeval (RR.xF Fq F))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xK_injective Fq F)) g :=
  rfl

instance isScalarTower_ratK :
    IsScalarTower (constField Fq F)[X] (RatFunc (constField Fq F)) F :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratK, ← div_one (algebraMap (constField Fq F)[X] (RatFunc (constField Fq F)) p),
      ← map_one (algebraMap (constField Fq F)[X] (RatFunc (constField Fq F))),
      RatFunc.liftAlgHom_apply_div, map_one, div_one, algebraMap_polyK]

/-- The separating element is the same over `Fq` and over `K`. -/
theorem xF_constField : RR.xF (constField Fq F) F = RR.xF Fq F := by
  show algebraMap (constField Fq F)[X] F X = _
  rw [algebraMap_polyK, aeval_X]

theorem hx_K : algebraMap F F (RR.xF Fq F) = RR.xF (constField Fq F) F :=
  (xF_constField Fq F).symm

instance functionField_K : FunctionField (constField Fq F) F := by
  let _ : Algebra (RatFunc Fq) (RatFunc (constField Fq F)) := (ratMap Fq (constField Fq F)).toAlgebra
  have : IsScalarTower (RatFunc Fq) (RatFunc (constField Fq F)) F :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (F := F) (F' := F) (hx_K Fq F)) g).symm
  exact Module.Finite.of_restrictScalars_finite (RatFunc Fq) (RatFunc (constField Fq F)) F

instance isSeparable_ratK : Algebra.IsSeparable (RatFunc (constField Fq F)) F := by
  let _ : Algebra (RatFunc Fq) (RatFunc (constField Fq F)) := (ratMap Fq (constField Fq F)).toAlgebra
  have : IsScalarTower (RatFunc Fq) (RatFunc (constField Fq F)) F :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (F := F) (F' := F) (hx_K Fq F)) g).symm
  exact Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) (RatFunc (constField Fq F)) F

/-- **`F / K` is geometrically connected**: the full constant field of `F` over `K` is `K`. -/
theorem constField_K : constField (constField Fq F) F = ⊥ :=
  algebraicClosure.algebraicClosure_eq_bot Fq F

/-- **F. K. Schmidt over the full constant field**: a divisor of `K`-degree `1` exists. -/
theorem exists_deg_one_K : ∃ D : Divisor (constField Fq F) F, Divisor.deg D = 1 :=
  exists_deg_one (constField Fq F) F (constField_K Fq F)

theorem finite_Pic0_K : Finite (Pic0 (constField Fq F) F) := finite_Pic0 (constField_K Fq F)

/-- The `K`-Frobenius `x ↦ x ^ (q ^ d)` is `π ^ d`: `L_m` over `K` is `L_(d m)` over `Fq`. -/
theorem mem_Lc_K {Ω : Type*} [Field Ω] [Algebra F Ω] {m : ℕ} {x : Ω} :
    x ∈ Lc (constField Fq F) Ω m ↔
      x ^ Fintype.card Fq ^ (Module.finrank Fq (constField Fq F) * m) = x := by
  rw [mem_Lc, card_constField, ← pow_mul]

section Descent

-- `Algebra K Ω` and `IsScalarTower K F Ω` are Mathlib's intermediate-field instances (through `F`).
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

variable (Ω) in
/-- **R6 descent** over the full constant field `K`: `Pic(X_m) ≃+ Pic(X̄)^(π_K ^ m)`, `π_K = π ^ d`. -/
noncomputable def picBarEquivK (m : ℕ) [NeZero m] :
    Pic (Lc (constField Fq F) Ω m) (Fc (constField Fq F) F Ω m) ≃+ fixedBar Ω (constField_K Fq F) m :=
  picBarEquiv Ω (constField_K Fq F) m

variable (Ω) in
/-- **R6 descent** for `Pic⁰`: `Pic⁰(X_m) ≃+ Pic⁰(X̄)^(π_K ^ m)`. -/
noncomputable def pic0BarEquivK (m : ℕ) [NeZero m] :
    Pic0 (Lc (constField Fq F) Ω m) (Fc (constField Fq F) F Ω m) ≃+
      (fixedBar Ω (constField_K Fq F) m ⊓ PicBar0 Ω (constField_K Fq F) :
        AddSubgroup (PicBar Ω (constField_K Fq F))) :=
  pic0BarEquiv Ω (constField_K Fq F) m

variable (Ω) in
/-- **R6** for `F` itself over `K`: `Pic(X) ≃+ Pic(X̄)^(π_K)`. -/
noncomputable def picBaseEquivK : Pic (constField Fq F) F ≃+ fixedBar Ω (constField_K Fq F) 1 :=
  picBaseEquiv Ω (constField_K Fq F)

variable (Ω) in
/-- **R6** for `F` itself over `K`: `Pic⁰(X) ≃+ Pic⁰(X̄)^(π_K)`. -/
noncomputable def pic0BaseEquivK :
    Pic0 (constField Fq F) F ≃+
      (fixedBar Ω (constField_K Fq F) 1 ⊓ PicBar0 Ω (constField_K Fq F) :
        AddSubgroup (PicBar Ω (constField_K Fq F))) :=
  pic0BaseEquiv Ω (constField_K Fq F)

variable (Ω) in
/-- **Class numbers over the full constant field** `K = F_(q^d)`: `#Pic⁰(X̄)^(π_K ^ m) = L_m(1) = Π (1 - ω_i ^ m)`,
`|ω_i| ≤ √(q ^ d)`, at most `2 g` of them. -/
theorem classNumber_barK :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * RR.genusF (constField Fq F) F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt ((Fintype.card Fq : ℝ) ^ Module.finrank Fq (constField Fq F))) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Places.numPoints (constField Fq F) F k : ℂ) =
          1 + ((Fintype.card Fq : ℂ) ^ Module.finrank Fq (constField Fq F)) ^ k - (c.map (· ^ k)).sum) ∧
      ∀ (m : ℕ) [NeZero m],
        Finite (fixedBar Ω (constField_K Fq F) m ⊓ PicBar0 Ω (constField_K Fq F) :
          AddSubgroup (PicBar Ω (constField_K Fq F))) ∧
        (Nat.card (fixedBar Ω (constField_K Fq F) m ⊓ PicBar0 Ω (constField_K Fq F) :
          AddSubgroup (PicBar Ω (constField_K Fq F))) : ℂ) = (Lpoly c m).eval 1 ∧
        (Lpoly c m).eval 1 = (c.map fun z => 1 - z ^ m).prod := by
  obtain ⟨c, h1, h2, h3, h4⟩ := classNumber_bar (Ω := Ω) (constField_K Fq F)
  refine ⟨c, h1, fun x hx => ?_, fun k hk => ?_, h4⟩
  · have h := h2 x hx
    rwa [card_constField, Nat.cast_pow] at h
  · rw [h3 k hk, card_constField, Nat.cast_pow]

end Descent

end Rebase

end RamanujanPetersson.PicDescent

end

-- ===== S4.Def_RP_PicDescent =====
section

/-!
# S4-PicDescent: class numbers `h_m = L_m(1)`, F. K. Schmidt, Galois descent for `Pic⁰` (G1-2 rest, G1-3, review R7)

Umbrella file of the unit (namespace `RamanujanPetersson.PicDescent`). `Fq` is a finite field with `q` elements,
`F / Fq` a function field (separable over `Fq(x)`), `hk : constField Fq F = ⊥` unless said otherwise;
`Ω` is an algebraically closed field over `F`; `F_m = Fc Fq F Ω m` is the constant field extension by
`L_m = Lc Fq Ω m` (`#L_m = q ^ m`), i.e. the function field of `X_m = X ×_{F_q} F_(q^m)`.

* Part A (`Def_RP_PicDescent_A`): `Pic`, `degPic`, `Pic0`; **F. K. Schmidt** `exists_deg_one hk` (a divisor of
  degree 1 exists); `finite_Pic0 hk`; **`classNumber_zeta hk`**: `#Pic⁰(X) = L(1) = Π (1 - ω_i)` with the zeta data
  `c` of S3 (`card c ≤ 2g`, `|ω_i| ≤ √q`, `N_k = 1 + q^k - Σ ω_i^k`).
* Part B (`B1`–`B4`): the constant field extensions `F_m` in coordinates (`RR.IsConstExt`, `isConstExt_Fc`,
  `genusF_Fc`, `constField_Fc`).
* Part C (`C1`, `C2`): `N_k(X_m) = N_{mk}(X)`; **`classNumber_Fc_zeta hk`**: for every `m ≥ 1`, `Pic⁰(X_m)` is finite
  and `h_m = #Pic⁰(X_m) = L_m(1) = Π (1 - ω_i ^ m)` (`Lpoly c m`, `eval_one_Lpoly`).
* Part H90 + D (`H90`, `D1`–`D5`): Hilbert 90 for the cyclic group `Gal(F_m / F) = ⟨π⟩` (`hilbert90_cyclic`),
  places and divisors under constant field extension, **`picEquiv h hk : Pic(X) ≃+ Pic(X_m)^π`** and
  **`pic0Equiv h hk : Pic⁰(X) ≃+ Pic⁰(X_m)^π`** (`π` = arithmetic `q`-power Frobenius, review R4).
* Part E (`E1`–`E3`): `Pic(X̄)` (`X̄ = F̄ ⊗ K`) as the direct limit `PicBar Ω hk` of `Pic(F_{(j+1)!})`, `π` on it
  (`piBar`), `PicBar0 = Pic⁰(X̄)`; **`picBarEquiv Ω hk m : Pic(X_m) ≃+ Pic(X̄)^(π^m)`**,
  **`pic0BarEquiv Ω hk m : Pic⁰(X_m) ≃+ Pic⁰(X̄)^(π^m)`**, `picBaseEquiv`, `pic0BaseEquiv` (`m = 1`),
  **`classNumber_bar hk`**: `#Pic⁰(X̄)^(π^m) = L_m(1) = Π (1 - ω_i ^ m)`.
* Part E4 (review R6, `E4`): any `F / Fq` with full constant field `K = constField Fq F = F_(q^d)`
  (`card_constField`) is a function field over `K` with `constField_K : constField K F = ⊥`; restated over `K`:
  `picBarEquivK`, `pic0BarEquivK`, `picBaseEquivK`, `pic0BaseEquivK`, `classNumber_barK` (`|ω_i| ≤ √(q^d)`),
  with `π_K = π ^ d` (`mem_Lc_K`).

`H²` input: `exists_conormPic_eq` (D5) lifts a `π`-fixed class by Hilbert 90 for `F_m / F` together with the
surjectivity of the norm `L_m^× → F_q^×` (`exists_pnorm_frob_eq`), i.e. `Br(F_q) = 0` for the procyclic group;
`conormPic_injective` uses Hilbert 90 for `L_m / F_q` (`hilbert90_cyclic`).
-/

set_option autoImplicit false

end

-- ===== S4.Def_RP_JacFrob_Setup =====
section

/-!
# S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`

`kbar = algebraicClosure Fq Ω` (an algebraic closure of `Fq`), `Fbar = F(kbar)` inside `Ω`, with the algebra
structures over `kbar`, `kbar[X]` and `RatFunc kbar` (`X ↦ x`) needed by `JacComplete.Jac kbar Fbar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent

section Setup

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

/-- `k-bar`: the algebraic closure of `Fq` inside `Ω`. -/
noncomputable abbrev kbar : IntermediateField Fq Ω := algebraicClosure Fq Ω

instance isAlgClosed_kbar [IsAlgClosed Ω] : IsAlgClosed (kbar Fq Ω) := IsAlgClosure.isAlgClosed Fq

/-- `F-bar = F · k-bar` inside `Ω`. -/
noncomputable def Fbar : IntermediateField F Ω := IntermediateField.adjoin F (kbar Fq Ω : Set Ω)

variable {Fq F Ω} in
theorem mem_Fbar_of_mem_kbar {x : Ω} (hx : x ∈ kbar Fq Ω) : x ∈ Fbar Fq F Ω :=
  IntermediateField.subset_adjoin F _ hx

/-- The inclusion `k-bar → F-bar`. -/
noncomputable def KtoF : kbar Fq Ω →+* Fbar Fq F Ω where
  toFun x := ⟨x, mem_Fbar_of_mem_kbar x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance algebra_kF : Algebra (kbar Fq Ω) (Fbar Fq F Ω) := (KtoF Fq F Ω).toAlgebra

theorem coe_algebraMap_kF (x : kbar Fq Ω) :
    ((algebraMap (kbar Fq Ω) (Fbar Fq F Ω) x : Fbar Fq F Ω) : Ω) = x := rfl

instance isScalarTower_kF : IsScalarTower Fq (kbar Fq Ω) (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

section FF

variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x` of `F`, inside `F-bar`. -/
noncomputable def xbar : Fbar Fq F Ω := algebraMap F (Fbar Fq F Ω) (RR.xF Fq F)

noncomputable instance algebra_polyK : Algebra (kbar Fq Ω)[X] (Fbar Fq F Ω) :=
  (aeval (xbar Fq F Ω)).toRingHom.toAlgebra

theorem algebraMap_polyK (p : (kbar Fq Ω)[X]) :
    algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) p = aeval (xbar Fq F Ω) p := rfl

instance isScalarTower_polyK : IsScalarTower (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (xbar Fq F Ω) a).symm

theorem transcendental_xbar : Transcendental (kbar Fq Ω) (xbar Fq F Ω) := by
  have h1 : Transcendental Fq (xbar Fq F Ω) := by
    rw [xbar, transcendental_algebraMap_iff (algebraMap F (Fbar Fq F Ω)).injective]
    exact transcendental_xF Fq F
  exact h1.extendScalars (kbar Fq Ω)

theorem aeval_xbar_injective : Function.Injective (aeval (R := kbar Fq Ω) (xbar Fq F Ω)) :=
  transcendental_iff_injective.1 (transcendental_xbar Fq F Ω)

noncomputable instance algebra_ratK : Algebra (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) :=
  (RatFunc.liftAlgHom (aeval (xbar Fq F Ω))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (aeval_xbar_injective Fq F Ω))).toRingHom.toAlgebra

theorem algebraMap_ratK (g : RatFunc (kbar Fq Ω)) :
    algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) g = RatFunc.liftAlgHom (aeval (xbar Fq F Ω))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xbar_injective Fq F Ω)) g :=
  rfl

instance isScalarTower_ratK :
    IsScalarTower (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratK, ← div_one (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) p),
      ← map_one (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω))), RatFunc.liftAlgHom_apply_div,
      map_one, div_one, algebraMap_polyK]

noncomputable instance decEq_ratK : DecidableEq (RatFunc (kbar Fq Ω)) := Classical.decEq _

theorem hx_Fbar : algebraMap F (Fbar Fq F Ω) (RR.xF Fq F) = RR.xF (kbar Fq Ω) (Fbar Fq F Ω) := by
  show xbar Fq F Ω = algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) X
  rw [algebraMap_polyK, aeval_X]

end FF

end Setup

end RamanujanPetersson.JacFrob

end

-- ===== S4.Def_RP_JacFrob_FF =====
section

/-!
# S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`

* `ratK : Fq(x) →+* kbar(x)` and `compatK`: the maps `Fq(x) → kbar(x) → F-bar` and `Fq(x) → F → F-bar` agree.
* `aeval_map_ratK`, `isIntegral_img`, `isSeparable_img`: images of elements of `F` are integral and separable
  over `kbar(x)`.
* `adjoin_bimg_eq_top`: the images of an `Fq(x)`-basis of `F` generate `F-bar` as a `kbar(x)`-algebra.
* instances `functionField_Fbar : FunctionField kbar Fbar` and `isSeparable_Fbar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent

section FF

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

instance isScalarTower_FqFFbar : IsScalarTower Fq F (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (IsScalarTower.algebraMap_apply Fq F Ω a)

/-- The ring map `Fq(x) → kbar(x)`. -/
noncomputable def ratK : RatFunc Fq →+* RatFunc (kbar Fq Ω) :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap Fq (kbar Fq Ω)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap Fq (kbar Fq Ω)).injective))

theorem ratK_div (p d : Fq[X]) :
    ratK Fq Ω (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (p.map (algebraMap Fq (kbar Fq Ω))) /
        algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (d.map (algebraMap Fq (kbar Fq Ω))) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (algebraMap Fq (kbar Fq Ω)).injective)) p d

theorem ratK_algebraMap (p : Fq[X]) :
    ratK Fq Ω (algebraMap Fq[X] (RatFunc Fq) p) =
      algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (p.map (algebraMap Fq (kbar Fq Ω))) := by
  have h := ratK_div Fq Ω p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem compatK_poly_hom :
    (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp (mapRingHom (algebraMap Fq (kbar Fq Ω))) =
      (algebraMap F (Fbar Fq F Ω)).comp (algebraMap Fq[X] F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) (C (algebraMap Fq (kbar Fq Ω) a)) =
        algebraMap Fq (Fbar Fq F Ω) a := by
      rw [IsScalarTower.algebraMap_apply Fq (kbar Fq Ω) (Fbar Fq F Ω)]
      exact (IsScalarTower.algebraMap_apply (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) _).symm
    have e2 : algebraMap Fq[X] F (C a) = algebraMap Fq F a :=
      (IsScalarTower.algebraMap_apply Fq Fq[X] F a).symm
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
    rw [e1, e2, ← IsScalarTower.algebraMap_apply Fq F (Fbar Fq F Ω)]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact (hx_Fbar Fq F Ω).symm

theorem compatK_hom :
    (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)).comp (ratK Fq Ω) =
      (algebraMap F (Fbar Fq F Ω)).comp (algebraMap (RatFunc Fq) F) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratK_algebraMap,
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F]
  exact RingHom.congr_fun (compatK_poly_hom Fq F Ω) p

theorem compatK (g : RatFunc Fq) :
    algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) (ratK Fq Ω g) =
      algebraMap F (Fbar Fq F Ω) (algebraMap (RatFunc Fq) F g) :=
  RingHom.congr_fun (compatK_hom Fq F Ω) g

theorem aeval_map_ratK (p : (RatFunc Fq)[X]) (f : F) :
    aeval (algebraMap F (Fbar Fq F Ω) f) (p.map (ratK Fq Ω)) =
      algebraMap F (Fbar Fq F Ω) (aeval f p) := by
  rw [aeval_def, eval₂_map, compatK_hom, aeval_def, hom_eval₂]

theorem isIntegral_img (f : F) :
    IsIntegral (RatFunc (kbar Fq Ω)) (algebraMap F (Fbar Fq F Ω) f) := by
  have hf : IsIntegral (RatFunc Fq) f := Algebra.IsIntegral.isIntegral f
  refine ⟨(minpoly (RatFunc Fq) f).map (ratK Fq Ω), (minpoly.monic hf).map _, ?_⟩
  rw [← aeval_def, aeval_map_ratK, minpoly.aeval, map_zero]

theorem isSeparable_img (f : F) :
    IsSeparable (RatFunc (kbar Fq Ω)) (algebraMap F (Fbar Fq F Ω) f) := by
  have hs : (minpoly (RatFunc Fq) f).Separable := Algebra.IsSeparable.isSeparable (RatFunc Fq) f
  refine (hs.map (f := ratK Fq Ω)).of_dvd (minpoly.dvd _ _ ?_)
  rw [aeval_map_ratK, minpoly.aeval, map_zero]

/-- The images in `F-bar` of the standard `Fq(x)`-basis of `F`. -/
noncomputable abbrev bimg : Set (Fbar Fq F Ω) :=
  Set.range (fun j => algebraMap F (Fbar Fq F Ω) (Module.finBasis (RatFunc Fq) F j))

theorem img_mem_adjoin (f : F) :
    algebraMap F (Fbar Fq F Ω) f ∈ Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) := by
  rw [← (Module.finBasis (RatFunc Fq) F).sum_repr f, map_sum]
  refine Subalgebra.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def, map_mul, ← compatK Fq F Ω]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin (Set.mem_range_self j))

theorem adjoin_bimg_eq_top : Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) = ⊤ := by
  have hsub : ∀ y, y ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω) → y ∈ Fbar Fq F Ω :=
    fun y hy => IntermediateField.algebra_adjoin_le_adjoin (F := F) (S := (kbar Fq Ω : Set Ω)) hy
  have hall : ∀ y (hy : y ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω)),
      (⟨y, hsub y hy⟩ : Fbar Fq F Ω) ∈ Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y hy => (⟨y, hsub y hy⟩ : Fbar Fq F Ω) ∈
      Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω)) (fun x hx => ?_) (fun f => ?_)
      (fun x y _ _ hx hy => Subalgebra.add_mem _ hx hy)
      (fun x y _ _ hx hy => Subalgebra.mul_mem _ hx hy) hy
    · have e : (⟨x, hsub x (Algebra.subset_adjoin hx)⟩ : Fbar Fq F Ω) =
          algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)
            (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (C ⟨x, hx⟩)) := by
        rw [← IsScalarTower.algebraMap_apply, algebraMap_polyK, aeval_C]
        rfl
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
    · exact img_mem_adjoin Fq F Ω f
  refine Algebra.eq_top_iff.2 fun z => ?_
  have hz : (z : Ω) ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω) := by
    have h := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := F)
      (S := (kbar Fq Ω : Set Ω))
      (fun x hx => ((mem_algebraicClosure_iff'.1 hx).tower_top (A := F)).isAlgebraic)
    rw [← h]
    exact z.2
  exact hall z hz

instance functionField_Fbar : FunctionField (kbar Fq Ω) (Fbar Fq F Ω) := by
  have hint : ∀ x ∈ bimg Fq F Ω, IsIntegral (RatFunc (kbar Fq Ω)) x := by
    rintro _ ⟨j, rfl⟩
    exact isIntegral_img Fq F Ω _
  have h := fg_adjoin_of_finite (s := bimg Fq F Ω) (Set.finite_range _) hint
  rw [adjoin_bimg_eq_top, Algebra.top_toSubmodule] at h
  exact ⟨h⟩

instance isSeparable_Fbar : Algebra.IsSeparable (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) := by
  refine (separableClosure.eq_top_iff _ _).1 (IntermediateField.toSubalgebra_injective ?_)
  rw [IntermediateField.top_toSubalgebra, eq_top_iff, ← adjoin_bimg_eq_top Fq F Ω]
  exact Algebra.adjoin_le (by
    rintro _ ⟨j, rfl⟩
    exact mem_separableClosure_iff.2 (isSeparable_img Fq F Ω _))

end FF

end RamanujanPetersson.JacFrob

end

-- ===== S4.Def_RP_JacFrob_Sig =====
section

/-!
# S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`

* `Lc_le_kbar`, `Fc_le_Fbar`, `exists_lev_of_mem_kbar`, `exists_lev_of_mem_Fbar`: `k-bar = ⋃ L_{lev j}` and
  `F-bar = ⋃ F_{lev j}`; `Kc j` (the level `F_{lev j}` as an `F`-subalgebra of `Ω`) is directed, and
  `Kc i ≤ Kc j → i ≤ j` (degrees).
* `sig : F-bar ≃ₐ[F] F-bar`, glued from the level Frobenii `frobF` (`Subalgebra.iSupLift`):
  `coe_sig_of_mem` (on `F_{lev j}` it is `frobF` of that level) and `sig_algebraMap_kbar` (`c ↦ c ^ q` on `k-bar`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent Places

section Lev

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

theorem Lc_le_kbar (n : ℕ) [NeZero n] : Lc Fq Ω n ≤ kbar Fq Ω := fun _ hx =>
  mem_algebraicClosure_iff'.2 (isSeparable_of_mem_Lc hx).isIntegral

theorem Fc_le_Fbar (n : ℕ) [NeZero n] : Fc Fq F Ω n ≤ Fbar Fq F Ω :=
  IntermediateField.adjoin_le_iff.2 fun _ hx => mem_Fbar_of_mem_kbar (Lc_le_kbar Fq Ω n hx)

variable {Fq Ω} in
theorem exists_lev_of_mem_kbar {x : Ω} (hx : x ∈ kbar Fq Ω) : ∃ j, x ∈ Lc Fq Ω (lev j) := by
  have hint : IsIntegral Fq x := mem_algebraicClosure_iff'.1 hx
  have : FiniteDimensional Fq (IntermediateField.adjoin Fq {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin Fq {x}) := Module.finite_of_finite Fq
  letI : Fintype (IntermediateField.adjoin Fq {x}) := Fintype.ofFinite _
  have hd : 0 < Module.finrank Fq (IntermediateField.adjoin Fq {x}) := Module.finrank_pos
  have h := congrArg Subtype.val (FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self Fq x⟩ : IntermediateField.adjoin Fq {x}))
  rw [SubmonoidClass.coe_pow, Module.card_eq_pow_finrank (K := Fq)] at h
  exact ⟨_, Lc_le (Nat.dvd_factorial hd (Nat.le_succ _)) (mem_Lc.2 h)⟩

theorem Fbar_toSubalgebra :
    (Fbar Fq F Ω).toSubalgebra = Algebra.adjoin F (kbar Fq Ω : Set Ω) :=
  IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun _ hx => ((mem_algebraicClosure_iff'.1 hx).tower_top (A := F)).isAlgebraic)

/-- The level `F_{lev j}` as an `F`-subalgebra of `Ω`. -/
noncomputable abbrev Kc (j : ℕ) : Subalgebra F Ω := (Fc Fq F Ω (lev j)).toSubalgebra

theorem lev_dvd_lev {i j : ℕ} (h : i ≤ j) : lev i ∣ lev j :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ h)

theorem dir_Kc : Directed (· ≤ ·) (Kc Fq F Ω) :=
  Monotone.directed_le fun _ _ h _ hx => Fc_le (lev_dvd_lev h) hx

theorem Fbar_le_iSup : (Fbar Fq F Ω).toSubalgebra ≤ ⨆ j, Kc Fq F Ω j := by
  rw [Fbar_toSubalgebra]
  refine Algebra.adjoin_le fun x hx => ?_
  obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar hx
  exact le_iSup (Kc Fq F Ω) j (mem_Fc_of_mem_Lc hj)

variable {Fq F Ω} in
theorem exists_lev_of_mem_Fbar {y : Ω} (hy : y ∈ Fbar Fq F Ω) : ∃ j, y ∈ Fc Fq F Ω (lev j) := by
  have h := Fbar_le_iSup Fq F Ω hy
  rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed (dir_Kc Fq F Ω), Set.mem_iUnion] at h
  exact h

end Lev

section Sig

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

include hk in
theorem le_of_Kc_le {i j : ℕ} (h : Kc Fq F Ω i ≤ Kc Fq F Ω j) : i ≤ j := by
  have hr : ∀ N [NeZero N], Module.finrank F (Fc Fq F Ω N) = N := fun N _ => by
    rw [finrank_Fc Fq F Ω hk N, finrank_Lc Fq Ω (NeZero.ne N)]
  have : FiniteDimensional F (Fc Fq F Ω (lev j)) :=
    Module.finite_of_finrank_pos (by rw [hr]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h2 := IntermediateField.finrank_le_of_le_right
    (show Fc Fq F Ω (lev i) ≤ Fc Fq F Ω (lev j) from fun _ hx => h hx)
  rw [hr, hr] at h2
  by_contra hlt
  exact absurd h2 (not_le.2 ((Nat.factorial_lt (Nat.succ_pos j)).2 (Nat.succ_lt_succ (not_le.1 hlt))))

/-- The level-`lev j` Frobenius as an `F`-algebra map `F_{lev j} → Ω`. -/
noncomputable def frobLev (j : ℕ) : Kc Fq F Ω j →ₐ[F] Ω :=
  (Fc Fq F Ω (lev j)).val.comp (frobF (isConstExt_Fc Fq F Ω hk (lev j))).toAlgHom

theorem frobLev_apply (j : ℕ) (y : Fc Fq F Ω (lev j)) :
    frobLev Fq F Ω hk j y = (frobF (isConstExt_Fc Fq F Ω hk (lev j)) y : Ω) := rfl

theorem frobLev_coe (j : ℕ) {c : Ω} (hc : c ∈ Lc Fq Ω (lev j)) :
    frobLev Fq F Ω hk j ⟨c, mem_Fc_of_mem_Lc hc⟩ = c ^ Fintype.card Fq := by
  show ((frobF (isConstExt_Fc Fq F Ω hk (lev j))
    (algebraMap (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) ⟨c, hc⟩) : Fc Fq F Ω (lev j)) : Ω) = _
  rw [frobF_algebraMap_L, coe_algebraMap_LF, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    SubmonoidClass.coe_pow]

theorem frobLev_compat (i j : ℕ) (h : Kc Fq F Ω i ≤ Kc Fq F Ω j) :
    frobLev Fq F Ω hk i = (frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h) := by
  have hij : lev i ∣ lev j := lev_dvd_lev (le_of_Kc_le Fq F Ω hk h)
  refine AlgHom.coe_ringHom_injective (ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk (lev i))
    (fun a => ?_) (fun l => ?_))
  · exact ((frobLev Fq F Ω hk i).commutes a).trans
      (((frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h)).commutes a).symm
  · have e1 : (frobLev Fq F Ω hk i : Kc Fq F Ω i →+* Ω)
        (algebraMap (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i)) l) = (l : Ω) ^ Fintype.card Fq :=
      frobLev_coe Fq F Ω hk i l.2
    have e2 : ((frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h) : Kc Fq F Ω i →+* Ω)
        (algebraMap (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i)) l) = (l : Ω) ^ Fintype.card Fq :=
      frobLev_coe Fq F Ω hk j (Lc_le hij l.2)
    exact e1.trans e2.symm

/-- The glued Frobenius `F-bar → Ω`. -/
noncomputable def sig0 : (Fbar Fq F Ω).toSubalgebra →ₐ[F] Ω :=
  Subalgebra.iSupLift (Kc Fq F Ω) (dir_Kc Fq F Ω) (frobLev Fq F Ω hk) (frobLev_compat Fq F Ω hk) _
    (Fbar_le_iSup Fq F Ω)

theorem sig0_of_mem (y : (Fbar Fq F Ω).toSubalgebra) {j : ℕ} (hy : (y : Ω) ∈ Kc Fq F Ω j) :
    sig0 Fq F Ω hk y = frobLev Fq F Ω hk j ⟨y, hy⟩ :=
  Subalgebra.iSupLift_of_mem (Kc Fq F Ω) y hy

theorem sig0_mem (y : (Fbar Fq F Ω).toSubalgebra) : sig0 Fq F Ω hk y ∈ (Fbar Fq F Ω).toSubalgebra := by
  obtain ⟨j, hj⟩ := exists_lev_of_mem_Fbar y.2
  rw [sig0_of_mem Fq F Ω hk y hj]
  exact Fc_le_Fbar Fq F Ω (lev j) (frobF (isConstExt_Fc Fq F Ω hk (lev j)) ⟨y, hj⟩).2

/-- `σ` as an `F`-algebra endomorphism of `F-bar`. -/
noncomputable def sig1 : Fbar Fq F Ω →ₐ[F] Fbar Fq F Ω :=
  (sig0 Fq F Ω hk).codRestrict (Fbar Fq F Ω).toSubalgebra (sig0_mem Fq F Ω hk)

theorem sig1_surjective : Function.Surjective (sig1 Fq F Ω hk) := by
  intro z
  obtain ⟨j, hj⟩ := exists_lev_of_mem_Fbar z.2
  let w := (frobF (isConstExt_Fc Fq F Ω hk (lev j))).symm ⟨z, hj⟩
  refine ⟨⟨w, Fc_le_Fbar Fq F Ω (lev j) w.2⟩, Subtype.ext ?_⟩
  show sig0 Fq F Ω hk ⟨w, Fc_le_Fbar Fq F Ω (lev j) w.2⟩ = z
  rw [sig0_of_mem Fq F Ω hk _ (j := j) w.2]
  show ((frobF (isConstExt_Fc Fq F Ω hk (lev j)) w : Fc Fq F Ω (lev j)) : Ω) = z
  rw [AlgEquiv.apply_symm_apply]

/-- **The arithmetic Frobenius** `σ` of `F-bar / F`: `frobF` on every level, `c ↦ c ^ q` on `k-bar`. -/
noncomputable def sig : Fbar Fq F Ω ≃ₐ[F] Fbar Fq F Ω :=
  AlgEquiv.ofBijective (sig1 Fq F Ω hk)
    ⟨(sig1 Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).injective, sig1_surjective Fq F Ω hk⟩

theorem coe_sig_of_mem (y : Fbar Fq F Ω) {j : ℕ} (hy : (y : Ω) ∈ Fc Fq F Ω (lev j)) :
    ((sig Fq F Ω hk y : Fbar Fq F Ω) : Ω) = (frobF (isConstExt_Fc Fq F Ω hk (lev j)) ⟨y, hy⟩ : Ω) :=
  sig0_of_mem Fq F Ω hk y hy

theorem sig_algebraMap_kbar (c : kbar Fq Ω) :
    sig Fq F Ω hk (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c ^ Fintype.card Fq := by
  obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar c.2
  apply Subtype.ext
  rw [coe_sig_of_mem Fq F Ω hk _ (j := j) (mem_Fc_of_mem_Lc hj), SubmonoidClass.coe_pow]
  exact frobLev_coe Fq F Ω hk j hj

end Sig

end RamanujanPetersson.JacFrob

end

-- ===== S4.Def_RP_JacFrob_Phi =====
section

/-!
# S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`

* `Phi : F-bar →ₐ[k-bar] F-bar`, `Phi z = σ⁻¹ (z ^ q) = (σ⁻¹ z) ^ q`; `Phi a = a ^ q` on `F`; `Phi x = x ^ q`;
* `Phi_comp_poly`: on `k-bar[X]` it is `expand q`; hence `isIntegral_Phi` and
* `PhiR : Rfin →ₐ[k-bar] Rfin` (the Frobenius of the affine curve `X⁰ = Spec Rfin`) and
  `PhiS g := symMap PhiR` on `S_g = SymRing k-bar Rfin g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent Places RamanujanPetersson.JacSym

section Phi

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

/-- **The relative Frobenius** `Φ = σ⁻¹ ∘ (·)^q`, a `k-bar`-algebra endomorphism of `F-bar`. -/
noncomputable def Phi : Fbar Fq F Ω →ₐ[kbar Fq Ω] Fbar Fq F Ω where
  toRingHom := ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω).comp
    (FiniteField.frobeniusAlgHom Fq (Fbar Fq F Ω) : Fbar Fq F Ω →+* Fbar Fq F Ω)
  commutes' c := by
    show (sig Fq F Ω hk).symm (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c ^ Fintype.card Fq) = _
    rw [← sig_algebraMap_kbar Fq F Ω hk, AlgEquiv.symm_apply_apply]

theorem Phi_apply (z : Fbar Fq F Ω) : Phi Fq F Ω hk z = (sig Fq F Ω hk).symm (z ^ Fintype.card Fq) := rfl

theorem Phi_apply' (z : Fbar Fq F Ω) : Phi Fq F Ω hk z = (sig Fq F Ω hk).symm z ^ Fintype.card Fq := by
  rw [Phi_apply, map_pow]

theorem Phi_algebraMap_F (a : F) :
    Phi Fq F Ω hk (algebraMap F (Fbar Fq F Ω) a) = algebraMap F (Fbar Fq F Ω) a ^ Fintype.card Fq := by
  rw [Phi_apply, ← map_pow, AlgEquiv.commutes]

theorem Phi_xbar : Phi Fq F Ω hk (xbar Fq F Ω) = xbar Fq F Ω ^ Fintype.card Fq :=
  Phi_algebraMap_F Fq F Ω hk (RR.xF Fq F)

theorem Phi_injective : Function.Injective (Phi Fq F Ω hk) :=
  (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).injective

theorem Phi_comp_poly :
    (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).comp (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)) =
      (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp
        (expand (kbar Fq Ω) (Fintype.card Fq) : (kbar Fq Ω)[X] →+* (kbar Fq Ω)[X]) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, algebraMap_polyK, expand_C, aeval_C,
      AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, algebraMap_polyK, expand_X, aeval_X,
      map_pow, Phi_xbar]

theorem isIntegral_Phi {z : Fbar Fq F Ω} (hz : IsIntegral (kbar Fq Ω)[X] z) :
    IsIntegral (kbar Fq Ω)[X] (Phi Fq F Ω hk z) :=
  IsIntegral.map_of_comp_eq
    (expand (kbar Fq Ω) (Fintype.card Fq) : (kbar Fq Ω)[X] →+* (kbar Fq Ω)[X])
    (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (Phi_comp_poly Fq F Ω hk).symm hz

/-- `Φ` on the finite coordinate ring `Rfin = k-bar[X]`-integral closure in `F-bar`. -/
noncomputable def PhiR : Rfin (kbar Fq Ω) (Fbar Fq F Ω) →ₐ[kbar Fq Ω] Rfin (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun r := ⟨Phi Fq F Ω hk r, isIntegral_Phi Fq F Ω hk r.2⟩
  map_one' := Subtype.ext (map_one (Phi Fq F Ω hk))
  map_mul' a b := Subtype.ext (map_mul (Phi Fq F Ω hk) (a : Fbar Fq F Ω) b)
  map_zero' := Subtype.ext (map_zero (Phi Fq F Ω hk))
  map_add' a b := Subtype.ext (map_add (Phi Fq F Ω hk) (a : Fbar Fq F Ω) b)
  commutes' c := Subtype.ext ((Phi Fq F Ω hk).commutes c)

theorem coe_PhiR (r : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :
    ((PhiR Fq F Ω hk r : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) : Fbar Fq F Ω) = Phi Fq F Ω hk r := rfl

theorem PhiR_injective : Function.Injective (PhiR Fq F Ω hk) := fun _ _ h =>
  Subtype.ext (Phi_injective Fq F Ω hk (congrArg Subtype.val h))

/-- `Φ` on `S_g = SymRing k-bar Rfin g` (coordinate ring of `Sym^g X⁰`). -/
noncomputable abbrev PhiS (g : ℕ) :
    SymRing (kbar Fq Ω) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) g →ₐ[kbar Fq Ω]
      SymRing (kbar Fq Ω) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) g :=
  symMap (PhiR Fq F Ω hk)

end Phi

end RamanujanPetersson.JacFrob

end


