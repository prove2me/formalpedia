-- Prove2me | Definitions.Def_RPLib_S4_CDPack15
-- name    : RPLib_S4_CDPack15
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:25:20.742755+00:00
-- url     : https://prove2.me/theorems/8da0cd05-69c0-4039-a16f-19b08e23e44e
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 15 of 71
-- statement:
--   Part 15 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResSum`: S4-PD (4), E4B part 4: the residue theorem at a level
--   * `Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack09b
import Definitions.Def_RPLib_S4_CDPack10
import Definitions.Def_RPLib_S4_CDPack14e
import Definitions.Def_RPLib_S4_KummerLev
import Definitions.Def_RPLib_S4_CDPack12
import Definitions.Def_RPLib_S4_CDPack08b

/-!
# Curve-duality library package, part 15 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResSum`: S4-PD (4), E4B part 4: the residue theorem at a level
* `Def_RP_Cone_ResMax`: S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResSum =====
section

/-!
# S4-PD (4), E4B part 4: the residue theorem at a level

* `comap_inclU_ne_bot`, `exists_bdry_comap_eq` (any chart): boundary primes of the pro-chart restrict to nonzero
  primes of `B_L`, and every nonzero prime of `B_L` is such a restriction (lying over).
* `eq_of_comap_eq_reps`, `exists_rep_comap_eq` (any chart): for representatives `Q t` of the
  `π₁^geo ∩ Gal(K_U/L)`-orbits of boundary primes, `t ↦ Q t ∩ B_L` is injective (when `L ⊇ K(𝔽_{p^k})` and
  `y ^ (p^k) ≡ y` at the boundary of `L`) and onto the nonzero primes of `B_L`.
* `dvd_sum_reps` (S3 chart, `R0 = O_∞`): if every boundary residue field of `L` has `q^m` elements and
  `L ⊇ F(𝔽_{q^m})`, then for `α ∈ K_U` with `α ^ N = b ∈ L`, `N ∣ Σ_t v_t(b)` over the representatives.
* `sum_reps_eq_zero`: the same for any `χ` with `χ(τ_t) = v_t(b) mod N` (normalised tame generators).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- A boundary prime of the pro-chart restricts to a nonzero prime of `B_L`. -/
theorem comap_inclU_ne_bot [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) : Q.comap (inclU R0 hLU) ≠ ⊥ := by
  have := hQ.1
  have hinj := algebraMap_proChart_injective (A := A) (K := K) (R0 := R0)
  have hPu : Q.under R0 ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPu
  intro h
  have h1 : algebraMap R0 (integralClosure R0 L) r ∈ Q.comap (inclU R0 hLU) := by
    rw [Ideal.mem_comap, AlgHom.commutes]; exact hrP
  rw [h, Ideal.mem_bot] at h1
  have h2 := congrArg (inclU R0 hLU) h1
  rw [AlgHom.commutes, map_zero] at h2
  exact hr0 (hinj (h2.trans (map_zero _).symm))

/-- Lying over: every nonzero prime of `B_L` is the trace of a boundary prime of the pro-chart. -/
theorem exists_bdry_comap_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    (w : Ideal (integralClosure R0 L)) [hwP : w.IsPrime] (hw : w ≠ ⊥) :
    ∃ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q ∧ Q.comap (inclU R0 hLU) = w := by
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (R0 := R0) (S := proChart A K R0)
    (inclU R0 hLU) (inclU_injective _) w
  refine ⟨P, ⟨hP, ?_⟩, hPw⟩
  rintro rfl
  apply hw
  rw [← hPw]
  exact Ideal.comap_bot_of_injective _ (inclU_injective _)

/-- Onto: every nonzero prime of `B_L` is the trace of one of the orbit representatives. -/
theorem exists_rep_comap_eq {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) {q : ℕ}
    {T : Type} (Qt : T → Ideal (proChart A K R0))
    (hcover : ∀ Q, IsBdryPrime A K R0 Q → ∃ t, ∃ g ∈ pi1geo A K q,
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (w : Ideal (integralClosure R0 L)) [hwP : w.IsPrime] (hw : w ≠ ⊥) :
    ∃ t, (Qt t).comap (inclU R0 hLU) = w := by
  obtain ⟨Q, hQ, hQw⟩ := exists_bdry_comap_eq hLU w hw
  obtain ⟨t, g, -, hgL, rfl⟩ := hcover Q hQ
  exact ⟨t, by rw [← hQw, comap_smul_of_fix hLU hgL]⟩

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
/-- One-to-one: two orbit representatives with the same trace on `B_L` coincide. -/
theorem eq_of_comap_eq_reps [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K] (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
      Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [FiniteDimensional K L]
    {k : ℕ} (hk : 0 < k) (hC : constLevel K p k ≤ L)
    (hres : ∀ w : Ideal (integralClosure R0 L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure R0 L, y ^ (p ^ k) - y ∈ w)
    {T : Type} (Qt : T → Ideal (proChart A K R0)) (hQt : ∀ t, IsBdryPrime A K R0 (Qt t))
    (hdisj : ∀ t t', ∀ g ∈ pi1geo A K (p ^ e), g ∈ (IntermediateField.restrict hLU).fixingSubgroup →
      Qt t' = g • Qt t → t = t')
    {t t' : T} (h : (Qt t).comap (inclU R0 hLU) = (Qt t').comap (inclU R0 hLU)) : t = t' := by
  have := (hQt t).1
  have := (hQt t').1
  obtain ⟨hfin, hcard⟩ := hgood _ (hQt t)
  obtain ⟨γ, hγ, hγL, hγQ⟩ := exists_geo_fix_smul he hζ hLU hk hC hcard
    (hres _ (Ideal.comap_isPrime _ _) (comap_inclU_ne_bot hLU (hQt t))) h
  exact hdisj t t' γ hγ hγL hγQ

end Chart

section Level

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Residue theorem at a level** (S3 chart): if `L ⊇ F(𝔽_{q^m})` is unramified over `U` and every boundary residue
field of `L` has `q^m` elements, then for representatives `Q t` of the `π₁^geo ∩ Gal(K_U/L)`-orbits of boundary
primes (places `v t` of `L` under them) and `α ∈ K_U` with `α ^ N = b ∈ L`, `N ∣ Σ_t v_t(b)`. -/
theorem dvd_sum_reps {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    (hL : L ∈ unramSet (Places.Rfin Fq F) F) [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [IsDedekindDomain (integralClosure (Places.Rfin Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rfin Fq F) L) L]
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) L) L]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU))
    {N : ℕ} {α : AlgebraicClosure F} (hαU : α ∈ maxUnram (Places.Rfin Fq F) F) {b : L} (hb : b ≠ 0)
    (hα : α ^ N = (b : AlgebraicClosure F)) :
    (N : ℤ) ∣ ∑ t, WithZero.log ((v t).valuation L b) := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) L), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) L, y ^ (p ^ (e * m)) - y ∈ w := by
    intro w hw hw0 y
    obtain ⟨w', rfl⟩ : ∃ w' : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L), w'.asIdeal = w :=
      ⟨⟨w, hw, hw0⟩, rfl⟩
    have h1 := hdi w'
    have : w'.asIdeal.IsMaximal := w'.isMaximal
    have : Finite (integralClosure (Places.Rinf Fq F) L ⧸ w'.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact pow_ne_zero _ Fintype.card_ne_zero)
    have h2 := pow_card_pow_sub_mem w'.asIdeal 1 y
    rw [h1, pow_one, hq, ← pow_mul] at h2
    exact h2
  have hk : 0 < e * m := Nat.mul_pos he hm
  have hdisj' : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' := by
    rw [← hq]; exact hdisj
  have hinj : Function.Injective v := by
    intro t t' h
    apply eq_of_comap_eq_reps he hζc (fun Q hQ => good_inf hq Q hQ) hLU hk hC hres Qt hQt hdisj'
    exact (hv t).symm.trans ((congrArg HeightOneSpectrum.asIdeal h).trans (hv t'))
  have hsurj : Function.Surjective v := by
    intro w
    obtain ⟨t, ht⟩ := exists_rep_comap_eq hLU Qt hcover w.asIdeal (hwP := w.isPrime) w.ne_bot
    exact ⟨t, HeightOneSpectrum.ext ((hv t).trans ht)⟩
  have hsum : ∑ t, WithZero.log ((v t).valuation L b) =
      ∑ᶠ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L), WithZero.log (w.valuation L b) := by
    rw [← finsum_eq_sum_of_fintype]
    exact finsum_comp_equiv (f := fun w => WithZero.log (w.valuation L b)) (Equiv.ofBijective v ⟨hinj, hsurj⟩)
  rw [hsum]
  obtain ⟨ζ, hζ⟩ := exists_prim_sup hq he hζc hm hC
  have hfin : ∀ y : HeightOneSpectrum (integralClosure (Places.Rfin Fq F) L),
      (N : ℤ) ∣ WithZero.log (y.valuation L b) := by
    intro y
    refine dvd_of_mem_maxUnram (Places.Rfin Fq F) hL (perfect_Rfin Fq F) (fun x => ?_) hαU hα y
    rw [RingHom.mem_range]
    refine ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩
    rintro ⟨z, rfl⟩
    exact z.2
  exact dvd_sum_bdry Fq L hm hb hfin
    (fun y => card_fin_level L hm hζ y) hdi

include hq he hζc in
/-- **Residue theorem for normalised tame generators**: under the hypotheses of `dvd_sum_reps`, any `χ` with
`χ(τ_t) = v_t(b) mod N` at every representative satisfies `Σ_t χ(τ_t) = 0`. -/
theorem sum_reps_eq_zero {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    (hL : L ∈ unramSet (Places.Rfin Fq F) F) [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [IsDedekindDomain (integralClosure (Places.Rfin Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rfin Fq F) L) L]
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) L) L]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU))
    {N : ℕ} {α : AlgebraicClosure F} (hαU : α ∈ maxUnram (Places.Rfin Fq F) F) {b : L} (hb : b ≠ 0)
    (hα : α ^ N = (b : AlgebraicClosure F)) (c : T → ZMod N)
    (hc : ∀ t, c t = ((WithZero.log ((v t).valuation L b) : ℤ) : ZMod N)) :
    ∑ t, c t = 0 := by
  have h := dvd_sum_reps hq he hζc hLU hL hm hC hdi Qt hQt hcover hdisj v hv hαU hb hα
  simp_rw [hc]
  rw [← Int.cast_sum]
  exact (CharP.intCast_eq_zero_iff (ZMod N) N _).2 h

end Level

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResMax =====
section

/-!
# S4-PD (4), E4B part 5b: one normalised tame generator for all constant levels

* `exists_stable`: finitely many families of subsets of `ℤ/N`, monotone along divisibility, are all constant on the
  multiples of one index `k₀`.
* `radVal` (valuation classes of the radicands of a level at `Q ∩ B_L`), `radVal_mono` (they grow along extensions in
  which inertia fixing the smaller level fixes the larger one).
* `exists_stable_tau`: for boundary primes `Q t` (`t` in a finite type) there are `k₀ > 0` and generators `τ t`
  normalised at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k` (from one normalisation per level).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial

noncomputable section

/-- Monotone families of subsets of `ℤ/N` stabilise simultaneously along divisibility. -/
theorem exists_stable {T : Type} [Fintype T] {N : ℕ} [NeZero N] (S : T → ℕ → Set (ZMod N))
    (hmono : ∀ t k k', 0 < k → 0 < k' → k ∣ k' → S t k ⊆ S t k') :
    ∃ k₀, 0 < k₀ ∧ ∀ t k, 0 < k → k₀ ∣ k → S t k ⊆ S t k₀ := by
  classical
  let g : ℕ → ℕ := fun k => ∑ t, (S t k).ncard
  have hbdd : BddAbove (g '' {k | 0 < k}) := by
    refine ⟨Fintype.card T * N, ?_⟩
    rintro _ ⟨k, -, rfl⟩
    calc g k = ∑ t, (S t k).ncard := rfl
      _ ≤ ∑ _t : T, N := Finset.sum_le_sum fun t _ => by
          calc (S t k).ncard ≤ (Set.univ : Set (ZMod N)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
            _ = N := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
      _ = Fintype.card T * N := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hne : (g '' {k | 0 < k}).Nonempty := ⟨g 1, 1, Nat.one_pos, rfl⟩
  obtain ⟨k₀, hk₀, hg₀⟩ := Nat.sSup_mem hne hbdd
  refine ⟨k₀, hk₀, fun t k hk hdvd => ?_⟩
  have hsub : ∀ t, S t k₀ ⊆ S t k := fun t => hmono t k₀ k hk₀ hk hdvd
  have hle : ∀ t ∈ (Finset.univ : Finset T), (S t k₀).ncard ≤ (S t k).ncard :=
    fun t _ => Set.ncard_le_ncard (hsub t)
  have hgk : g k ≤ g k₀ := by
    rw [hg₀]
    exact le_csSup hbdd ⟨k, hk, rfl⟩
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (le_antisymm (Finset.sum_le_sum hle) hgk)
  exact (Set.eq_of_subset_of_ncard_le (hsub t) (heq t (Finset.mem_univ t)).ge).ge

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- The place `Q ∩ B_L` of a level under a boundary prime `Q`. -/
def bdryPlace {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] : HeightOneSpectrum (integralClosure R0 L) :=
  ⟨Q.comap (inclU R0 hLU), haveI := hQ.1; Ideal.IsPrime.comap _, comap_inclU_ne_bot hLU hQ⟩

/-- Valuation classes mod `N`, at `Q ∩ B_L`, of the radicands `α ^ N = b ∈ L` (`α ∈ K_U`). -/
def radVal (Q : Ideal (proChart A K R0)) {L : IntermediateField K (AlgebraicClosure K)}
    (hLU : L ≤ maxUnram A K) [IsDedekindDomain (integralClosure R0 L)]
    [IsFractionRing (integralClosure R0 L) L] (N : ℕ) : Set (ZMod N) :=
  {c | ∃ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b ∧
    ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ((WithZero.log (v.valuation L b) : ℤ) : ZMod N) = c}

set_option synthInstance.maxHeartbeats 400000 in
theorem radVal_mono [Ring.HasFiniteQuotients R0] {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    {L L' : IntermediateField K (AlgebraicClosure K)} (hLL : L ≤ L') (hLU : L ≤ maxUnram A K)
    (hL'U : L' ≤ maxUnram A K) [FiniteDimensional K L']
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    [IsDedekindDomain (integralClosure R0 L')] [IsFractionRing (integralClosure R0 L') L']
    (hfix : ∀ σ ∈ Q.inertia (Pi1 A K), (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ L → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ L' → σ x = x) (N : ℕ) :
    radVal Q hLU N ⊆ radVal Q hL'U N := by
  have := hQ.1
  rintro c ⟨α, b, hα, hc⟩
  refine ⟨α, IntermediateField.inclusion hLL b, hα, fun v' hv' => ?_⟩
  rw [log_val_eq_of_inertia_fix hLL hLU hL'U (bdryPlace hQ hLU) rfl v' hv' hfix b]
  exact hc _ rfl

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- Constant levels grow with divisibility. -/
theorem constLevel_le_of_dvd {k k' : ℕ} (hk' : 0 < k') (h : k ∣ k') : constLevel K p k ≤ constLevel K p k' := by
  refine IntermediateField.adjoin_le_iff.2 fun y hy => ?_
  have hy' : y ^ p ^ k = y := by
    rw [mem_rootSet] at hy
    simpa [sub_eq_zero] using hy.2
  obtain ⟨j, rfl⟩ := h
  exact mem_constLevel hk' (pow_pow_mul_eq hy' j)

omit [IsDedekindDomain R0] [IsFractionRing R0 K] in
/-- Inertia fixing `M` fixes `M ⊔ K(𝔽_{p^k})`. -/
theorem inertia_fix_sup {e : ℕ} (he : 0 < e) {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    {M : IntermediateField K (AlgebraicClosure K)} (hMU : M ≤ maxUnram A K) {k : ℕ} (hk : 0 < k)
    (hCU : constLevel K p k ≤ maxUnram A K) {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    (hσM : ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y) :
    ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p k → σ y = y := by
  have hgeo := Kummer.inertia_le_pi1geo he rfl hσ
  have h1 : σ ∈ (IntermediateField.restrict hMU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact hσM y ((IntermediateField.mem_restrict hMU _).1 hy)
  have h2 : σ ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he hk ((IntermediateField.mem_restrict hCU _).1 hy) σ hgeo
  have h3 := mem_fix_sup hMU hCU h1 h2
  intro y hy
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h3 y ((IntermediateField.mem_restrict _ _).2 hy)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **One normalised generator per boundary prime for all constant levels** `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`. -/
theorem exists_stable_tau [Ring.HasFiniteQuotients R0] {e : ℕ} (he : 0 < e)
    {N : ℕ} [NeZero N] (hN : IsUnit (N : R0)) {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    {T : Type} [Fintype T] (Q : T → Ideal (proChart A K R0)) (hQ : ∀ t, IsBdryPrime A K R0 (Q t))
    (J : T → Subgroup (Pi1 A K))
    (hJ : ∀ t, ∀ σ ∈ J t, σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (P : ∀ t, J t → Prop)
    (htau : ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∃ τ : J t, P t τ ∧ ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N)) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t, (∀ t, P t (τ t)) ∧
      ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α (τ t) =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N) := by
  classical
  have hMU : M ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hM
  have hLk : ∀ k, 0 < k → M ⊔ constLevel K p (e * k) ∈ unramSet A K := fun k hk =>
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have hLkU : ∀ k, 0 < k → M ⊔ constLevel K p (e * k) ≤ maxUnram A K := fun k hk => by
    rw [maxUnram_eq_sSup]
    exact le_sSup (hLk k hk)
  have hfixk : ∀ k, 0 < k → ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K),
      (∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y) →
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ y = y := by
    intro k hk t σ hσ hσM
    have := (hQ t).1
    exact inertia_fix_sup he hMU (Nat.mul_pos he hk) (le_sup_right.trans (hLkU k hk)) hσ hσM
  have hFD : ∀ k, 0 < k → FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := fun k hk => (hLk k hk).1
  have hDed : ∀ k, 0 < k → IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) :=
    fun k hk => by
      have := hFD k hk
      have : IsGalois K ↥(M ⊔ constLevel K p (e * k)) := (hLk k hk).2.1
      exact integralClosure.isDedekindDomain (A := R0) (K := K) (L := ↥(M ⊔ constLevel K p (e * k)))
  have hFrac : ∀ k, 0 < k → IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))
      ↥(M ⊔ constLevel K p (e * k)) := fun k hk => by
    have := hFD k hk
    exact integralClosure.isFractionRing_of_finite_extension (A := R0) K _
  have hLL : ∀ k k', 0 < k → 0 < k' → k ∣ k' →
      M ⊔ constLevel K p (e * k) ≤ M ⊔ constLevel K p (e * k') := fun k k' hk hk' hdvd =>
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hk') (Nat.mul_dvd_mul_left e hdvd)) M
  let S : T → ℕ → Set (ZMod N) := fun t k => if hk : 0 < k then
    (haveI := hDed k hk; haveI := hFrac k hk; radVal (Q t) (hLkU k hk) N) else ∅
  have hS_eq : ∀ t k (hk : 0 < k), S t k =
      (haveI := hDed k hk; haveI := hFrac k hk; radVal (Q t) (hLkU k hk) N) := fun t k hk => dif_pos hk
  have hmono : ∀ t k k', 0 < k → 0 < k' → k ∣ k' → S t k ⊆ S t k' := by
    intro t k k' hk hk' hdvd
    rw [hS_eq t k hk, hS_eq t k' hk']
    have := hFD k' hk'
    have := hDed k hk
    have := hFrac k hk
    have := hDed k' hk'
    have := hFrac k' hk'
    exact radVal_mono (hQ t) (hLL k k' hk hk' hdvd) (hLkU k hk) (hLkU k' hk')
      (fun σ hσ h => hfixk k' hk' t σ hσ fun y hy => h y (le_sup_left (a := M) hy)) N
  obtain ⟨k₀, hk₀, hstab⟩ := exists_stable S hmono
  have := hFD k₀ hk₀
  have := hDed k₀ hk₀
  have := hFrac k₀ hk₀
  choose τ hP hnorm using fun t => htau k₀ hk₀ (hLkU k₀ hk₀) t (bdryPlace (hQ t) (hLkU k₀ hk₀)) rfl
  refine ⟨k₀, hk₀, τ, hP, ?_⟩
  intro k hk hdvd hLU _ _ t v hv α b hα
  have := hFD k hk
  have := (hQ t).1
  have hJle : J t ≤ (Q t).inertia (Pi1 A K) := fun σ hσ => (hJ t σ hσ).1
  have hfix' : ∀ σ ∈ (Q t).inertia (Pi1 A K),
      (∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k₀) → σ x = x) →
      ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ x = x :=
    fun σ hσ h => hfixk k hk t σ hσ fun y hy => h y (le_sup_left (a := M) hy)
  have hval := log_val_eq_of_inertia_fix (hLL k₀ k hk₀ hk hdvd) (hLkU k₀ hk₀) hLU
    (bdryPlace (hQ t) (hLkU k₀ hk₀)) rfl v hv hfix'
  refine kchar_norm_of_le hN hζN hJle (hLL k₀ k hk₀ hk hdvd) (hLkU k₀ hk₀) hLU
    (bdryPlace (hQ t) (hLkU k₀ hk₀)) v hv
    (fun σ hσ => hfixk k hk t σ (hJ t σ hσ).1 (hJ t σ hσ).2) hval ?_ (hnorm t) α b hα
  intro α' b' hα'
  have hmem : ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b') : ℤ) : ZMod N) ∈ S t k := by
    rw [hS_eq t k hk]
    exact ⟨α', b', hα', fun v' hv' => by rw [HeightOneSpectrum.ext (hv'.trans hv.symm)]⟩
  have hmem0 := hstab t k hk hdvd hmem
  rw [hS_eq t k₀ hk₀] at hmem0
  obtain ⟨β, c, hβ, hc⟩ := hmem0
  exact ⟨β, c, hβ, hc _ rfl⟩

end Chart

end

end Residue
end RamanujanPetersson

end


