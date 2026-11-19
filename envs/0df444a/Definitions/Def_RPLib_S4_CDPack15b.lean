-- Prove2me | Definitions.Def_RPLib_S4_CDPack15b
-- name    : RPLib_S4_CDPack15b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:07:06.763034+00:00
-- url     : https://prove2.me/theorems/7b86cd56-9c25-4ecd-9718-5624468cfb5c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 15b of 71
-- statement:
--   Part 15b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ExDef`: S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it
--   * `Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack15x
import Definitions.Def_RPLib_S4_CDPack02
import Definitions.Def_RPLib_S4_KummerBridge

/-!
# Curve-duality library package, part 15b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ExDef`: S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it
* `Def_RP_Cone_Exist`: S4-PD (4), E4X part 2: existence of global characters with prescribed residues
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ExDef =====
section

/-!
# S4-PD (4), E4X part 1: the divisibility hypothesis for boundary divisors, and Kummer roots from it

* `PicDivX A K R0 p N`: **`Pic⁰(X̄)` is `N`-divisible on boundary divisors** -- for every finite level `M ≤ K_U`
  whose boundary residue fields all have the same size and every boundary divisor `D` of `M` with `Σ D = 0`
  (degree `0`), after a constant extension `M·𝔽_{p^m}` some `a ≠ 0` has `N ∣ v_y(a)` at every finite place `y`
  and `D + div(a) ≡ 0 mod N` at the boundary. Explicit hypothesis of S4-PD item (4) (discharged downstream by
  S4-CoreB, like `CdOne.PicDivU`).
* `exists_root_picDivX`: from `PicDivX`, a unit `α ∈ K_U` with `α ^ N ∈ M ⊔ K(𝔽_{p^(e k)})` for every constant level
  `M ⊔ K(𝔽_{p^(e k)}) ⊇ L·𝔽_{p^m}`, whose boundary valuations are `-D mod N` (Kummer unramified criterion + valuations
  along constant extensions).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CdOne TameInertia IsDedekindDomain

noncomputable section

/-- **`Pic⁰(X̄)/N = 0` on boundary divisors**: at every finite level `M ≤ K_U` whose boundary residue fields all have
`r` elements, every boundary divisor `D` with `Σ D = 0` becomes, after a constant extension `M·𝔽_{p^m}`, congruent
mod `N` to `-div(a)` for some `a ≠ 0` whose finite valuations are all divisible by `N`. -/
def PicDivX (A K R0 : Type) [CommRing A] [Field K] [Algebra A K] [CommRing R0] [IsDedekindDomain R0]
    [Algebra R0 K] [IsFractionRing R0 K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) : Prop :=
  ∀ M : IntermediateField K (AlgebraicClosure K), FiniteDimensional K M → M ≤ maxUnram A K →
    ∀ [IsDedekindDomain (integralClosure R0 M)] [IsFractionRing (integralClosure R0 M) M] (r : ℕ),
    (∀ w : HeightOneSpectrum (integralClosure R0 M), Nat.card (integralClosure R0 M ⧸ w.asIdeal) = r) →
    ∀ D : HeightOneSpectrum (integralClosure R0 M) → ℤ, (Function.support D).Finite → ∑ᶠ w, D w = 0 →
    ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ constLevel K p m), a ≠ 0 ∧
      (∀ [IsDedekindDomain (integralClosure A ↥(M ⊔ constLevel K p m))]
        [IsFractionRing (integralClosure A ↥(M ⊔ constLevel K p m)) ↥(M ⊔ constLevel K p m)]
        (y : HeightOneSpectrum (integralClosure A ↥(M ⊔ constLevel K p m))),
        (N : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ constLevel K p m) a)) ∧
      ∀ [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p m))]
        [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p m)) ↥(M ⊔ constLevel K p m)]
        (w : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p m))),
        (N : ℤ) ∣ D (underI R0 (le_sup_left : M ≤ M ⊔ constLevel K p m) w) +
          WithZero.log (w.valuation ↥(M ⊔ constLevel K p m) a)

variable {A K : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Kummer roots from `PicDivX`**: a unit `α ∈ K_U` such that at every constant level `L₂ = M ⊔ K(𝔽_{p^(e k)})`
containing `L·𝔽_{p^m}`, `α ^ N = b ∈ L₂` with `v₂(b) ≡ -D(v) mod N` at the boundary place `v₂` of `L₂` over the place
`v` of `L` (both under one boundary prime `Q`). -/
theorem exists_root_picDivX [Ring.HasFiniteQuotients R0] {N : ℕ} [NeZero N] (hPic : PicDivX A K R0 p N)
    (hNA : IsUnit (N : A)) {e : ℕ} (he : 0 < e) {M L : IntermediateField K (AlgebraicClosure K)}
    (hM : M ∈ unramSet A K) (hMU : M ≤ maxUnram A K) (hL : L ∈ unramSet A K) (hLU : L ≤ maxUnram A K)
    (hML : M ≤ L) [hDL : IsDedekindDomain (integralClosure R0 L)] [hFL : IsFractionRing (integralClosure R0 L) L]
    {r : ℕ} (hr : ∀ w : HeightOneSpectrum (integralClosure R0 L), Nat.card (integralClosure R0 L ⧸ w.asIdeal) = r)
    (D : HeightOneSpectrum (integralClosure R0 L) → ℤ) (hD : (Function.support D).Finite)
    (hD0 : ∑ᶠ w, D w = 0) :
    ∃ m, 0 < m ∧ ∃ α : (maxUnram A K)ˣ, ∀ k, 0 < k → L ⊔ constLevel K p m ≤ M ⊔ constLevel K p (e * k) →
      ∀ (hL2U : M ⊔ constLevel K p (e * k) ≤ maxUnram A K),
      ∃ b : ↥(M ⊔ constLevel K p (e * k)), (α : maxUnram A K) ^ N = IntermediateField.inclusion hL2U b ∧
        ∀ [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
          [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
          (Q : Ideal (proChart A K R0)), IsBdryPrime A K R0 Q →
          ∀ v2 : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))),
            v2.asIdeal = Q.comap (inclU R0 hL2U) →
          ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
            (N : ℤ) ∣ D v + WithZero.log (v2.valuation ↥(M ⊔ constLevel K p (e * k)) b) := by
  have hFDL : FiniteDimensional K L := hL.1
  obtain ⟨m, hm, a, ha0, hafin, habd⟩ := hPic L hFDL hLU r hr D hD hD0
  refine ⟨m, hm, ?_⟩
  have hL1 : L ⊔ constLevel K p m ∈ unramSet A K := sup_mem_unramSet A K hL (constLevel_mem_unramSet A hm)
  have hL1U : L ⊔ constLevel K p m ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL1
  have : FiniteDimensional K ↥(L ⊔ constLevel K p m) := hL1.1
  have : IsGalois K ↥(L ⊔ constLevel K p m) := hL1.2.1
  have hDA1 : IsDedekindDomain (integralClosure A ↥(L ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(L ⊔ constLevel K p m))
  have hFA1 : IsFractionRing (integralClosure A ↥(L ⊔ constLevel K p m)) ↥(L ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  have hDR1 : IsDedekindDomain (integralClosure R0 ↥(L ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := R0) (K := K) (L := ↥(L ⊔ constLevel K p m))
  have hFR1 : IsFractionRing (integralClosure R0 ↥(L ⊔ constLevel K p m)) ↥(L ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K _
  -- the Kummer root is unramified over `U`
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ↥(L ⊔ constLevel K p m)) : AlgebraicClosure K)
    (Nat.pos_of_ne_zero (NeZero.ne N))
  have hγU : γ ∈ maxUnram A K := root_mem_maxUnram_of_dvd A hL1 hNA ha0 (fun y => hafin y) hγ
  have hγ0 : (⟨γ, hγU⟩ : maxUnram A K) ≠ 0 := by
    intro h0
    have h1 : γ = 0 := congrArg Subtype.val h0
    apply ha0
    have h2 : ((a : ↥(L ⊔ constLevel K p m)) : AlgebraicClosure K) = 0 := by
      rw [← hγ, h1, zero_pow (NeZero.ne N)]
    exact_mod_cast h2
  refine ⟨Units.mk0 _ hγ0, fun k hk hL12 hL2U => ?_⟩
  refine ⟨IntermediateField.inclusion hL12 a, by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Units.val_mk0, IntermediateField.coe_inclusion, IntermediateField.coe_inclusion]
    exact hγ, ?_⟩
  intro _ _ Q hQ v2 hv2 v hv
  have := hQ.1
  let v1 : HeightOneSpectrum (integralClosure R0 ↥(L ⊔ constLevel K p m)) :=
    ⟨Q.comap (inclU R0 hL1U), Ideal.IsPrime.comap _, comap_inclU_ne_bot hL1U hQ⟩
  have h1 := habd v1
  have hu : underI R0 (le_sup_left : L ≤ L ⊔ constLevel K p m) v1 = v := by
    apply HeightOneSpectrum.ext
    rw [hv]
    ext x
    show x ∈ Ideal.comap (incl R0 K (le_sup_left : L ≤ L ⊔ constLevel K p m)) (Ideal.comap (inclU R0 hL1U) Q) ↔
      x ∈ Ideal.comap (inclU R0 hLU) Q
    have hxe : inclU R0 hL1U (incl R0 K (le_sup_left : L ≤ L ⊔ constLevel K p m) x) = inclU R0 hLU x := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [inclU, AlgHom.coe_mapIntegralClosure, AlgHom.coe_restrictScalars', IntermediateField.coe_inclusion]
      exact incl_val R0 K _ x
    simp only [Ideal.mem_comap]
    rw [← hxe]
  have hCU : constLevel K p (e * k) ≤ maxUnram A K := le_sup_right.trans hL2U
  have hL2 : M ⊔ constLevel K p (e * k) ∈ unramSet A K :=
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have : FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := hL2.1
  have h2 := log_val_eq_of_inertia_fix hL12 hL1U hL2U v1 rfl v2 hv2
    (fun σ hσ hσ1 => inertia_fix_sup he hMU (Nat.mul_pos he hk) hCU hσ
      (fun y hy => hσ1 y ((hML.trans le_sup_left) hy))) a
  rw [h2, ← hu]
  exact h1

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_Exist =====
section

/-!
# S4-PD (4), E4X part 2: existence of global characters with prescribed residues

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U`, representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes and generators `τ t` of their inertia groups `J t`,
normalised at the constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k` (output of `exists_norm_tau_sum`).

* `bij_reps`: at a level with exact boundary residue degrees, the places under the representatives are all the
  boundary places, each once.
* `exists_kchar_of_sum_zero` (**existence**, converse of the global residue theorem): under `PicDivX`, for every
  `c : T → ℤ/N` with `Σ_t c t = 0` there is a locally constant hom `χ : Γ_H → ℤ/N` with `χ(τ t) = c t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a CdOne TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- At a level `L ⊇ F(𝔽_{q^m})` whose boundary residue fields have `q^m` elements, the places `v t` under the orbit
representatives `Q t` form a bijection onto the boundary places of `L`. -/
theorem bij_reps {L : IntermediateField F (AlgebraicClosure F)} (hLU : L ≤ maxUnram (Places.Rfin Fq F) F)
    [FiniteDimensional F L] [IsDedekindDomain (integralClosure (Places.Rinf Fq F) L)]
    {m : ℕ} (hm : 0 < m) (hC : constLevel F p (e * m) ≤ L)
    (hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L),
      Nat.card (integralClosure (Places.Rinf Fq F) L ⧸ w.asIdeal) = Fintype.card Fq ^ m)
    {T : Type} (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) L))
    (hv : ∀ t, (v t).asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU)) :
    Function.Bijective v := by
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
  refine ⟨fun t t' h => ?_, fun w => ?_⟩
  · apply eq_of_comap_eq_reps he hζc (fun Q hQ => good_inf hq Q hQ) hLU hk hC hres Qt hQt hdisj'
    exact (hv t).symm.trans ((congrArg HeightOneSpectrum.asIdeal h).trans (hv t'))
  · obtain ⟨t, ht⟩ := exists_rep_comap_eq hLU Qt hcover w.asIdeal (hwP := w.isPrime) w.ne_bot
    exact ⟨t, HeightOneSpectrum.ext ((hv t).trans ht)⟩

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Existence** (converse of the global residue theorem): under `PicDivX`, every `c : T → ℤ/N` with `Σ_t c t = 0`
is `t ↦ χ(τ t)` for a locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_kchar_of_sum_zero {N : ℕ} [NeZero N] (hNA : IsUnit (N : Places.Rfin Fq F))
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hMU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (J : T → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : ∀ t, J t ≤ Γ)
    (τ : ∀ t, J t) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hnorm : ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
      [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
      [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
        ↥(M ⊔ constLevel F p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
      v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
      ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
        (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α (τ t) =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N))
    (c : T → ZMod N) (hc : ∑ t, c t = 0) :
    ∃ χ : Γ → ZMod N, IsLocallyConstant χ ∧ (∀ σ σ', χ (σ * σ') = χ σ + χ σ') ∧
      ∀ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = c t := by
  classical
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨fun _ => 0, IsLocallyConstant.const 0, fun _ _ => (add_zero 0).symm, fun t => isEmptyElim t⟩
  -- the level `L = M ⊔ K(𝔽_{p^(e m)})`, `k₀ ∣ m`, with exact boundary residue degrees
  have hFDM : FiniteDimensional F M := hM.1
  have : IsGalois F M := hM.2.1
  obtain ⟨m0, hm0, hpow⟩ := exists_bdry_pow Fq M
  obtain ⟨m, hm_def⟩ : ∃ m, m = m0 * k₀ := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos hm0 hk₀
  have hdvd0 : k₀ ∣ m := ⟨m0, by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hCU : constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) M), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) M, y ^ (Fintype.card Fq ^ m) - y ∈ w := by
    intro w hw hw0 y
    rw [hm_def]
    exact hpow w hw hw0 _ y
  have hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))),
      Nat.card (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)) ⧸ w.asIdeal) =
        Fintype.card Fq ^ m :=
    fun w => card_bdry_sup hq he hζc hMU hm hres hCU w
  -- geometric elements fix the constant levels
  have hgC : ∀ {k : ℕ} (hk : 0 < k) (hkU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F),
      ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hkU).fixingSubgroup := by
    intro k hk hkU g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hkU _).1 hy) g
      (by rw [← hq]; exact hg)
  have hcoverL : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t := by
    intro Q hQ
    obtain ⟨t, g, hg, hgM, hQg⟩ := hcover Q hQ
    exact ⟨t, g, hg, mem_fix_sup hMU hCU hgM (hgC hm hCU g hg), hQg⟩
  have hdisjL : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' :=
    fun t t' g hg hgL h => hdisj t t' g hg (mem_fix_of_le hMU (le_sup_left.trans (le_fixF hLU hgL))) h
  -- the boundary places of `L` are the `v t`, each once
  let v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) := fun t =>
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hLU (hQt t)⟩
  have hbij : Function.Bijective v :=
    bij_reps hq he hζc hLU hm le_sup_right hdi Qt hQt hcoverL hdisjL v (fun t => rfl)
  let eqv := Equiv.ofBijective v hbij
  -- an integer lift `D'` of `c` with total `0`
  let c' : T → ℤ := fun t => ((c t).val : ℤ)
  have hcast : ∀ t, ((c' t : ℤ) : ZMod N) = c t := fun t => by
    simp only [c', Int.cast_natCast, ZMod.natCast_zmod_val]
  let s : ℤ := ∑ t, c' t
  have hs : (s : ZMod N) = 0 := by
    show ((∑ t, c' t : ℤ) : ZMod N) = 0
    rw [Int.cast_sum]
    simp only [hcast]
    exact hc
  let D' : T → ℤ := fun t => c' t - if t = t₀ then s else 0
  have hD'sum : ∑ t, D' t = 0 := by
    simp only [D', Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sub_self _
  have hD'c : ∀ t, ((D' t : ℤ) : ZMod N) = c t := by
    intro t
    simp only [D']
    rw [Int.cast_sub, hcast]
    split_ifs
    · rw [hs, sub_zero]
    · rw [Int.cast_zero, sub_zero]
  -- the boundary divisor `D = -D'` on `L`
  let D : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) → ℤ :=
    fun w => -D' (eqv.symm w)
  have hDv : ∀ t, D (v t) = -D' t := fun t => by
    show -D' (eqv.symm (eqv t)) = -D' t
    rw [Equiv.symm_apply_apply]
  have : Finite (HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))) :=
    Finite.of_equiv T eqv
  have hDfin : (Function.support D).Finite := Set.toFinite _
  have hDsum : ∑ᶠ w, D w = 0 := by
    rw [← finsum_comp_equiv eqv, finsum_eq_sum_of_fintype]
    have h : ∀ t, D (eqv t) = -D' t := hDv
    simp only [h, Finset.sum_neg_distrib, hD'sum, neg_zero]
  -- the Kummer root from `PicDivX`
  obtain ⟨m', hm', α, hα⟩ := exists_root_picDivX (hDL := hDedI) (hFL := hFracI) hPic hNA he hM hMU hLM hLU
    le_sup_left hdi D hDfin hDsum
  -- the level `L₂ = M ⊔ K(𝔽_{p^(e m m')})` contains `L·𝔽_{p^m'}` and `k₀ ∣ m m'`
  have hk : 0 < m * m' := Nat.mul_pos hm hm'
  have hdvd : k₀ ∣ m * m' := hdvd0.mul_right m'
  have hL12 : M ⊔ constLevel F p (e * m) ⊔ constLevel F p m' ≤ M ⊔ constLevel F p (e * (m * m')) := by
    refine sup_le (sup_le le_sup_left ((constLevel_le_of_dvd (Nat.mul_pos he hk) ?_).trans le_sup_right))
      ((constLevel_le_of_dvd (Nat.mul_pos he hk) ?_).trans le_sup_right)
    · exact Nat.mul_dvd_mul_left e (Dvd.intro m' rfl)
    · exact ⟨e * m, by ring⟩
  have hL2M : M ⊔ constLevel F p (e * (m * m')) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have hL2U : M ⊔ constLevel F p (e * (m * m')) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL2M
  have hC2U : constLevel F p (e * (m * m')) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hL2U
  have : FiniteDimensional F ↥(M ⊔ constLevel F p (e * (m * m'))) := hL2M.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * (m * m'))) := hL2M.2.1
  have hDedI2 : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m')))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F)
      (L := ↥(M ⊔ constLevel F p (e * (m * m'))))
  have hFracI2 : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m'))))
      ↥(M ⊔ constLevel F p (e * (m * m'))) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  obtain ⟨b, hαb, hval⟩ := hα (m * m') hk hL12 hL2U
  -- `α` is a Kummer radical for `Γ_H`
  have hζΓ : ∀ σ ∈ Γ, σ ζN = ζN := fun σ hσ => hζNg σ ((hΓ σ).1 hσ).1
  have hαr : α ∈ rad Γ N := by
    refine (mem_rad Γ N α).2 fun σ hσ => ?_
    obtain ⟨hσg, hσM⟩ := (hΓ σ).1 hσ
    have hσL := mem_fix_sup hMU hC2U hσM (hgC hk hC2U σ hσg)
    rw [hαb]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _
      ((IntermediateField.mem_restrict _ _).2 b.2)
  refine ⟨kchar hζN (Γ := Γ) α, isLocallyConstant_kchar hζN α, kchar_mul hζN hζΓ hαr, fun t => ?_⟩
  have h1 : kchar hζN (Γ := Γ) α ⟨τ t, hJΓ t (τ t).2⟩ = kchar hζN (Γ := J t) α (τ t) := rfl
  let v2 : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * (m * m')))) :=
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hL2U), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hL2U (hQt t)⟩
  rw [h1, @hnorm (m * m') hk hdvd hL2U hDedI2 hFracI2 t v2 rfl α b hαb]
  have h2 := @hval hDedI2 hFracI2 (Qt t) (hQt t) v2 rfl (v t) rfl
  rw [hDv t] at h2
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 h2
  push_cast at h3
  rw [← hD'c t]
  exact (neg_add_eq_zero.1 h3).symm

end

end Residue
end RamanujanPetersson

end


