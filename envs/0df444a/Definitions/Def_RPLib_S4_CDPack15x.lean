-- Prove2me | Definitions.Def_RPLib_S4_CDPack15x
-- name    : RPLib_S4_CDPack15x
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:41:34.647949+00:00
-- url     : https://prove2.me/theorems/9be01573-c966-43e1-8d4e-afd660f32f31
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 15x of 71
-- statement:
--   Part 15x of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack15

/-!
# Curve-duality library package, part 15x of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResGlob`: S4-PD (4), E4B part 5c: the global residue theorem
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResGlob =====
section

/-!
# S4-PD (4), E4B part 5c: the global residue theorem

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), a finite level `M ≤ K_U` and representatives `Q t` of the
`Γ_H := π₁^geo ∩ Gal(K_U/M)`-orbits of boundary primes; `J t` is the inertia of `Q t` fixing `M`.

* `exists_tau_sum_eq_zero`: from one normalised generator per constant level (`htau`) there are `k₀ > 0` and
  generators `τ t ∈ J t`, normalised at every level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k`, such that
  `Σ_t χ(τ t) = 0` for EVERY locally constant additive `χ : Γ_H → ℤ/N` (global residue theorem).
* `htau_norm` (any chart): the level-wise hypothesis `htau` from `exists_norm_tau`.
* `exists_norm_tau_sum`: the same with the tame generators of `exists_norm_tau` and their characters `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

section Chart

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- A normalised tame generator `τ` of `J ≤ I(Q)` with its character `θ` (the shape of `exists_norm_tau`). -/
abbrev TauProp (Q : Ideal (proChart A K R0)) (J : Subgroup (Pi1 A K)) (N : ℕ) (τ : J) : Prop :=
  ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
    (∀ g ∈ Q.inertia (Pi1 A K), ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J),
      θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
    (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
      ∀ σ, χ σ = χ τ * θ σ)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The level-wise normalisation hypothesis `htau` of `exists_stable_tau`, from `exists_norm_tau` at every constant
level `M ⊔ K(𝔽_{p^(e k)})` (inertia fixing `M` fixes these levels). -/
theorem htau_norm [Ring.HasFiniteQuotients R0] {e : ℕ} (he : 0 < e) {N : ℕ} [NeZero N]
    {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N) (hζNg : ∀ σ ∈ pi1geo A K (p ^ e), σ ζN = ζN)
    {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K) (hMU : M ≤ maxUnram A K)
    {T : Type} (Q : T → Ideal (proChart A K R0)) (hQ : ∀ t, IsBdryPrime A K R0 (Q t))
    (J : T → Subgroup (Pi1 A K))
    (hJ : ∀ t σ, σ ∈ J t ↔ σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M → σ y = y)
    (d : T → ℕ) (hd0 : ∀ t, 0 < d t)
    (hNA : ∀ t, IsUnit ((N * d t : ℕ) : A)) (hNR : ∀ t, IsUnit ((N * d t : ℕ) : R0))
    (ζ : T → maxUnram A K) (hζ : ∀ t, IsPrimitiveRoot (ζ t) (N * d t))
    (hζI : ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K), σ (ζ t) = ζ t)
    (x : T → HeightOneSpectrum R0) (hx : ∀ t, (x t).asIdeal = (Q t).comap (algebraMap R0 (proChart A K R0)))
    (a : T → A) (ha : ∀ t, 1 < (x t).valuation K (algebraMap A K (a t)))
    (kk : T → ℕ) (hd : ∀ t, ∀ σ ∈ (Q t).inertia (Pi1 A K), σ ^ (p ^ kk t * d t) ∈ J t) :
    ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel K p (e * k) ≤ maxUnram A K)
      [IsDedekindDomain (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))]
      [IsFractionRing (integralClosure R0 ↥(M ⊔ constLevel K p (e * k))) ↥(M ⊔ constLevel K p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure R0 ↥(M ⊔ constLevel K p (e * k)))),
      v.asIdeal = (Q t).comap (inclU R0 hLU) →
      ∃ τ : J t, TauProp (Q t) (J t) N τ ∧
      ∀ (α : (maxUnram A K)ˣ) (b : ↥(M ⊔ constLevel K p (e * k))),
        (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel K p (e * k)) b) : ℤ) : ZMod N) := by
  intro k hk hLU _ _ t v hv
  have : NeZero (d t) := ⟨(hd0 t).ne'⟩
  have hLk : M ⊔ constLevel K p (e * k) ∈ unramSet A K :=
    sup_mem_unramSet A K hM (constLevel_mem_unramSet A (Nat.mul_pos he hk))
  have : FiniteDimensional K ↥(M ⊔ constLevel K p (e * k)) := hLk.1
  have := (hQ t).1
  have hJk : ∀ σ, σ ∈ J t ↔ σ ∈ (Q t).inertia (Pi1 A K) ∧
      ∀ y : maxUnram A K, (y : AlgebraicClosure K) ∈ M ⊔ constLevel K p (e * k) → σ y = y := by
    intro σ
    refine ⟨fun hσ => ⟨((hJ t σ).1 hσ).1, inertia_fix_sup he hMU (Nat.mul_pos he hk)
      (le_sup_right.trans hLU) ((hJ t σ).1 hσ).1 ((hJ t σ).1 hσ).2⟩,
      fun h => (hJ t σ).2 ⟨h.1, fun y hy => h.2 y (le_sup_left (a := M) hy)⟩⟩
  have hζNJ : ∀ σ ∈ J t, σ ζN = ζN := fun σ hσ =>
    hζNg σ (Kummer.inertia_le_pi1geo he rfl ((hJ t σ).1 hσ).1)
  obtain ⟨τ, θ, h1, h2, h3, h4, h5, h6⟩ := exists_norm_tau (hQ t) (hNA t) (hNR t) (hζ t) (hζI t) (x t)
    (hx t) (ha t) hLU v hv hJk (kk t) (hd t) hζN hζNJ
  exact ⟨τ, ⟨θ, h1, h2, h3, h4, h5⟩, h6⟩

end Chart

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Places.Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Global residue theorem** (S3 chart): generators `τ t` of the inertia groups `J t`, normalised at all constant
levels `M ⊔ K(𝔽_{p^(e k)})` (`k₀ ∣ k`), with `Σ_t χ(τ t) = 0` for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_tau_sum_eq_zero {N : ℕ} [NeZero N] (hN : IsUnit (N : Places.Rinf Fq F))
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
    (hJ : ∀ t, ∀ σ ∈ J t, σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F) ∧
      ∀ y : maxUnram (Places.Rfin Fq F) F, (y : AlgebraicClosure F) ∈ M → σ y = y)
    (P : ∀ t, J t → Prop)
    (htau : ∀ k, 0 < k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
      [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
      [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
        ↥(M ⊔ constLevel F p (e * k))]
      (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
      v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
      ∃ τ : J t, P t τ ∧ ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
        (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J t) α τ =
          ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t, (∀ t, P t (τ t)) ∧
      (∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
        [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
        [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
          ↥(M ⊔ constLevel F p (e * k))]
        (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
        v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
        ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
          (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
          kchar hζN (Γ := J t) α (τ t) =
            ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  obtain ⟨k₀, hk₀, τ, hP, hnorm⟩ := exists_stable_tau he hN hζN hM Qt hQt J hJ P htau
  refine ⟨k₀, hk₀, τ, hP, hnorm, fun χ hχc hχ => ?_⟩
  -- the character is Kummer, with radicand in a constant level
  have hζΓ : ∀ σ ∈ Γ, σ ζN = ζN := fun σ hσ => hζNg σ ((hΓ σ).1 hσ).1
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  -- one level `L = M ⊔ K(𝔽_{p^(e m)})` with `k₀ ∣ m`, `k1 ∣ m` and exact boundary residue degrees
  have hFDM : FiniteDimensional F M := hM.1
  have : IsGalois F M := hM.2.1
  obtain ⟨m0, hm0, hpow⟩ := exists_bdry_pow Fq M
  obtain ⟨m, hm_def⟩ : ∃ m, m = m0 * (k₀ * k1) := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos hm0 (Nat.mul_pos hk₀ hk1)
  have hdvd0 : k₀ ∣ m := ⟨m0 * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨m0 * k₀, by rw [hm_def]; ring⟩
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
  have hDedF : IsDedekindDomain (integralClosure (Places.Rfin Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rfin Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracF : IsFractionRing (integralClosure (Places.Rfin Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rfin Fq F) F _
  have hres : ∀ w : Ideal (integralClosure (Places.Rinf Fq F) M), w.IsPrime → w ≠ ⊥ →
      ∀ y : integralClosure (Places.Rinf Fq F) M, y ^ (Fintype.card Fq ^ m) - y ∈ w := by
    intro w hw hw0 y
    rw [hm_def]
    exact hpow w hw hw0 _ y
  have hdi : ∀ w : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))),
      Nat.card (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)) ⧸ w.asIdeal) =
        Fintype.card Fq ^ m :=
    fun w => card_bdry_sup hq he hζc hMU hm hres hCU w
  -- the orbit representatives for `Γ_H` are representatives for `π₁^geo ∩ Gal(K_U/L)`
  have hgC : ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hm) ((IntermediateField.mem_restrict hCU _).1 hy) g
      (by rw [← hq]; exact hg)
  have hcoverL : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hLU).fixingSubgroup ∧ Q = g • Qt t := by
    intro Q hQ
    obtain ⟨t, g, hg, hgM, hQg⟩ := hcover Q hQ
    exact ⟨t, g, hg, mem_fix_sup hMU hCU hgM (hgC g hg), hQg⟩
  have hdisjL : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hLU).fixingSubgroup → Qt t' = g • Qt t → t = t' :=
    fun t t' g hg hgL h => hdisj t t' g hg (mem_fix_of_le hMU (le_sup_left.trans (le_fixF hLU hgL))) h
  -- the radicand as an element of `L`
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  have hαb : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) ^ N = (b : AlgebraicClosure F) :=
    (map_pow (maxUnram (Places.Rfin Fq F) F).val _ N).symm
  have hb : b ≠ 0 := by
    intro h
    have h2 : ((b : ↥(M ⊔ constLevel F p (e * m))) : AlgebraicClosure F) = 0 := by simp [h]
    rw [← hαb] at h2
    have h3 : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) = 0 :=
      (pow_eq_zero_iff (NeZero.ne N)).1 h2
    exact Units.ne_zero α (by exact_mod_cast h3)
  -- the places under the representatives, built along the S3 instance path (`bdryPlace` uses the generic one)
  let v : T → HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) := fun t =>
    ⟨(Qt t).comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := (hQt t).1),
      comap_inclU_ne_bot hLU (hQt t)⟩
  refine sum_reps_eq_zero hq he hζc hLU hLM hm le_sup_right hdi Qt hQt hcoverL hdisjL
    v (fun t => rfl) (α : maxUnram (Places.Rfin Fq F) F).2 hb hαb
    (fun t => χ ⟨τ t, hJΓ t (τ t).2⟩) ?_
  intro t
  rw [← hαχ ⟨τ t, hJΓ t (τ t).2⟩]
  exact @hnorm m hm hdvd0 hLU hDedI hFracI t (v t) rfl α b (Subtype.ext rfl)

include hq he hζc in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Global residue theorem with tame generators**: the generators `τ t` of `exists_norm_tau` (with their
characters `θ t`) can be chosen with `Σ_t χ(τ t) = 0` for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem exists_norm_tau_sum {N : ℕ} [NeZero N] (hN : IsUnit (N : Places.Rinf Fq F))
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
    (hJ : ∀ t σ, σ ∈ J t ↔ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F) ∧
      ∀ y : maxUnram (Places.Rfin Fq F) F, (y : AlgebraicClosure F) ∈ M → σ y = y)
    (d : T → ℕ) (hd0 : ∀ t, 0 < d t)
    (hNA : ∀ t, IsUnit ((N * d t : ℕ) : Places.Rfin Fq F))
    (hNR : ∀ t, IsUnit ((N * d t : ℕ) : Places.Rinf Fq F))
    (ζ : T → maxUnram (Places.Rfin Fq F) F) (hζ : ∀ t, IsPrimitiveRoot (ζ t) (N * d t))
    (hζI : ∀ t, ∀ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F), σ (ζ t) = ζ t)
    (x : T → HeightOneSpectrum (Places.Rinf Fq F))
    (hx : ∀ t, (x t).asIdeal =
      (Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))))
    (a : T → Places.Rfin Fq F)
    (ha : ∀ t, 1 < (x t).valuation F (algebraMap (Places.Rfin Fq F) F (a t)))
    (kk : T → ℕ)
    (hd : ∀ t, ∀ σ ∈ (Qt t).inertia (Pi1 (Places.Rfin Fq F) F), σ ^ (p ^ kk t * d t) ∈ J t) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, J t,
      (∀ t, TauProp (Qt t) (J t) N (τ t)) ∧
      (∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
        [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
        [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
          ↥(M ⊔ constLevel F p (e * k))]
        (t : T) (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
        v.asIdeal = (Qt t).comap (inclU (Places.Rinf Fq F) hLU) →
        ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
          (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
          kchar hζN (Γ := J t) α (τ t) =
            ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  exact exists_tau_sum_eq_zero hq he hζc hN hζN hζNg hM hMU Qt hQt hcover hdisj Γ hΓ J hJΓ
    (fun t σ hσ => (hJ t σ).1 hσ)
    (fun t τ => TauProp (Qt t) (J t) N τ)
    (htau_norm he hζN (fun σ hσ => hζNg σ (by rw [hq]; exact hσ)) hM hMU Qt hQt J hJ d hd0 hNA hNR ζ hζ hζI
      x hx a ha kk hd)

end

end Residue
end RamanujanPetersson

end


