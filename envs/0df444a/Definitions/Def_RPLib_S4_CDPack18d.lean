-- Prove2me | Definitions.Def_RPLib_S4_CDPack18d
-- name    : RPLib_S4_CDPack18d
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:37:14.714248+00:00
-- url     : https://prove2.me/theorems/588c6182-4a0c-4270-ba12-634c59c0b4e1
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 18d of 71
-- statement:
--   Part 18d of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack10
import Definitions.Def_RPLib_S4_CDPack16
import Definitions.Def_RPLib_S4_CDPack18c

/-!
# Curve-duality library package, part 18d of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_TwS3 =====
section

/-!
# S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data

* `twist_jt` (chart-generic): the local twist `χ (φ σ φ⁻¹) = q • χ σ` on `J = I(Q) ∩ ker π` for `φ • Q = Q`.
* `twist_loc_S3`: the same in the S3 chart for a Frobenius lift `φ` (`q = |𝔽_q|`), level data discharged.
* `tw_core`: for the normalised generators `τ` of `exists_norm_tau_fin`, `g⁻¹` a Frobenius lift with
  `P u = g⁻¹ • P s`: `χ (g⁻¹ τ_s g) = q • χ τ_u` (local twist if `u = s`, global normalisation otherwise).
* **`exists_resDat_tw`**: `exists_resDat` together with this twist clause.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Gen

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option maxHeartbeats 800000 in
/-- **Local twist on `J = I(Q) ∩ ker π`** (chart-generic): for `φ • Q = Q` with `φ ζ = ζ ^ q`. -/
theorem twist_jt {Gf : Type} [Group Gf] [Finite Gf] (π : Pi1 A K →* Gf) {Q : Ideal (proChart A K R0)}
    (hQ : IsBdryPrime A K R0 Q) [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ}
    [NeZero N] [NeZero d] (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0))
    {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Inert Q, σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    (a : A) (ha : 1 < x.valuation K (algebraMap A K a)) (k : ℕ) (hpd : p ^ k * d = Nat.card Gf)
    (φ : Pi1 A K) (hφQ : φ • Q = Q) (q : ℕ) (hφζ : φ ζ = ζ ^ q)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0) (χ : Jt π Q → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (σ : Pi1 A K) (hσ : σ ∈ Jt π Q)
    (hσ' : φ * σ * φ⁻¹ ∈ Jt π Q) :
    χ ⟨φ * σ * φ⁻¹, hσ'⟩ = q • χ ⟨σ, hσ⟩ := by
  have hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q := fun b => by
    have h := Ideal.smul_mem_pointwise_smul_iff (a := φ) (S := Q) (x := b)
    rwa [hφQ] at h
  have hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ Jt π Q := fun σ hσ => by
    rw [hpd]
    exact Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hσ _, by rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']⟩
  exact twist_hom (p := p) hQ hNA hNR hζ hζI x hx ha inf_le_left k hd φ hφ q hφζ hMo χ hχc hχ σ hσ hσ'

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Local twist in the S3 chart**: a Frobenius lift `φ` stabilising the boundary prime `Q` acts on every locally
constant homomorphism `χ : I(Q) ∩ ker π → M` (`N M = 0`) by `χ (φ σ φ⁻¹) = q • χ σ`. -/
theorem twist_loc_S3 {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0) {Gf : Type} [Group Gf] [Finite Gf]
    (π : Pi1 (Places.Rfin Fq F) F →* Gf) {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) (φ : Pi1 (Places.Rfin Fq F) F)
    (hφF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ) (hφQ : φ • Q = Q)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0) (χ : Jt π Q → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (σ : Pi1 (Places.Rfin Fq F) F)
    (hσ : σ ∈ Jt π Q) (hσ' : φ * σ * φ⁻¹ ∈ Jt π Q) :
    χ ⟨φ * σ * φ⁻¹, hσ'⟩ = Fintype.card Fq • χ ⟨σ, hσ⟩ := by
  have hp : p.Prime := Fact.out
  have hc0 : Nat.card Gf ≠ 0 := Nat.card_pos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.card Gf / p ^ Nat.factorization (Nat.card Gf) p := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd_def]
    exact Nat.ordCompl_pos p hc0
  have hdF : (d : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p, hd_def]
    exact Nat.not_dvd_ordCompl hp hc0
  have hpd : p ^ Nat.factorization (Nat.card Gf) p * d = Nat.card Gf := by
    rw [hd_def]
    exact Nat.ordProj_mul_ordCompl_eq_self (Nat.card Gf) p
  have hNd : ((N * d : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero hNF hdF
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) hd0.ne'⟩
  have : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨ζd, hζd, hζc⟩ := Kummer.exists_zeta (Places.Rfin Fq F) F p he (N * d) hNd
  have hne : Q.comap (algebraMap (Places.Rinf Fq F)
      (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) ≠ ⊥ := by
    have := hQ.1
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  obtain ⟨x, hx⟩ : ∃ x : HeightOneSpectrum (Places.Rinf Fq F), x.asIdeal =
      Q.comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) :=
    ⟨⟨_, Ideal.IsPrime.comap _ (hK := hQ.1), hne⟩, rfl⟩
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  exact twist_jt π hQ (p := p) (CP4a.isUnit_cast_Rfin hNd) (CP4a.isUnit_cast_Rinf hNd) hζd
    (fun σ' hσ'' => Kummer.zeta_fixed hζc σ' (by
      have h := Kummer.inertia_le_pi1geo he hq (hP := hQ.1) hσ''
      rwa [hq] at h)) x hx
    (⟨algebraMap Fq[X] F X, isIntegral_algebraMap⟩ : Places.Rfin Fq F)
    (by have h := JacComplete.one_lt_placeVal_inr_x (K := Fq) (F := F) x; exact h)
    _ hpd φ hφQ _ (hφF ζd (by rw [hq]; exact hζc)) hMo χ hχc hχ σ hσ hσ'

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

include hq he hP in
set_option maxHeartbeats 800000 in
/-- Case `u = s` of `tw_core`: `g⁻¹` stabilises `P u` (local twist). -/
theorem tw_same [Finite Gf] {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0) {u : S} (g : Pi1 (Places.Rfin Fq F) F)
    (hgF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹) (hu : P u = g⁻¹ • P u)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0)
    (χ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (hc : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) * g ∈
      Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) :
    χ ⟨_, hc⟩ = Fintype.card Fq • χ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
  have hφQ : g⁻¹ • cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) =
      cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) := by
    have key : ∀ X, X = P u → g⁻¹ • X = X := by
      rintro X rfl
      exact hu.symm
    exact key _ (cosQA_base π _ I P u)
  have hc' : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ ∈ Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
    rw [inv_inv]
    exact hc
  have h := twist_loc_S3 hq he hNF π (cosQA_bdry π _ I P hP _) g⁻¹ hgF hφQ hMo χ hχc hχ _ (τ _).2 hc'
  have e1 : (⟨_, hc'⟩ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) = ⟨_, hc⟩ := by
    apply Subtype.ext
    show g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ = g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) * g
    rw [inv_inv]
  exact (congrArg χ e1).symm.trans h

include hq he hP hI in
set_option maxHeartbeats 1600000 in
/-- **Twist of the normalised generators**: if `g⁻¹` is a Frobenius lift with `P u = g⁻¹ • P s`, then
`χ (g⁻¹ τ_s g) = q • χ τ_u` for every locally constant homomorphism `χ : J_u → M` (`N M = 0`). -/
theorem tw_core [Finite Gf] {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N) (hζNc : IsConst (p ^ e) ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • P s)
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    [Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)] {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hT : ∀ t, TauProp (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) N (τ t))
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (s u : S) (g : Pi1 (Places.Rfin Fq F) F)
    (hgF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹) (hu : P u = g⁻¹ • P s)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0)
    (χ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (hc : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) * g ∈
      Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) :
    χ ⟨_, hc⟩ = Fintype.card Fq • χ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
  by_cases hus : u = s
  · subst hus
    exact tw_same hq he π P hP I τ hNF g hgF hu hMo χ hχc hχ hc
  classical
  have hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN := by
    rw [hq]
    exact Kummer.zeta_fixed hζNc
  have hgF' : IsFrobLift (Places.Rfin Fq F) F (p ^ e) g⁻¹ := by
    rw [← hq]
    exact hgF
  have hx : g⁻¹ ζN = epow ζN ((p ^ e : ℕ) : ZMod N) := Kummer.frobLift_zeta hζN hζNc hgF'
  have hτ' : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ ∈ Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
    rw [inv_inv]
    exact hc
  have h1 := normAll_conj_tw hq he hζN hM hMU (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s))
    (ile_S3 hq he P hP I hI s (tau_base_I π _ I P τ hI s)) ((hπM _).1 (tau_base_ker π _ I P τ s)) hx hτ'
    (normAll_base π P I τ hζN hn s)
  rw [← hu] at h1
  have h2 := normAll_base π P I τ hζN hn u
  have hJΓu := jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP
    (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)
  obtain ⟨χ', hχ'c, hχ', hχ't⟩ := yconj_exist hq he π P hP I hI τ hNF hPic hζN hζNg hM hMU hπM hcov hdis hk₀ hn
    (Pi.single (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) 1 -
      Pi.single (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) 1)
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self])
  have hne : cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u ≠
      cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s := fun h => hus (congrArg Sigma.fst h)
  have hχu : χ' ⟨τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hJΓu (τ _).2⟩ = 1 := by
    rw [← yconj_chi hq he π P hP I hI τ hζN hζNg hM hMU hπM hk₀ hn χ' hχ'c hχ'
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hχ't]
    simp [Pi.single_apply, hne]
  have h3 := chi_eq_of_normTw hq he hζN hM hMU _ (fun σ hσ => hζNg σ (Subgroup.mem_inf.1 hσ).1)
    (memΓH_S3 hMU hπM) (hP u) _ hJΓu _ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))
    hk₀ hk₀ h1 h2 χ' hχ'c hχ'
  rw [hχu, mul_one] at h3
  obtain ⟨θ, -, -, hθ1, -, hgen⟩ := hT (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)
  have h4 : ∀ σ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)),
      χ' ⟨σ, hJΓu σ.2⟩ = χ' ⟨τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hJΓu (τ _).2⟩ * θ σ :=
    hgen (fun σ => χ' ⟨σ, hJΓu σ.2⟩) (hχ'c.comp_continuous (continuous_subtype_val.subtype_mk _))
      (fun a b => hχ' ⟨a, hJΓu a.2⟩ ⟨b, hJΓu b.2⟩)
  have h5 := h4 ⟨_, hτ'⟩
  rw [hχu, one_mul] at h5
  have hθc : θ ⟨_, hτ'⟩ = ((p ^ e : ℕ) : ZMod N) := h5.symm.trans h3
  have e1 : (⟨_, hτ'⟩ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) = ⟨_, hc⟩ := by
    apply Subtype.ext
    show g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ = g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) * g
    rw [inv_inv]
  rw [← e1, eq_val_nsmul_of_gen hMo hθ1 (fun χ0 hc0 h0 => ⟨_, hgen χ0 hc0 h0⟩) χ hχc hχ ⟨_, hτ'⟩, hθc,
    ZMod.val_natCast, nsmul_mod_eq hMo, ← hq]

end Tau

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Arithmetic residue data with the Frobenius twist**: `exists_resDat` together with
`χ (g⁻¹ σ_s g) = q • χ σ_u` whenever `g⁻¹` is a Frobenius lift with `P u = g⁻¹ • P s`. -/
theorem exists_resDat_tw {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Finite Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
    (hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • P s)
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
    [Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)] :
    ∃ D : PerfectCx.ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I N
      (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I),
      ∀ (s u : S) (g : Pi1 (Places.Rfin Fq F) F), IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹ →
        P u = g⁻¹ • P s → ∀ (Mo : Type) [AddCommGroup Mo], (∀ m : Mo, N • m = 0) →
        ∀ χ : D.J u → Mo, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) →
        ∀ hc : g⁻¹ * D.σ s * g ∈ D.J u,
          χ ⟨_, hc⟩ = Fintype.card Fq • χ ⟨D.σ u, (D.hJ u _).2 ⟨D.hσ u, D.hσπ u⟩⟩ := by
  obtain ⟨ζN, hζN, hζNc⟩ := Kummer.exists_zeta (Places.Rfin Fq F) F p he N hNF
  have hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN := by
    rw [hq]
    exact Kummer.zeta_fixed hζNc
  obtain ⟨k₀, hk₀, τ, hT, hn, hs⟩ := exists_norm_tau_fin hq he hNF hζN hζNg hM hMU π hπM
    (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P) (cosQA_bdry π _ I P hP)
    (cosQA_cover π _ I P hπM hcov hI) (cosQA_disj_S3 hq he hMU π hπM P hP hdis I hI)
    (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP)
  refine ⟨{
    σ := fun s => (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F)
    hσ := fun s => Subgroup.mem_inf.2 ⟨ile_S3 hq he P hP I hI s (tau_base_I π _ I P τ hI s), tau_base_I π _ I P τ hI s⟩
    hσπ := tau_base_ker π _ I P τ
    J := fun s => Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s))
    hJ := jt_base_iff π _ I P hI (ile_S3 hq he P hP I hI)
    hloc := locGen_base π P I hI τ hT
    ΓH := pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker
    hΓH := fun g => Subgroup.mem_inf.trans (and_congr Iff.rfl MonoidHom.mem_ker)
    sh := Sigma.fst
    x := cosX π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I
    hx := fun t => cosX_mem t
    y := fun t => ⟨_, yconj_mem π _ I P τ hI (ile_S3 hq he P hP I hI) t⟩
    hy := fun t => rfl
    hrep := fun s q hq' => cos_rep s q hq'
    hR := fun χ hχc hχ => (Finset.sum_congr rfl fun t _ =>
      yconj_chi hq he π P hP I hI τ hζN hζNg hM hMU hπM hk₀ hn χ hχc hχ t).trans (hs χ hχc hχ)
    hE := yconj_exist hq he π P hP I hI τ hNF hPic hζN hζNg hM hMU hπM hcov hdis hk₀ hn
    s0 := Classical.arbitrary S }, fun s u g hgF hu Mo _ hMo χ hχc hχ hc => ?_⟩
  exact tw_core hq he π P hP I hI τ hNF hPic hζN hζNc hM hMU hπM hcov hdis hk₀ hT hn s u g hgF hu hMo χ hχc hχ hc

end S3

end

end Residue
end RamanujanPetersson

end


