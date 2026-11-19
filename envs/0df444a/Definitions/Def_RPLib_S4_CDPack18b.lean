-- Prove2me | Definitions.Def_RPLib_S4_CDPack18b
-- name    : RPLib_S4_CDPack18b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:08:21.178056+00:00
-- url     : https://prove2.me/theorems/2d99c7c4-ea7f-4488-9b49-2c5aafe0e66a
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 18b of 71
-- statement:
--   Part 18b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_TwBdry`: S4-PD (4), arithmetic twist part 1: the boundary hypotheses `hD`, `ht` of `h2Equiv_frob`
--   * `Def_RP_Cone_ResAsmFin`: S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack18

/-!
# Curve-duality library package, part 18b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_TwBdry`: S4-PD (4), arithmetic twist part 1: the boundary hypotheses `hD`, `ht` of `h2Equiv_frob`
* `Def_RP_Cone_ResAsmFin`: S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_TwBdry =====
section

/-!
# S4-PD (4), arithmetic twist part 1: the boundary hypotheses `hD`, `ht` of `h2Equiv_frob`

* `map_inf_conj_iff` (pure group theory): conjugate inertia groups have conjugate images `(Γ ⊓ I)`.
* `inert_conj_iff` (chart-generic): `P' = g⁻¹ • P` gives `x ∈ I(P') ↔ g x g⁻¹ ∈ I(P)`.
* `tt_injective`, `tt_bijective`: a boundary permutation `t` with `ψ⁻¹ • P s = h_s • P (t s)` (`h_s ∈ Γ`, `Γ` normal,
  points disjoint modulo `Γ`) is bijective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

open CurveCoh
open scoped Pointwise

theorem map_inf_conj_iff {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) [hΓ : Γ.Normal]
    {I1 I2 : Subgroup G} (g : G) (h : ∀ x, x ∈ I1 ↔ g * x * g⁻¹ ∈ I2) (d : Gf) :
    d ∈ (Γ ⊓ I1).map π ↔ π g * d * (π g)⁻¹ ∈ (Γ ⊓ I2).map π := by
  constructor
  · rintro ⟨x, ⟨hxΓ, hxI⟩, rfl⟩
    exact ⟨g * x * g⁻¹, ⟨hΓ.conj_mem x hxΓ g, (h x).1 hxI⟩, by simp only [map_mul, map_inv]⟩
  · rintro ⟨y, ⟨hyΓ, hyI⟩, hy⟩
    refine ⟨g⁻¹ * y * g, ⟨?_, (h _).2 ?_⟩, ?_⟩
    · simpa using hΓ.conj_mem y hyΓ g⁻¹
    · have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e]
      exact hyI
    · rw [map_mul, map_mul, map_inv, hy]
      group

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

theorem inert_conj_iff {P P' : Ideal (proChart A K R0)} {g : Pi1 A K} (hP : P' = g⁻¹ • P) (x : Pi1 A K) :
    x ∈ Inert P' ↔ g * x * g⁻¹ ∈ Inert P := by
  constructor
  · intro hx
    have h2 := conj_mem_inertia_smul g hx
    rw [hP, smul_inv_smul] at h2
    exact h2
  · intro hx
    have h2 := conj_mem_inertia_smul g⁻¹ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e, ← hP] at h2
    exact h2

theorem tt_injective {S : Type} (P : S → Ideal (proChart A K R0)) (Γ : Subgroup (Pi1 A K)) [hΓ : Γ.Normal]
    (hdis : ∀ s s', ∀ g ∈ Γ, P s' = g • P s → s = s') (ψ : Pi1 A K) (t : S → S) (h : S → Γ)
    (hspec : ∀ s, ψ⁻¹ • P s = ((h s : Γ) : Pi1 A K) • P (t s)) : Function.Injective t := by
  intro s s' hss
  have h1 := hspec s
  have h2 := hspec s'
  rw [hss] at h1
  refine hdis s s' (ψ * (((h s' : Γ) : Pi1 A K) * ((h s : Γ) : Pi1 A K)⁻¹) * ψ⁻¹)
    (hΓ.conj_mem _ (Γ.mul_mem (h s').2 (Γ.inv_mem (h s).2)) ψ) ?_
  calc P s' = ψ • ψ⁻¹ • P s' := (smul_inv_smul ψ _).symm
    _ = ψ • ((h s' : Γ) : Pi1 A K) • P (t s') := by rw [h2]
    _ = ψ • ((h s' : Γ) : Pi1 A K) • (((h s : Γ) : Pi1 A K)⁻¹ • ((h s : Γ) : Pi1 A K) • P (t s')) := by
        rw [inv_smul_smul]
    _ = ψ • ((h s' : Γ) : Pi1 A K) • (((h s : Γ) : Pi1 A K)⁻¹ • ψ⁻¹ • P s) := by rw [h1]
    _ = (ψ * (((h s' : Γ) : Pi1 A K) * ((h s : Γ) : Pi1 A K)⁻¹) * ψ⁻¹) • P s := by simp only [mul_smul]

theorem tt_bijective {S : Type} [Finite S] (P : S → Ideal (proChart A K R0)) (Γ : Subgroup (Pi1 A K))
    [Γ.Normal] (hdis : ∀ s s', ∀ g ∈ Γ, P s' = g • P s → s = s') (ψ : Pi1 A K) (t : S → S) (h : S → Γ)
    (hspec : ∀ s, ψ⁻¹ • P s = ((h s : Γ) : Pi1 A K) • P (t s)) : Function.Bijective t :=
  Finite.injective_iff_bijective.1 (tt_injective P Γ hdis ψ t h hspec)

end Gen

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResAsmFin =====
section

/-!
# S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`

`exists_norm_tau_sum` for `J t = I(Q t) ∩ ker π` in the S3 chart, with all level data (`d = |Gf|_{p'}`, roots of
unity, places, `x`) discharged (split from `Def_RP_Cone_ResAsm` for build time).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- `exists_norm_tau_sum` for `J t = I(Q t) ∩ ker π`, with the level data (`d = |Gf|_{p'}`, `ζ`, places, `x`)
discharged. -/
theorem exists_norm_tau_fin {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Finite Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
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
    (hJΓ : ∀ t, Jt π (Qt t) ≤ Γ) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, Jt π (Qt t),
      (∀ t, TauProp (Qt t) (Jt π (Qt t)) N (τ t)) ∧
      (∀ t, NormAll p e hζN M (Qt t) (Jt π (Qt t)) (τ t) k₀) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
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
  haveI : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) hd0.ne'⟩
  obtain ⟨ζd, hζd, hζdg⟩ := CP4a.exists_zeta_geo hq he hNd
  have hne : ∀ t, (Qt t).comap (algebraMap (Places.Rinf Fq F)
      (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) ≠ ⊥ := by
    intro t
    have := (hQt t).1
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hQt t).2
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  obtain ⟨x, hx⟩ : ∃ x : T → HeightOneSpectrum (Places.Rinf Fq F), ∀ t, (x t).asIdeal =
      (Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) :=
    ⟨fun t => ⟨(Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))),
      Ideal.IsPrime.comap _ (hK := (hQt t).1), hne t⟩, fun _ => rfl⟩
  obtain ⟨k₀, hk₀, τ, hT, hn, hs⟩ := exists_norm_tau_sum hq he (CP4a.exists_zeta_level he)
    (CP4a.isUnit_cast_Rinf hNF) hζN hζNg hM hMU Qt hQt hcover hdisj Γ hΓ (fun t => Jt π (Qt t)) hJΓ
    (fun t σ => Subgroup.mem_inf.trans (and_congr Iff.rfl (MonoidHom.mem_ker.trans (eq_one_iff_fixM hMU hπM σ))))
    (fun _ => d) (fun _ => hd0) (fun _ => CP4a.isUnit_cast_Rfin hNd) (fun _ => CP4a.isUnit_cast_Rinf hNd)
    (fun _ => ζd) (fun _ => hζd)
    (fun t σ hσ => by
      haveI := (hQt t).1
      exact hζdg σ (Kummer.inertia_le_pi1geo he hq (hP := (hQt t).1) hσ))
    x hx (fun _ => (⟨algebraMap Fq[X] F X, isIntegral_algebraMap⟩ : Places.Rfin Fq F))
    (fun t => by
      have h := JacComplete.one_lt_placeVal_inr_x (K := Fq) (F := F) (x t)
      exact h)
    (fun _ => Nat.factorization (Nat.card Gf) p)
    (fun t σ hσ => by
      show σ ^ (p ^ Nat.factorization (Nat.card Gf) p * d) ∈ Jt π (Qt t)
      rw [hpd]
      exact Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hσ _, by rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']⟩)
  refine ⟨k₀, hk₀, τ, hT, fun t => ?_, hs⟩
  intro k hk hdvd hLU hD hF v hv α b hαb
  exact @hn k hk hdvd hLU hD hF t v hv α b hαb

end S3

end

end Residue
end RamanujanPetersson

end


