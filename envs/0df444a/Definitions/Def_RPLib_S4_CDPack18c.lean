-- Prove2me | Definitions.Def_RPLib_S4_CDPack18c
-- name    : RPLib_S4_CDPack18c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:25:57.864764+00:00
-- url     : https://prove2.me/theorems/af08b3a1-f9b9-4d77-8c64-4f38aa8c0a40
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 18c of 71
-- statement:
--   Part 18c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack18b

/-!
# Curve-duality library package, part 18c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResAsm2 =====
section

/-!
# S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart

Continues `Def_RP_Cone_ResAsm` (split for build time). With `τ t` the normalised generators of
`exists_norm_tau_fin` at the cover points `cosQA t`:

* `locGen_base`, `normAll_base`: the base-point data `σ s := τ (cosB s)`.
* `yconj_chi`: `χ (x_t σ x_t⁻¹) = χ (τ t)`; `yconj_exist`: existence at the conjugates.
* **`exists_resDat`**: under `PicDivX`, a `ResDat π π₁^geo I N (CosT π π₁^geo I)` (the input of `ResDat.toResHyp`).
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

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

include hI in
set_option maxHeartbeats 400000 in
theorem locGen_base {N : ℕ}
    (hT : ∀ t, TauProp (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) N (τ t)) (s : S) :
    PerfectCx.LocGen (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s))) (I s) N
        (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)) :=
  locGen_of_eq (inert_cosQA_base π _ I P hI s) (hT (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s))

set_option maxHeartbeats 400000 in
theorem normAll_base {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} {k₀ : ℕ}
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀) (s : S) :
    NormAll p e hζN M (P s) (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)))
      (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)) k₀ := by
  have key : ∀ X, X = cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) →
      NormAll p e hζN M X (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)))
        (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)) k₀ := by
    rintro X rfl
    exact hn _
  exact key (P s) (cosQA_base π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P s).symm

include hq he hP hI in
set_option maxHeartbeats 800000 in
/-- The conjugate `y t = x_t σ x_t⁻¹` and `τ t` have the same `χ`-value. -/
theorem yconj_chi {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (χ : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) → ZMod N) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) (t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I) :
    χ ⟨_, yconj_mem π _ I P τ hI (ile_S3 hq he P hP I hI) t⟩ =
      χ ⟨τ t, jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP t (τ t).2⟩ := by
  have h1 := normAll_conj hq he hζN hM hMU (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I t.1))
    (ile_S3 hq he P hP I hI t.1 (tau_base_I π _ I P τ hI t.1)) ((hπM _).1 (tau_base_ker π _ I P τ t.1))
    (hζNg _ (cosX_mem t)) (yconj_memJ π _ I P τ hI t) (normAll_base π P I τ hζN hn t.1)
  exact chi_eq_of_norm hq he hζN hM hMU _ (fun σ hσ => hζNg σ (Subgroup.mem_inf.1 hσ).1) (memΓH_S3 hMU hπM)
    (cosQA_bdry π _ I P hP t) (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP t) ⟨_, yconj_memJ π _ I P τ hI t⟩ (τ t)
    hk₀ hk₀ h1 (hn t) χ hχc hχ

include hq he hP hI in
set_option maxHeartbeats 800000 in
/-- Existence at the conjugates `y t` (from `exists_kchar_of_sum_zero`). -/
theorem yconj_exist {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • P s)
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    [Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)] {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (c : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I → ZMod N) (hc : ∑ t, c t = 0) :
    ∃ χ : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) → ZMod N, IsLocallyConstant χ ∧
      (∀ a b, χ (a * b) = χ a + χ b) ∧ ∀ t, χ ⟨_, yconj_mem π _ I P τ hI (ile_S3 hq he P hP I hI) t⟩ = c t := by
  obtain ⟨χ, hχc, hχ, hχt⟩ := exists_kchar_of_sum_zero hq he (CP4a.exists_zeta_level he)
    (CP4a.isUnit_cast_Rfin hNF) hPic hζN hζNg hM hMU (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P)
    (cosQA_bdry π _ I P hP) (cosQA_cover π _ I P hπM hcov hI) (cosQA_disj_S3 hq he hMU π hπM P hP hdis I hI)
    (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (fun t => Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP) τ hk₀
    (by
      intro k hk hdvd hLU hD hF t v hv α b hαb
      exact @hn t k hk hdvd hLU hD hF v hv α b hαb) c hc
  exact ⟨χ, hχc, hχ, fun t =>
    (yconj_chi hq he π P hP I hI τ hζN hζNg hM hMU hπM hk₀ hn χ hχc hχ t).trans (hχt t)⟩

end Tau

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Arithmetic residue data**: for boundary primes `P s` (one per `π₁^geo`-orbit, `I s = I(P s)`), a finite level
`M` with `ker π = Gal(K_U/M)` and `N` prime to `p`, under `PicDivX` there is a `ResDat` over the cover points
`CosT π π₁^geo I` (`σ s` normalised tame generators at the base points, `y t = x_t σ x_t⁻¹`; `hR` = global residue
theorem, `hE` = existence). -/
theorem exists_resDat {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
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
    Nonempty (PerfectCx.ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I N
      (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)) := by
  obtain ⟨ζN, hζN, hζNg⟩ := CP4a.exists_zeta_geo hq he hNF
  obtain ⟨k₀, hk₀, τ, hT, hn, hs⟩ := exists_norm_tau_fin hq he hNF hζN hζNg hM hMU π hπM
    (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P) (cosQA_bdry π _ I P hP)
    (cosQA_cover π _ I P hπM hcov hI) (cosQA_disj_S3 hq he hMU π hπM P hP hdis I hI)
    (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP)
  exact ⟨{
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
    s0 := Classical.arbitrary S }⟩

end S3

end

end Residue
end RamanujanPetersson

end


