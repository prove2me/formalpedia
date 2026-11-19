-- Prove2me | Definitions.Def_RPLib_S4_CDPack18
-- name    : RPLib_S4_CDPack18
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:03:13.846802+00:00
-- url     : https://prove2.me/theorems/281d3449-3309-46d9-8482-17e57eef9fc4
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 18 of 71
-- statement:
--   Part 18 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack16
import Definitions.Def_RPLib_S4_CDPack12
import Definitions.Def_RPLib_S4_CDPack06b
import Definitions.Def_RPLib_S4_CDPack17
import Definitions.Def_RPLib_S4_CDPack15c

/-!
# Curve-duality library package, part 18 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResAsm =====
section

/-!
# S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), boundary primes `P s` (one per `π₁^geo`-orbit), a finite level
`M ≤ K_U` with `π : π₁ → Gf` (`Gf` finite, `ker π = Gal(K_U/M)`), and `N` prime to `p`.

* `conj_mem_inertia_smul`: `x I(Q) x⁻¹ ⊆ I(x • Q)`; `Inert Q := I(Q)`, `Jt π Q := I(Q) ∩ ker π`.
* `cosQA`, `cosB`, `cosQA_base`: the cover points `x_t • P (sh t)` and the base points (trivial cosets), with the
  cover / disjointness / inertia facts proved for a general chart `(A, K, R0)` (elaboration note: statements in the
  concrete S3 chart never mention `Ideal.inertia` or a generic `[MulAction]` term directly; they go through these
  chart-generic abbreviations, which instantiate cheaply).
* `exists_norm_tau_fin` (level data discharged) is in `Def_RP_Cone_ResAsmFin`.
* The assembly `exists_resDat` is in `Def_RP_Cone_ResAsm2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- Inertia is conjugation-equivariant: `x I(Q) x⁻¹ ⊆ I(x • Q)`. -/
theorem conj_mem_inertia_smul {Q : Ideal (proChart A K R0)} (x : Pi1 A K) {σ : Pi1 A K}
    (hσ : σ ∈ Q.inertia (Pi1 A K)) : x * σ * x⁻¹ ∈ (x • Q).inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun b => ?_
  have h := AddSubgroup.mem_inertia.1 hσ (x⁻¹ • b)
  have e : (x * σ * x⁻¹) • b - b = x • (σ • x⁻¹ • b - x⁻¹ • b) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [e]
  exact Ideal.smul_mem_pointwise_smul x _ Q h

/-- The inertia group of `Q` (chart-generic, so that concrete charts can state it cheaply). -/
abbrev Inert (Q : Ideal (proChart A K R0)) : Subgroup (Pi1 A K) := Q.inertia (Pi1 A K)

/-- The part `I(Q) ∩ ker π` of the inertia of `Q`. -/
abbrev Jt {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (Q : Ideal (proChart A K R0)) : Subgroup (Pi1 A K) :=
  Q.inertia (Pi1 A K) ⊓ π.ker

variable (A K R0) in
/-- The pointwise action of `π₁` on ideals of the pro-chart. -/
abbrev instMA : MulAction (Pi1 A K) (Ideal (proChart A K R0)) := inferInstance

theorem stabI_gen (Q : Ideal (proChart A K R0)) (δ : Pi1 A K) (h : δ ∈ Inert Q) : δ • Q = Q :=
  MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q h)

end Conj

section Gen

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The base point over `s` (the trivial coset). -/
abbrev cosB (s : S) : CosT π Γ I := ⟨s, ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩

theorem locGen_of_eq {H : Type} [Group H] [TopologicalSpace H] {J I1 I2 : Subgroup H} {N : ℕ} {τ : J}
    (h : I1 = I2) (hl : PerfectCx.LocGen J I1 N τ) : PerfectCx.LocGen J I2 N τ := by
  subst h
  exact hl

end Gen

section CosA

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]
  {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (Γ : Subgroup (Pi1 A K)) {S : Type} (I : S → Subgroup (Pi1 A K))
  (P : S → Ideal (proChart A K R0))

/-- The cover point over `t`: `x_t • P (sh t)`. -/
abbrev cosQA (t : CosT π Γ I) : Ideal (proChart A K R0) := cosX π Γ I t • P t.1

theorem cosQA_base (s : S) : cosQA π Γ I P (cosB π Γ I s) = P s := by
  show cosX π Γ I ⟨s, ((1 : Γ.map π) : (Γ.map π) ⧸ cosD π Γ I s)⟩ • P s = P s
  rw [cosX_base, one_smul]

/-- The cover points are boundary primes. -/
theorem cosQA_bdry (hP : ∀ s, IsBdryPrime A K R0 (P s)) (t : CosT π Γ I) : IsBdryPrime A K R0 (cosQA π Γ I P t) :=
  isBdryPrime_smul A K R0 (cosX π Γ I t) (hP t.1)

/-- **Cover**: every boundary prime is `g • cosQA t` with `g ∈ Γ ∩ ker π`. -/
theorem cosQA_cover {H : Subgroup (Pi1 A K)} (hπH : ∀ σ, π σ = 1 ↔ σ ∈ H)
    (hcov : ∀ Q, IsBdryPrime A K R0 Q → ∃ s, ∃ g ∈ Γ, Q = g • P s) (hI : ∀ s, I s = Inert (P s)) :
    ∀ Q, IsBdryPrime A K R0 Q → ∃ t, ∃ g ∈ Γ, g ∈ H ∧ Q = g • cosQA π Γ I P t := by
  have hstabI : ∀ s, ∀ δ ∈ I s, δ • P s = P s := fun s δ hδ => stabI_gen (P s) δ ((hI s).le hδ)
  intro Q hQ
  obtain ⟨s, γ, hγ, rfl⟩ := hcov Q hQ
  obtain ⟨t, ht, g, hg, hgπ, hgt⟩ := cos_cover (π := π) hstabI s hγ
  exact ⟨t, g, hg, (hπH g).1 hgπ, by rw [hgt, ← ht]⟩

/-- **Disjointness** of the cover points. -/
theorem cosQA_disj {H : Subgroup (Pi1 A K)} (hπH : ∀ σ, π σ = 1 ↔ σ ∈ H)
    (hdis : ∀ s s', ∀ g ∈ Γ, P s' = g • P s → s = s') (hstab : ∀ s, ∀ u ∈ Γ, u • P s = P s → u ∈ I s) :
    ∀ t t', ∀ g ∈ Γ, g ∈ H → cosQA π Γ I P t' = g • cosQA π Γ I P t → t = t' :=
  fun t t' g hg hgH h => cos_disj hdis hstab t t' hg ((hπH g).2 hgH) h

theorem inert_cosQA_base (hI : ∀ s, I s = Inert (P s)) (s : S) : Inert (cosQA π Γ I P (cosB π Γ I s)) = I s := by
  rw [cosQA_base, hI s]

theorem i_le_of_bdry (hI : ∀ s, I s = Inert (P s)) (hgeo : ∀ Q, IsBdryPrime A K R0 Q → Inert Q ≤ Γ)
    (hP : ∀ s, IsBdryPrime A K R0 (P s)) (s : S) : I s ≤ Γ :=
  (hI s).le.trans (hgeo _ (hP s))

theorem jt_le (hgeo : ∀ Q, IsBdryPrime A K R0 Q → Inert Q ≤ Γ) (hP : ∀ s, IsBdryPrime A K R0 (P s))
    (t : CosT π Γ I) : Jt π (cosQA π Γ I P t) ≤ Γ ⊓ π.ker := fun σ hσ =>
  Subgroup.mem_inf.2 ⟨hgeo _ (cosQA_bdry π Γ I P hP t) (Subgroup.mem_inf.1 hσ).1, (Subgroup.mem_inf.1 hσ).2⟩

theorem jt_base_iff (hI : ∀ s, I s = Inert (P s)) (hIΓ : ∀ s, I s ≤ Γ) (s : S) (g : Pi1 A K) :
    g ∈ Jt π (cosQA π Γ I P (cosB π Γ I s)) ↔ g ∈ Γ ⊓ I s ∧ π g = 1 :=
  Subgroup.mem_inf.trans (and_congr ((SetLike.ext_iff.1 (inert_cosQA_base π Γ I P hI s) g).trans
    ⟨fun h => Subgroup.mem_inf.2 ⟨hIΓ s h, h⟩, fun h => (Subgroup.mem_inf.1 h).2⟩) MonoidHom.mem_ker)

variable (τ : ∀ t : CosT π Γ I, Jt π (cosQA π Γ I P t))

theorem tau_base_I (hI : ∀ s, I s = Inert (P s)) (s : S) : (τ (cosB π Γ I s) : Pi1 A K) ∈ I s :=
  (inert_cosQA_base π Γ I P hI s).le (Subgroup.mem_inf.1 (τ (cosB π Γ I s)).2).1

theorem tau_base_ker (s : S) : π (τ (cosB π Γ I s) : Pi1 A K) = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 (τ (cosB π Γ I s)).2).2

theorem yconj_ker (t : CosT π Γ I) :
    π (cosX π Γ I t * (τ (cosB π Γ I t.1) : Pi1 A K) * (cosX π Γ I t)⁻¹) = 1 := by
  rw [map_mul, map_mul, map_inv, tau_base_ker π Γ I P τ t.1, mul_one, mul_inv_cancel]

theorem yconj_mem (hI : ∀ s, I s = Inert (P s)) (hIΓ : ∀ s, I s ≤ Γ) (t : CosT π Γ I) :
    cosX π Γ I t * (τ (cosB π Γ I t.1) : Pi1 A K) * (cosX π Γ I t)⁻¹ ∈ Γ ⊓ π.ker :=
  Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.mul_mem (cosX_mem t) (hIΓ t.1 (tau_base_I π Γ I P τ hI t.1)))
    (Γ.inv_mem (cosX_mem t)), MonoidHom.mem_ker.2 (yconj_ker π Γ I P τ t)⟩

theorem yconj_memJ (hI : ∀ s, I s = Inert (P s)) (t : CosT π Γ I) :
    cosX π Γ I t * (τ (cosB π Γ I t.1) : Pi1 A K) * (cosX π Γ I t)⁻¹ ∈ Jt π (cosQA π Γ I P t) :=
  Subgroup.mem_inf.2 ⟨Residue.conj_mem_inertia_smul (cosX π Γ I t) ((hI t.1).le (tau_base_I π Γ I P τ hI t.1)),
    MonoidHom.mem_ker.2 (yconj_ker π Γ I P τ t)⟩

end CosA

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- `π σ = 1` iff `σ` fixes `M` (from `ker π = Gal(K_U/M)`). -/
theorem eq_one_iff_fixM {M : IntermediateField F (AlgebraicClosure F)} (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] {π : Pi1 (Places.Rfin Fq F) F →* Gf}
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) (σ : Pi1 (Places.Rfin Fq F) F) :
    π σ = 1 ↔ ∀ y : maxUnram (Places.Rfin Fq F) F, (y : AlgebraicClosure F) ∈ M → σ y = y :=
  (hπM σ).trans ⟨fun h y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).1 h y
      ((IntermediateField.mem_restrict hMU y).2 hy),
    fun h => (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy =>
      h y ((IntermediateField.mem_restrict hMU y).1 hy)⟩

include hq he in
set_option maxHeartbeats 400000 in
/-- Inertia of a boundary prime lies in `π₁^geo`. -/
theorem inertia_le_geo_S3 {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) :
    Inert Q ≤ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) := fun _ hg =>
  Kummer.inertia_le_pi1geo he hq (hP := hQ.1) hg

include hq he in
set_option maxHeartbeats 400000 in
/-- An element of `π₁^geo` stabilising a boundary prime lies in its inertia. -/
theorem stab_S3 {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) {u : Pi1 (Places.Rfin Fq F) F}
    (hu : u ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (huQ : u • Q = Q) : u ∈ Inert Q := by
  haveI : Q.IsPrime := hQ.1
  obtain ⟨hfin, hcard⟩ := CP4a.good_inf hq Q hQ
  haveI := hfin
  exact stab_mem_inertia he (CP4a.exists_zeta_level he) hcard (by rw [← hq]; exact hu) huQ

include hq he in
set_option maxHeartbeats 400000 in
/-- The inertia groups `I s = I(P s)` lie in `π₁^geo`. -/
theorem ile_S3 {S : Type} (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
    (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s)) (s : S) :
    I s ≤ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) :=
  i_le_of_bdry _ I P hI (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP s

include hq he in
set_option maxHeartbeats 400000 in
/-- **Disjointness** in the S3 chart. -/
theorem cosQA_disj_S3 {M : IntermediateField F (AlgebraicClosure F)} (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {S : Type} (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s)) :
    ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup →
        cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t' =
          g • cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t → t = t' :=
  cosQA_disj π _ I P hπM hdis fun s _ hu hus => (hI s).ge (stab_S3 hq he (hP s) hu hus)

set_option maxHeartbeats 400000 in
/-- `Γ_H = π₁^geo ∩ ker π` in the shape of `exists_norm_tau_sum`. -/
theorem memΓH_S3 {M : IntermediateField F (AlgebraicClosure F)} (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] {π : Pi1 (Places.Rfin Fq F) F →* Gf}
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) (σ : Pi1 (Places.Rfin Fq F) F) :
    σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker ↔
      σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup :=
  Subgroup.mem_inf.trans (and_congr Iff.rfl (MonoidHom.mem_ker.trans (hπM σ)))

end S3

end

end Residue
end RamanujanPetersson

end


