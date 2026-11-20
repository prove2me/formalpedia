-- Prove2me | Definitions.Def_RPLib_F2_026
-- name    : RPLib_F2_026
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T12:05:23.335212+00:00
-- url     : https://prove2.me/theorems/65bf9611-9918-45ba-9e08-9bd45a65c3af
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 026 of 70
-- statement:
--   File 026 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
--   * `S4.Def_RP_Cone_TwBdry`: S4-PD (4), arithmetic twist part 1: the boundary hypotheses `hD`, `ht` of `h2Equiv_frob`
--   * `S4.Def_RP_Cone_TwLoc`: S4-PD (4), arithmetic twist part A: the local twist of tame characters
--   * `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
--   * `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
--   * `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
--   * `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
--   * `S4.Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_024

/-!
# Ramanujan-Petersson curve library (flat edition), file 026 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
* `S4.Def_RP_Cone_TwBdry`: S4-PD (4), arithmetic twist part 1: the boundary hypotheses `hD`, `ht` of `h2Equiv_frob`
* `S4.Def_RP_Cone_TwLoc`: S4-PD (4), arithmetic twist part A: the local twist of tame characters
* `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
* `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
* `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
* `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
* `S4.Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
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

-- ===== S4.Def_RP_Cone_TwLoc =====
section

/-!
# S4-PD (4), arithmetic twist part A: the local twist of tame characters

For `J ≤ I(Q)` with `σ ^ (p^k d) ∈ J` on `I(Q)` (as in `tame_inertia_le`), and `φ` stabilising `Q` with
`φ ζ = ζ ^ q` (`ζ` a primitive `N d`-th root of unity fixed by inertia):

* `exists_twist_char`: a generator `θ : J → ℤ/N` of the locally constant characters with
  `θ (φ σ φ⁻¹) = q • θ σ` (the cyclotomic twist, from the twist clause of `exists_tame_char` at level `N d`).
* `twist_hom`: every locally constant homomorphism `χ : J → M` to an abelian group killed by `N` satisfies
  `χ (φ σ φ⁻¹) = q • χ σ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section Alg

/-- An additive character takes `σ ^ n` to `n • r σ`. -/
theorem char_pow {G : Type} [Group G] {B : Type} [AddCommGroup B] (r : G → B)
    (hr : ∀ σ τ, r (σ * τ) = r σ + r τ) (σ : G) (n : ℕ) : r (σ ^ n) = n • r σ := by
  have h1 : r 1 = 0 := by
    have h := hr 1 1
    rw [mul_one] at h
    simpa using h
  induction n with
  | zero => rw [pow_zero, h1, zero_nsmul]
  | succ n ih => rw [pow_succ, hr, ih, succ_nsmul]

theorem val_nsmul_nsmul {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (q : ℕ)
    (z : ZMod N) (m : M) : (q • z).val • m = q • z.val • m := by
  have e : q • z = ((q * z.val : ℕ) : ZMod N) := by
    rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e, ZMod.val_natCast, nsmul_mod_eq hM, mul_nsmul']

end Alg

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Local twist.** For `J ≤ I(Q)` as in `tame_inertia_le` and `φ` stabilising `Q` with `φ ζ = ζ ^ q`, there is a
generator `θ` of the locally constant characters `J → ℤ/N` with `θ (φ σ φ⁻¹) = q • θ σ`. -/
theorem exists_twist_char {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    (φ : Pi1 A K) (hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q) (q : ℕ) (hφζ : φ ζ = ζ ^ q) :
    ∃ θ : J → ZMod N, ∃ τ₀ : J, IsLocallyConstant θ ∧ (∀ σ τ, θ (σ * τ) = θ σ + θ τ) ∧ θ τ₀ = 1 ∧
      (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ τ, χ (σ * τ) = χ σ + χ τ) →
        ∃ c : ZMod N, ∀ σ, χ σ = c * θ σ) ∧
      ∀ σ (hσ : σ ∈ J) (hσ' : φ * σ * φ⁻¹ ∈ J), θ ⟨φ * σ * φ⁻¹, hσ'⟩ = q • θ ⟨σ, hσ⟩ := by
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne d)⟩
  obtain ⟨θ', hθc, hθm, ⟨σ₀, hθ1⟩, -, htw⟩ := exists_tame_char (p := p) hQ hNA hNR hζ hζI x hx ha
  let ι : J → Q.inertia (Pi1 A K) := fun σ => ⟨σ, hJ σ.2⟩
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  let r : J → ZMod (N * d) := fun σ => θ' (ι σ)
  have hr : ∀ σ τ, r (σ * τ) = r σ + r τ := fun σ τ => hθm (ι σ) (ι τ)
  have hpow : ∀ n : ℕ, θ' (σ₀ ^ n) = (n : ZMod (N * d)) := by
    intro n
    rw [char_pow θ' hθm σ₀ n, hθ1, nsmul_eq_mul, mul_one]
  let g : J := ⟨(σ₀ : Pi1 A K) ^ (p ^ k * d), hd _ σ₀.2⟩
  have hg : r g = ((p ^ k * d : ℕ) : ZMod (N * d)) := by
    rw [← hpow]
    show θ' (ι g) = _
    congr 1
  have hp : Nat.Coprime p (N * d) := coprime_of_isUnit (K := K) hNA
  obtain ⟨f, hf, τ₀, hτ₀⟩ := exists_div_char (Fact.out : p.Prime).pos hp r hr hg
  let θ : J → ZMod N := fun σ => f (r σ)
  have hθm' : ∀ σ τ, θ (σ * τ) = θ σ + θ τ := hf
  have hθc' : IsLocallyConstant θ := (hθc.comp_continuous hιc).comp f
  have hN : IsUnit (N : R0) := by
    rw [Nat.cast_mul] at hNR
    exact isUnit_of_mul_isUnit_left hNR
  have hζN : IsPrimitiveRoot (ζ ^ d) N := IsPrimitiveRoot.pow (NeZero.pos _) hζ (mul_comm N d)
  have hζJ : ∀ σ ∈ J, σ (ζ ^ d) = ζ ^ d := fun σ hσ => by rw [map_pow, hζI σ (hJ hσ)]
  have hw : φ ζ = epow ζ ((q : ℕ) : ZMod (N * d)) := by
    rw [epow, ZMod.val_natCast, pow_mod_N hζ]
    exact hφζ
  refine ⟨θ, τ₀, hθc', hθm', hτ₀, fun χ hχc hχ => exists_eq_mul_of_surj
    (fun χ' hc' h' => exists_ne_eq_of_family_le hQ hN hζN hJ hζJ χ' hc' h') hθc' hθm' hτ₀ hχc hχ,
    fun σ hσ hσ' => ?_⟩
  -- `r (φ σ φ⁻¹) = q r σ = r (σ ^ q)`, then apply `f`
  have hc : φ⁻¹ * (φ * σ * φ⁻¹) * φ ∈ Q.inertia (Pi1 A K) := inertia_conj hφ (hJ hσ')
  have h1 := htw φ hφ ((q : ℕ) : ZMod (N * d)) hw (φ * σ * φ⁻¹) (hJ hσ')
  have e1 : (⟨φ⁻¹ * (φ * σ * φ⁻¹) * φ, hc⟩ : Q.inertia (Pi1 A K)) = ι ⟨σ, hσ⟩ :=
    Subtype.ext (by show φ⁻¹ * (φ * σ * φ⁻¹) * φ = σ; group)
  have h2 : r ⟨φ * σ * φ⁻¹, hσ'⟩ = r (⟨σ, hσ⟩ ^ q) := by
    rw [char_pow r hr, nsmul_eq_mul]
    show θ' ⟨φ * σ * φ⁻¹, hJ hσ'⟩ = _
    rw [h1, e1]
  show f (r ⟨φ * σ * φ⁻¹, hσ'⟩) = q • f (r ⟨σ, hσ⟩)
  rw [h2]
  exact char_pow θ hθm' ⟨σ, hσ⟩ q

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Local twist for `N`-torsion coefficients**: every locally constant homomorphism `χ : J → M` (`N M = 0`)
satisfies `χ (φ σ φ⁻¹) = q • χ σ` when `φ` stabilises `Q` and `φ ζ = ζ ^ q`. -/
theorem twist_hom {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N d : ℕ} [NeZero N] [NeZero d]
    (hNA : IsUnit ((N * d : ℕ) : A)) (hNR : IsUnit ((N * d : ℕ) : R0)) {ζ : maxUnram A K}
    (hζ : IsPrimitiveRoot ζ (N * d)) (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a))
    {J : Subgroup (Pi1 A K)} (hJ : J ≤ Q.inertia (Pi1 A K)) (k : ℕ)
    (hd : ∀ σ ∈ Q.inertia (Pi1 A K), σ ^ (p ^ k * d) ∈ J)
    (φ : Pi1 A K) (hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q) (q : ℕ) (hφζ : φ ζ = ζ ^ q)
    {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (χ : J → M) (hχc : IsLocallyConstant χ)
    (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) (σ : Pi1 A K) (hσ : σ ∈ J) (hσ' : φ * σ * φ⁻¹ ∈ J) :
    χ ⟨φ * σ * φ⁻¹, hσ'⟩ = q • χ ⟨σ, hσ⟩ := by
  obtain ⟨θ, τ₀, -, -, hθ1, hgen, htw⟩ :=
    exists_twist_char (p := p) hQ hNA hNR hζ hζI x hx ha hJ k hd φ hφ q hφζ
  rw [eq_val_nsmul_of_gen hM hθ1 hgen χ hχc hχ, eq_val_nsmul_of_gen hM hθ1 hgen χ hχc hχ ⟨σ, hσ⟩,
    htw σ hσ hσ', val_nsmul_nsmul hM]

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_TwNorm =====
section

/-!
# S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation

The twisted forms of `kchar_conj`, `norm_conj`, `normAll_conj` and `chi_eq_of_norm` (`Def_RP_Cone_ResTr`): if `x`
acts on `ζ_N` by `x ζ_N = ζ_N ^ w` (e.g. a Frobenius lift, `w = q`), then conjugating a normalised generator by `x`
gives a generator `w`-normalised at `x • Q` (`NormAllTw`), and a `w`-normalised generator has `w` times the
`χ`-value of a normalised one at the same prime (`chi_eq_of_normTw`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section ConjTw

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

/-- **Kummer characters under twisted conjugation**: if `α = γ β`, `γ ζ = ζ ^ w` and `(τ β / β) ^ N = 1`, then
`kchar α (γ τ γ⁻¹) = w * kchar β τ`. -/
theorem kchar_conj_tw (hζ : IsPrimitiveRoot ζ N) {J J' : Subgroup (E ≃ₐ[K] E)} {γ : E ≃ₐ[K] E} {w : ZMod N}
    (hγ : γ ζ = epow ζ w) {α β : Eˣ} (hβ : (α : E) = γ (β : E)) (τ : J)
    (hτ' : γ * (τ : E ≃ₐ[K] E) * γ⁻¹ ∈ J') (hpow : ((τ : E ≃ₐ[K] E) (β : E) / β) ^ N = 1) :
    kchar hζ (Γ := J') α ⟨γ * (τ : E ≃ₐ[K] E) * γ⁻¹, hτ'⟩ = w * kchar hζ (Γ := J) β τ := by
  have h1 : (γ * (τ : E ≃ₐ[K] E) * γ⁻¹) (α : E) / α = γ ((τ : E ≃ₐ[K] E) (β : E) / β) := by
    rw [map_div₀, hβ]
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e1 : (τ : E ≃ₐ[K] E) (β : E) / β = ζ ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val :=
    (epow_dlog hζ hpow).symm
  have h2 : γ ((τ : E ≃ₐ[K] E) (β : E) / β) = epow ζ (w * dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)) := by
    calc γ ((τ : E ≃ₐ[K] E) (β : E) / β)
        = γ (ζ ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val) := congrArg (fun z => γ z) e1
      _ = (γ ζ) ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val := map_pow _ _ _
      _ = epow ζ (w * dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)) := by rw [hγ, epow_pow hζ]
  show dlog hζ _ = w * dlog hζ _
  rw [h1, h2, dlog_epow]

end ConjTw

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- **Twisted (L4) at one level**: if `τ ∈ J` (fixing `L`) is normalised at `(L, Q)` and `x ζ_N = ζ_N ^ w`, then
`x τ x⁻¹ ∈ J'` is `w`-normalised at `(L, x • Q)`. -/
theorem norm_conj_tw {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    [hD : IsDedekindDomain (integralClosure R0 L)] [hF : IsFractionRing (integralClosure R0 L) L]
    {N : ℕ} [NeZero N] {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {J J' : Subgroup (Pi1 A K)} (τ : J) {x : Pi1 A K} {w : ZMod N} (hx : x ζN = epow ζN w)
    (hτ' : x * (τ : Pi1 A K) * x⁻¹ ∈ J')
    (hτL : ∀ y : L, (τ : Pi1 A K) (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y)
    (Q : Ideal (proChart A K R0))
    (hn : ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation L b) : ℤ) : ZMod N))
    (v' : HeightOneSpectrum (integralClosure R0 L)) (hv' : v'.asIdeal = (x • Q).comap (inclU R0 hLU))
    (α : (maxUnram A K)ˣ) (b : L) (hαb : (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b) :
    kchar hζN (Γ := J') α ⟨x * (τ : Pi1 A K) * x⁻¹, hτ'⟩ =
      w * ((WithZero.log (v'.valuation L b) : ℤ) : ZMod N) := by
  obtain ⟨σL, hσL⟩ := exists_restrict hLU x
  obtain ⟨v, hv, hval⟩ := exists_valuation_transport hLU hσL v' hv'
  have hxi : ∀ y : L, x (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (σL y) :=
    fun y => Subtype.ext (hσL y).symm
  let β : (maxUnram A K)ˣ := Units.map (x⁻¹ : Pi1 A K).toRingEquiv.toMonoidHom α
  have hβ' : (β : maxUnram A K) = (x⁻¹ : Pi1 A K) α := rfl
  have hβ : (α : maxUnram A K) = x (β : maxUnram A K) := by
    rw [hβ', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hb' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hLU (σL.symm b) := by
    have h := hxi (σL.symm b)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [hβ', ← map_pow, hαb, ← h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hpow : ((τ : Pi1 A K) (β : maxUnram A K) / β) ^ N = 1 := by
    rw [div_pow, ← map_pow, hb', hτL, div_self]
    rw [← hb']
    exact pow_ne_zero _ β.ne_zero
  rw [kchar_conj_tw hζN hx hβ τ hτ' hpow, hn v hv β (σL.symm b) hb', ← hval, AlgEquiv.apply_symm_apply]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `τ ∈ J` is `w`-normalised at `Q` at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k`. -/
abbrev NormAllTw (p e : ℕ) {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (M : IntermediateField F (AlgebraicClosure F))
    (Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) (J : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (τ : J) (k₀ : ℕ) (w : ZMod N) : Prop :=
  ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
      ↥(M ⊔ constLevel F p (e * k))]
    (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
    v.asIdeal = Q.comap (inclU (Places.Rinf Fq F) hLU) →
    ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
      (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
      kchar hζN (Γ := J) α τ = w * ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end S3

end

end Residue
end RamanujanPetersson


end

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

end Tau

end S3

end

end Residue
end RamanujanPetersson


end

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

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

end Tau

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx =====
section

/-!
# S4-PD umbrella: the perfect complex and the cone in the S3 chart

Items (1)-(3) are `Def_RP_Tsen`, `Def_RP_TameInertia`, `Def_RP_CdOne`; item (5) (the perfect `Λ[Γ]`-complex, mod `l^m`)
is `Def_RP_PerfectCx_RedPC` and its imports. This file closes item (4) in the S3 chart (`U = Spec Rfin`, boundary over `∞`):
* `h2Equiv_S3`: for `ρ = τ ∘ π` (`π` cut out by a finite unramified `M`), the cone's `H²` is `H²_c = V_Γ`, and the
  cone Frobenius of `φ⁻¹` (`φ` a Frobenius lift, true boundary permutation) is `q • ρ(φ⁻¹)` (`= V_Γ(-1)`).
* **`h2Equiv_lisse`**: the same for every lisse `ρ` (finite `V`, open kernel).
* `cone_h3_eq_zero`: the cone's `H³ = Π_s H²(Γ ⊓ I_s, -)` vanishes.
Explicit hypotheses: `PicDivU` (`cd_l ≤ 1`) and `PicDivX` (residue surjectivity), as in `CdOne` / `Cone_Exist`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh Kummer CP4a Residue
open scoped Pointwise Polynomial

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

/-- `trueTau_spec` solved for `P (t s)` (chart-generic, rule L3'). -/
theorem trueTau_smul {S : Type} (D : BdryData A K q R0 S) (ψ : Pi1 A K) (s : S) :
    D.P (trueTau D ψ s) = (ψ * (trueH D ψ s : Pi1 A K))⁻¹ • D.P s := by
  rw [mul_inv_rev, mul_smul, trueTau_spec D ψ s, inv_smul_smul]

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- A geometric element times a Frobenius lift is a Frobenius lift. -/
theorem isFrobLift_geo_mul {g φ : Pi1 (Places.Rfin Fq F) F}
    (hg : g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))
    (hφ : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ) :
    IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) (g * φ) := by
  intro x hx
  rw [AlgEquiv.mul_apply, hφ x hx]
  obtain ⟨n, hn, hxn⟩ := hx
  exact (mem_pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) g).1 hg _
    ⟨n, hn, by rw [← pow_mul, mul_comm (Fintype.card Fq), pow_mul, hxn]⟩

end S3

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysD =====
section

/-!
# S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`

Route G (session 44). `Γ_L` (`fixLev`) fixes the constants of level `L`; these sets are closed, directed, and
`⋂ Γ_L = π₁^geo`, so by compactness some `Γ_L` lies in the open set `π₁^geo · N` (`exists_fixLev_sub`). Any `ψ`
acts on `𝔽_{q^L} ⊆ K_U` as a power `x ↦ x^{q^j}` (`exists_pow_lev`, CP4a's `exists_frob_pow_of_finite`), as does `φ^j`
for a Frobenius lift `φ`; hence `(φ^j)⁻¹ ψ ∈ Γ_L` and `ψ = φ^j γ n` (`exists_frobPow_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open Places PicDescent CurveCoh Kummer GalCover CP4a
open scoped Pointwise Polynomial

noncomputable section

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- `Γ_L`: the automorphisms fixing the constants of level `L`. -/
def fixLev (q L : ℕ) : Set (Pi1 A K) := {σ | ∀ x : maxUnram A K, x ^ q ^ L = x → σ x = x}

theorem isClosed_fixLev (q L : ℕ) : IsClosed (fixLev (A := A) (K := K) q L) := by
  have hs : fixLev (A := A) (K := K) q L =
      ⋂ (x : maxUnram A K) (_ : x ^ q ^ L = x), {σ : Pi1 A K | σ x = x} := by
    ext σ
    simp only [fixLev, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hs]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_setOf_apply_eq x x

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

end S3

end

end CupDuality
end RamanujanPetersson


end


