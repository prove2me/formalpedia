-- Prove2me | Definitions.Def_RPLib_FX_GOSC_03
-- name    : RPLib_FX_GOSC_03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:46:07.063664+00:00
-- url     : https://prove2.me/theorems/b405b6c9-4d3a-5406-adab-c41d7d28ca94
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 03 of 14
-- statement:
--   File 03 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
--   * `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
--   * `S4.Def_RP_GOS_B_Deg`: S4-GOS-B, part Deg: the fundamental identity in degree form
--   * `S4.Def_RP_GOS_B_FF`: S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`
--   * `S4.Def_RP_GOS_B_Gal`: S4-GOS-B, part Gal: the charts of a Galois extension of function fields
--   * `S4.Def_RP_GOS_B_Hil`: S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension
--   * `S4.Def_RP_GOS_B_Tow`: S4-GOS-B, part Tow: the global character `Φ` and the tower identity
--   * `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
--   * `S4.Def_RP_GOS_B_Scl`: S4-GOS-B, part Scl: Riemann-Roch data over a larger constant field (O6d, constant-field glue)
--   * `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
--   * `S4.Def_RP_GOS_C_SWS`: S4-GOS-C, part SWS: the Swan conductors at conjugate places agree
--   * `S4.Def_RP_GOS_C_RAT`: S4-GOS-C, part RAT: the projective line `𝔽_q(x)`
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib
import Definitions.Def_RPLib_F2_002
import Definitions.Def_RPLib_FX_GOSC_02

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 03 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
* `S4.Def_RP_Lefschetz_PtCov`: S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points
* `S4.Def_RP_GOS_B_Deg`: S4-GOS-B, part Deg: the fundamental identity in degree form
* `S4.Def_RP_GOS_B_FF`: S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`
* `S4.Def_RP_GOS_B_Gal`: S4-GOS-B, part Gal: the charts of a Galois extension of function fields
* `S4.Def_RP_GOS_B_Hil`: S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension
* `S4.Def_RP_GOS_B_Tow`: S4-GOS-B, part Tow: the global character `Φ` and the tower identity
* `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
* `S4.Def_RP_GOS_B_Scl`: S4-GOS-B, part Scl: Riemann-Roch data over a larger constant field (O6d, constant-field glue)
* `S4.Def_RP_GOS_B_PlKc`: S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)
* `S4.Def_RP_GOS_C_SWS`: S4-GOS-C, part SWS: the Swan conductors at conjugate places agree
* `S4.Def_RP_GOS_C_RAT`: S4-GOS-C, part RAT: the projective line `𝔽_q(x)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_PtPro =====
section

/-!
# S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)

* `finite_setOf_pow_eq`, `finite_quot_ker`: points with values in a finite set have finite residue rings.
* `resPt`, `jPt`: restriction `π₁(U) → Gal(L/K)` and the inclusion `O_L → O_{K_U}` (the pro-chart over `A`) for a
  finite unramified Galois level `L`, with `resPt_surjective`, `jPt_smul`.
* `exists_frob_pro`: for a point `w` of the pro-chart with `Fr ∘ w = w` on `A` (finite image), some `F ∈ π₁(U)` has
  `w ∘ F = Fr ∘ w` (finite levels by `hom_smul_trans`, then compactness of `π₁(U)`).
* `IsFrobPt Fr u F` and `exists_isFrobPt`: every point `u` of `A` has a Frobenius element.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtProGen

end PtProGen

section PtPro

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

theorem faithfulSMul_proChart : FaithfulSMul A (proChart A K A) := by
  refine (faithfulSMul_iff_algebraMap_injective A _).2 fun x y hxy => ?_
  have h1 : algebraMap A (maxUnram A K) x = algebraMap A (maxUnram A K) y := congrArg Subtype.val hxy
  rw [IsScalarTower.algebraMap_apply A K (maxUnram A K), IsScalarTower.algebraMap_apply A K (maxUnram A K) y] at h1
  exact IsFractionRing.injective A K ((algebraMap K (maxUnram A K)).injective h1)

end PtPro

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtCov =====
section

/-!
# S4-Lefschetz, L5c3: one finite level for all blocks, normalized Frobenius elements at points

* `exists_unramSet_fix`: a finite unramified Galois level `L` containing a finite set of `K_U`, whose fixer in
  `π₁(U)` lies in a given open subgroup; `fix_of_resPt_eq_one`, `pi_eq_of_resPt_eq`, `piBar` (`π` through
  `Gal(L/K)`), `piBar_resPt`.
* `isConj_of_isFrobPt`: two Frobenius elements at the same point are conjugate modulo an open normal subgroup.
* `kStar hq n`: the constants `x ∈ K_U` with `x ^ (q ^ n) = x` (a finite field with an `Fq`-algebra structure),
  `incStar` into the pro-chart.
* `exists_normFrob`: at every point `u` (with `Fr ∘ u = u`, finite image) there are a point `w` of the pro-chart over
  `u` and a Frobenius element `F` (`w ∘ F = Fr ∘ w`) with `w = ιS` on `kStar` (normalization by `φ ^ j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section PtCovLevel

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

variable {A K}

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end PtCovLevel

section KStar

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable {k0 : Type} [Field k0] [Fintype k0] [Algebra k0 K] {p e : ℕ} [Fact p.Prime] [CharP K p]

theorem smul_algebraMap_proChart (σ : Pi1 A K) (a : A) :
    σ • algebraMap A (proChart A K A) a = algebraMap A (proChart A K A) a := by
  refine Subtype.ext ?_
  show σ (algebraMap A (maxUnram A K) a) = algebraMap A (maxUnram A K) a
  rw [IsScalarTower.algebraMap_apply A K (maxUnram A K), AlgEquiv.commutes]

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end KStar

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_B_Deg =====
section

/-!
# S4-GOS-B, part Deg: the fundamental identity in degree form

For `A → B` as in `Def_RP_GOS_B_Loc` with compatible `Fq`-algebra structures and `P : HOS A`:
`Σ_{Q | P} e_Q deg Q = [L : K] deg P` (`deg` = `Places.deg Fq`, `e_Q = ramificationIdx'`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace RamanujanPetersson.GOS

section Deg

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (A : Type*) {K L : Type*} {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable [Module.Finite A B] [Algebra.IsIntegral A B]
variable [Algebra Fq A] [Algebra Fq B] [IsScalarTower Fq A B]

include K L in
set_option linter.deprecated false in
theorem sum_under_eq_deg (P : HeightOneSpectrum A) :
    ∑ Q ∈ (finite_under_eq A (B := B) P).toFinset,
      ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) * (Places.deg Fq Q : ℤ) =
    (Module.finrank K L : ℤ) * Places.deg Fq P := by
  classical
  have := P.isMaximal
  have hsum := Ideal.sum_ramification_inertia B K L P.ne_bot
  have himg : (finite_under_eq A (B := B) P).toFinset.image (fun Q => Q.asIdeal) =
      IsDedekindDomain.primesOverFinset P.asIdeal B := by
    ext I
    rw [Finset.mem_image, IsDedekindDomain.mem_primesOverFinset_iff P.ne_bot]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      have hu : Q ∈ {Q : HeightOneSpectrum B | Q.under A = P} := (Set.Finite.mem_toFinset _).1 hQ
      exact ⟨Q.isPrime, (liesOver_iff_under_eq A P Q).2 hu⟩
    · rintro ⟨hI, hIP⟩
      have hI0 : I ≠ ⊥ := by
        rintro rfl
        apply P.ne_bot
        rw [hIP.over]
        exact Ideal.comap_bot_of_injective _ (algebraMap_injective' A (K := K) (L := L))
      refine ⟨⟨I, hI, hI0⟩, (Set.Finite.mem_toFinset _).2 ?_, rfl⟩
      exact (liesOver_iff_under_eq A P ⟨I, hI, hI0⟩).1 hIP
  rw [← himg, Finset.sum_image (fun Q _ Q' _ h => HeightOneSpectrum.ext h)] at hsum
  calc ∑ Q ∈ (finite_under_eq A (B := B) P).toFinset,
        ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) * (Places.deg Fq Q : ℤ)
      = ∑ Q ∈ (finite_under_eq A (B := B) P).toFinset,
        (Places.deg Fq P : ℤ) * ((P.asIdeal.ramificationIdx' Q.asIdeal *
          Ideal.inertiaDeg' P.asIdeal Q.asIdeal : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun Q hQ => ?_
        have hu : Q ∈ {Q : HeightOneSpectrum B | Q.under A = P} := (Set.Finite.mem_toFinset _).1 hQ
        replace hu : Q.under A = P := hu
        rw [deg_eq_mul_inertiaDeg Fq A P Q hu, hu]
        push_cast; ring
    _ = (Module.finrank K L : ℤ) * Places.deg Fq P := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, hsum, mul_comm]

end Deg

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_FF =====
section

/-!
# S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`

For function fields `K → L` over `Fq` (both with the `Fq[X] ⊆ RatFunc Fq` package, compatible towers):
the chart instances (`Rfin`, `Rinf`), the cotrace `ffCotrace`, the different divisor `diffDiv` and
**`riemannHurwitz`**: `2 g_L - 2 ℓ_L(0) = [L:K] (2 g_K - 2 ℓ_K(0)) + deg Diff(L/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.RR
open RamanujanPetersson.CupDuality

section FF

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]

instance finite_rfin_ff : Module.Finite (Rfin Fq K) (Rfin Fq L) :=
  Module.Finite.of_restrictScalars_finite Fq[X] (Rfin Fq K) (Rfin Fq L)

instance finite_rinf_ff : Module.Finite (Rinf Fq K) (Rinf Fq L) :=
  Module.Finite.of_restrictScalars_finite (Oinf Fq) (Rinf Fq K) (Rinf Fq L)

instance isScalarTower_poly_rfin_ff : IsScalarTower Fq[X] (Rfin Fq K) L :=
  IsScalarTower.of_algebraMap_eq fun p => IsScalarTower.algebraMap_apply Fq[X] K L p

instance isScalarTower_oinf_rinf_ff : IsScalarTower (Oinf Fq) (Rinf Fq K) L :=
  IsScalarTower.of_algebraMap_eq fun p => IsScalarTower.algebraMap_apply (Oinf Fq) K L p

instance isIntegralClosure_rfin_ff : IsIntegralClosure (Rfin Fq L) (Rfin Fq K) L :=
  IsIntegralClosure.tower_top (R := Fq[X])

instance isIntegralClosure_rinf_ff : IsIntegralClosure (Rinf Fq L) (Rinf Fq K) L :=
  IsIntegralClosure.tower_top (R := Oinf Fq)

instance isScalarTower_Fq_rfin_ff : IsScalarTower Fq (Rfin Fq K) (Rfin Fq L) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply Fq K L c)

instance isScalarTower_Fq_rinf_ff : IsScalarTower Fq (Rinf Fq K) (Rinf Fq L) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply Fq K L c)

/-- The cotrace data of `L / K` on the two charts `Rfin`, `Rinf`. -/
def ffCotrace : Cotrace (ffData Fq K) (ffData Fq L) :=
  haveI := finiteDimensional_ff Fq K L
  haveI := isSeparable_ff Fq K L
  Cotrace.ofCharts (A1 := Rfin Fq K) (B1 := Rfin Fq L) (A2 := Rinf Fq K) (B2 := Rinf Fq L)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The different divisor of `L / K` (finite part from `Rfin`, infinite part from `Rinf`). -/
def diffDiv : Divisor Fq L :=
  (ordDiv (differentIdeal (Rfin Fq K) (Rfin Fq L))).sumElim (ordDiv (differentIdeal (Rinf Fq K) (Rinf Fq L)))

theorem ffCotrace_d : (ffCotrace Fq K L).d = diffDiv Fq K L := rfl

theorem ffCotrace_pr_inl (Q : HeightOneSpectrum (Rfin Fq L)) :
    (ffCotrace Fq K L).pr (Sum.inl Q) = Sum.inl (Q.under (Rfin Fq K)) := rfl

theorem ffCotrace_pr_inr (Q : HeightOneSpectrum (Rinf Fq L)) :
    (ffCotrace Fq K L).pr (Sum.inr Q) = Sum.inr (Q.under (Rinf Fq K)) := rfl

theorem ffCotrace_e_inl (Q : HeightOneSpectrum (Rfin Fq L)) :
    (ffCotrace Fq K L).e (Sum.inl Q) = (Q.under (Rfin Fq K)).asIdeal.ramificationIdx' Q.asIdeal := rfl

theorem ffCotrace_e_inr (Q : HeightOneSpectrum (Rinf Fq L)) :
    (ffCotrace Fq K L).e (Sum.inr Q) = (Q.under (Rinf Fq K)).asIdeal.ramificationIdx' Q.asIdeal := rfl

theorem ffCotrace_hdeg (P : Place Fq K) :
    ∑ Q ∈ ((ffCotrace Fq K L).fib_finite P).toFinset, ((ffCotrace Fq K L).e Q : ℤ) * (ffData Fq L).deg Q =
      (Module.finrank K L : ℤ) * (ffData Fq K).deg P := by
  classical
  rcases P with P | P
  · have hset : ((ffCotrace Fq K L).fib_finite (Sum.inl P)).toFinset =
        (finite_under_eq (Rfin Fq K) (B := Rfin Fq L) P).toFinset.map ⟨Sum.inl, Sum.inl_injective⟩ := by
      ext Q
      rw [Set.Finite.mem_toFinset, Finset.mem_map, Set.mem_setOf_eq]
      rcases Q with Q | Q
      · rw [ffCotrace_pr_inl]
        constructor
        · intro h
          exact ⟨Q, (Set.Finite.mem_toFinset _).2 (Sum.inl.inj h), rfl⟩
        · rintro ⟨Q', hQ', hQQ'⟩
          simp only [Function.Embedding.coeFn_mk, Sum.inl.injEq] at hQQ'
          subst hQQ'
          have h := (Set.Finite.mem_toFinset _).1 hQ'
          exact congrArg Sum.inl h
      · rw [ffCotrace_pr_inr]
        simp
    have := finiteDimensional_ff Fq K L
    have := isSeparable_ff Fq K L
    rw [hset, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, ffCotrace_e_inl, ffData_deg, Places.Place.deg_inl]
    exact sum_under_eq_deg Fq (Rfin Fq K) (K := K) (L := L) P
  · have hset : ((ffCotrace Fq K L).fib_finite (Sum.inr P)).toFinset =
        (finite_under_eq (Rinf Fq K) (B := Rinf Fq L) P).toFinset.map ⟨Sum.inr, Sum.inr_injective⟩ := by
      ext Q
      rw [Set.Finite.mem_toFinset, Finset.mem_map, Set.mem_setOf_eq]
      rcases Q with Q | Q
      · rw [ffCotrace_pr_inl]
        simp
      · rw [ffCotrace_pr_inr]
        constructor
        · intro h
          exact ⟨Q, (Set.Finite.mem_toFinset _).2 (Sum.inr.inj h), rfl⟩
        · rintro ⟨Q', hQ', hQQ'⟩
          simp only [Function.Embedding.coeFn_mk, Sum.inr.injEq] at hQQ'
          subst hQQ'
          have h := (Set.Finite.mem_toFinset _).1 hQ'
          exact congrArg Sum.inr h
    have := finiteDimensional_ff Fq K L
    have := isSeparable_ff Fq K L
    rw [hset, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, ffCotrace_e_inr, ffData_deg, Places.Place.deg_inr]
    exact sum_under_eq_deg Fq (Rinf Fq K) (K := K) (L := L) P

/-- **Riemann-Hurwitz** for an extension `L / K` of function fields over `Fq`:
`2 g_L - 2 ℓ_L(0) = [L:K] (2 g_K - 2 ℓ_K(0)) + deg Diff(L/K)`. -/
theorem riemannHurwitz :
    2 * (genusF Fq L : ℤ) - 2 * ellF Fq L 0 =
      (Module.finrank K L : ℤ) * (2 * (genusF Fq K : ℤ) - 2 * ellF Fq K 0) + (diffDiv Fq K L).deg := by
  rw [← ffData_degD, ← ffCotrace_d]
  exact (ffCotrace Fq K L).riemannHurwitz_data ffData_axioms ffData_axioms (ffCotrace_hdeg Fq K L)

end FF

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Gal =====
section

/-!
# S4-GOS-B, part Gal: the charts of a Galois extension of function fields

For function fields `K → L` over `Fq` and a finite group `G` with `IsGaloisGroup G K L`: the action of `G` on
the charts `Rfin Fq L`, `Rinf Fq L`, and `IsGaloisGroup G (Rfin Fq K) (Rfin Fq L)`, `IsGaloisGroup G (Rinf Fq K) (Rinf Fq L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.CupDuality

section Gal

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

include K in
theorem smulCommClass_oinf_gal : SMulCommClass G (Oinf Fq) L :=
  ⟨fun g p x => by
    rw [← algebraMap_smul K p x, ← algebraMap_smul K p (g • x), smul_comm]⟩

/-- The action of `G` on the finite chart of `L`. -/
@[instance_reducible] def actRfin : MulSemiringAction G (Rfin Fq L) :=
  haveI := smulCommClass_poly_gal Fq K L G
  inferInstanceAs (MulSemiringAction G (integralClosure Fq[X] L))

/-- The action of `G` on the infinite chart of `L`. -/
@[instance_reducible] def actRinf : MulSemiringAction G (Rinf Fq L) :=
  haveI := smulCommClass_oinf_gal Fq K L G
  inferInstanceAs (MulSemiringAction G (integralClosure (Oinf Fq) L))

theorem actRfin_smul (g : G) (x : Rfin Fq L) :
    letI := actRfin Fq K L G
    ((g • x : Rfin Fq L) : L) = g • (x : L) := rfl

theorem actRinf_smul (g : G) (x : Rinf Fq L) :
    letI := actRinf Fq K L G
    ((g • x : Rinf Fq L) : L) = g • (x : L) := rfl

theorem smulDistribClass_rfin :
    letI := actRfin Fq K L G
    SMulDistribClass G (Rfin Fq L) L :=
  letI := actRfin Fq K L G
  ⟨fun g b x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    rfl⟩

theorem smulDistribClass_rinf :
    letI := actRinf Fq K L G
    SMulDistribClass G (Rinf Fq L) L :=
  letI := actRinf Fq K L G
  ⟨fun g b x => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    rfl⟩

theorem isGaloisGroup_rfin :
    letI := actRfin Fq K L G
    IsGaloisGroup G (Rfin Fq K) (Rfin Fq L) :=
  letI := actRfin Fq K L G
  haveI := smulDistribClass_rfin Fq K L G
  IsGaloisGroup.of_isFractionRing G (Rfin Fq K) (Rfin Fq L) K L

theorem isGaloisGroup_rinf :
    letI := actRinf Fq K L G
    IsGaloisGroup G (Rinf Fq K) (Rinf Fq L) :=
  letI := actRinf Fq K L G
  haveI := smulDistribClass_rinf Fq K L G
  IsGaloisGroup.of_isFractionRing G (Rinf Fq K) (Rinf Fq L) K L

end Gal

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Hil =====
section

/-!
# S4-GOS-B, part Hil: Hilbert's formula and `e = |I|` on the charts of a Galois extension

For `IsGaloisGroup G K L` (function fields over `Fq`): the ramification function `iQ`, Hilbert's formula for the
different of `Rinf Fq K → Rinf Fq L`, its vanishing on `Rfin` when the finite inertia groups are trivial,
`deg Diff(L/K) = Σ_{Q | ∞} d_Q deg Q`, and `Σ_{Q | R} |I_Q| deg Q = |G| deg R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.CupDuality

section Ram

variable (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L]

end Ram

section Hil

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

instance finite_rinf_places : Finite (HeightOneSpectrum (Rinf Fq L)) :=
  Set.finite_univ_iff.mp ((ZetaSB.finite_infPlaces (Fq := Fq) (F := L)).subset fun P _ =>
    (Set.Finite.mem_toFinset _).1 (ZetaSB.mem_infPlaces (Fq := Fq) (F := L) P))

instance fintype_rinf_places : Fintype (HeightOneSpectrum (Rinf Fq L)) := Fintype.ofFinite _

end Hil

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Tow =====
section

/-!
# S4-GOS-B, part Tow: the global character `Φ` and the tower identity

For `IsGaloisGroup G K L` (function fields over `Fq`, all finite places of `L` unramified over `K`):
`χ_c(F) = 2 ℓ_F(0) - 2 g_F - Σ_{R | ∞} deg R` (`chiC`), the global character
`Φ(1) = χ_c(L)`, `Φ(σ) = Σ_{Q | ∞, σ ∈ I_Q} deg Q (i_Q(σ) - 1)` (`Phi`), and the identity
**`Σ_{σ ∈ G} Φ(σ) = |G| χ_c(K)`** (`sum_Phi_eq`), from Riemann-Hurwitz and Hilbert's different formula.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)
open RamanujanPetersson.RR

section Chi

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `χ_c` of the affine curve `Spec (Rfin Fq F)`: `2 ℓ(0) - 2 g - Σ_{R | ∞} deg R`. -/
def chiC : ℤ :=
  2 * (ellF Fq F 0 : ℤ) - 2 * (genusF Fq F : ℤ) - ∑ R : HeightOneSpectrum (Rinf Fq F), (Places.deg Fq R : ℤ)

end Chi

section Tow

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

theorem card_filter_erase_inertia (Q : HeightOneSpectrum (Rinf Fq L)) :
    letI := actRinf Fq K L G
    ((((Finset.univ.erase (1 : G)).filter (· ∈ Q.asIdeal.inertia G)).card : ℕ) : ℤ) =
      (Nat.card (Q.asIdeal.inertia G) : ℤ) - 1 := by
  letI := actRinf Fq K L G
  have h1 : (1 : G) ∈ Finset.univ.filter (· ∈ Q.asIdeal.inertia G) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, one_mem _⟩
  have hc : Nat.card (Q.asIdeal.inertia G) = (Finset.univ.filter (· ∈ Q.asIdeal.inertia G)).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)
  rw [Finset.filter_erase, Finset.card_erase_of_mem h1, hc, Nat.cast_sub (Finset.card_pos.2 ⟨1, h1⟩), Nat.cast_one]

end Tow

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_TowH =====
section

/-!
# S4-GOS-B, part TowH: the tower identity for a subgroup

For `IsGaloisGroup G Fq(X) L` and `H ≤ G`, with `L^H = fixF Fq L G H`:
**`Σ_{h ∈ H} Φ(h) = |H| χ_c(L^H)`** (`sum_Phi_subgroup`), where `Φ = Phi Fq (RatFunc Fq) L G` is the global
character of `G` (`Phi_subgroup`: the character of `H` on `L / L^H` is its restriction).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section TowH

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]

instance isScalarTower_Fq_intF (E : IntermediateField (RatFunc Fq) L) : IsScalarTower Fq E L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_Fq_poly_intF (E : IntermediateField (RatFunc Fq) L) : IsScalarTower Fq Fq[X] E :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply Fq Fq[X] L c)

variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G (RatFunc Fq) L]
variable (H : Subgroup G)

theorem inertia_subgroup_iff (h : H) (Q : HeightOneSpectrum (Rinf Fq L)) :
    (letI := actRinf Fq (fixF Fq L G H) L H; h ∈ Q.asIdeal.inertia H) ↔
      (letI := actRinf Fq (RatFunc Fq) L G; (h : G) ∈ Q.asIdeal.inertia G) :=
  Iff.rfl

theorem hfin_subgroup (hfin : letI := actRfin Fq (RatFunc Fq) L G;
      ∀ Q : HeightOneSpectrum (Rfin Fq L), Q.asIdeal.inertia G = ⊥) :
    letI := actRfin Fq (fixF Fq L G H) L H
    ∀ Q : HeightOneSpectrum (Rfin Fq L), Q.asIdeal.inertia H = ⊥ := by
  letI := actRfin Fq (fixF Fq L G H) L H
  intro Q
  refine (Subgroup.eq_bot_iff_forall _).2 fun h hh => Subtype.ext ?_
  have hG : (h : G) ∈ (letI := actRfin Fq (RatFunc Fq) L G; Q.asIdeal.inertia G) := hh
  rw [hfin Q] at hG
  exact Subgroup.mem_bot.1 hG

end TowH

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Scl =====
section

/-!
# S4-GOS-B, part Scl: Riemann-Roch data over a larger constant field (O6d, constant-field glue)

Two Riemann-Roch data `d1 : Data Fq F ι1`, `d2 : Data k F ι2` for a tower `Fq ⊆ k ⊆ F`, with a bijection
`e : ι2 ≃ ι1` of the places, equal valuations and `deg₁ (e i) = n deg₂ i`, `n = [k : Fq]`:

* `LD_scl`, `ell_scl`: `L₁(D) = L₂(D ∘ e)` and `ℓ₁(D) = [k : Fq] ℓ₂(D ∘ e)`;
* `degD_scl`: `deg₁ D = n deg₂ (D ∘ e)`;
* `gamma_scl`, **`genus_scl`**: `γ₁ = n γ₂` and `g₁ = n g₂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.GOS

open RR

section Scl

variable {Fq k F ι1 ι2 : Type*} [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Field F] [Algebra Fq k]
  [Algebra k F] [Algebra Fq F] [IsScalarTower Fq k F] (d1 : Data Fq F ι1) (d2 : Data k F ι2) (e : ι2 ≃ ι1)
  (hv : ∀ i, d1.v (e i) = d2.v i)

include hv in
theorem LD_scl (D : ι1 →₀ ℤ) (f : F) : f ∈ d1.LD D ↔ f ∈ d2.LD (D.equivMapDomain e.symm) := by
  rw [Data.mem_LD, Data.mem_LD]
  constructor
  · intro h i
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, ← hv]
    exact h (e i)
  · intro h j
    have := h (e.symm j)
    rwa [Finsupp.equivMapDomain_apply, Equiv.symm_symm, ← hv, Equiv.apply_symm_apply] at this

include hv in
theorem ell_scl (D : ι1 →₀ ℤ) :
    d1.ell D = Module.finrank Fq k * d2.ell (D.equivMapDomain e.symm) := by
  have hsub : (d2.LD (D.equivMapDomain e.symm)).restrictScalars Fq = d1.LD D := by
    ext f
    rw [Submodule.restrictScalars_mem]
    exact (LD_scl d1 d2 e hv D f).symm
  rw [Data.ell, Data.ell, ← hsub, Module.finrank_mul_finrank Fq k]
  exact ((Submodule.restrictScalarsEquiv Fq k F (d2.LD (D.equivMapDomain e.symm))).restrictScalars Fq).finrank_eq

variable (n : ℕ) (hdeg : ∀ i, d1.deg (e i) = n * d2.deg i)

include hdeg in
theorem degD_scl (D : ι1 →₀ ℤ) : d1.degD D = n * d2.degD (D.equivMapDomain e.symm) := by
  unfold Data.degD
  rw [Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [← Equiv.apply_symm_apply e j, hdeg, Equiv.symm_apply_apply]
  push_cast
  ring

include hv hdeg in
theorem gamma_scl (hd1 : d1.Axioms) (hd2 : d2.Axioms) (hn : Module.finrank Fq k = n) :
    d1.gamma = n * d2.gamma := by
  have key : ∀ D : ι1 →₀ ℤ, d1.degD D - d1.ell D =
      n * (d2.degD (D.equivMapDomain e.symm) - d2.ell (D.equivMapDomain e.symm)) := by
    intro D
    rw [degD_scl d1 d2 e n hdeg, ell_scl d1 d2 e hv, hn]
    push_cast
    ring
  apply le_antisymm
  · obtain ⟨D0, h0⟩ := Data.exists_gamma hd1
    rw [← h0, key]
    exact mul_le_mul_of_nonneg_left (Data.defect_le_gamma hd2 _) (by positivity)
  · obtain ⟨D0, h0⟩ := Data.exists_gamma hd2
    have h := Data.defect_le_gamma hd1 (D0.equivMapDomain e)
    have hD : (D0.equivMapDomain e).equivMapDomain e.symm = D0 := by
      ext i
      simp [Finsupp.equivMapDomain_apply]
    rw [key, hD, h0] at h
    exact h

include hv hdeg in
/-- **Genus over a larger constant field**: `g₁ = [k : Fq] g₂`. -/
theorem genus_scl (hd1 : d1.Axioms) (hd2 : d2.Axioms) (hn : Module.finrank Fq k = n) :
    d1.genus = n * d2.genus := by
  have h1 := Data.genus_eq hd1
  have h2 := Data.genus_eq hd2
  have h0 := ell_scl d1 d2 e hv 0
  rw [Finsupp.equivMapDomain_zero, hn] at h0
  have hg := gamma_scl d1 d2 e hv n hdeg hd1 hd2 hn
  have : (d1.genus : ℤ) = n * d2.genus := by
    rw [h1, h2, h0, hg]
    push_cast
    ring
  exact_mod_cast this

end Scl

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_PlKc =====
section

/-!
# S4-GOS-B, part PlKc: a function field over `𝔽_q` and over its full constant field `k_E` (O6d glue)

`d := [k_E : 𝔽_q]`.
* `plKc`: places over `k_E` ≃ places over `𝔽_q` (`R_fin`, `R_∞` do not see the constant field);
  `ffv_plKc` (same valuations), `deg_plKc` (`deg_{𝔽_q} = d · deg_{k_E}`);
* **`genusF_Kc`**: `g(E/𝔽_q) = d · g(E/k_E)`;
* **`numPoints_Kc`**: `N_m(E/𝔽_q) = [d ∣ m] d N_{m/d}(E/k_E)` (as `dil d`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places Lefschetz RR

/-- Degrees under a ring isomorphism of the coordinate rings of two bases `Fq ⊆ k`. -/
theorem deg_equivOfRingEquiv {Fq k S1 S2 : Type} [Field Fq] [Fintype Fq] [Field k] [Fintype k] [Algebra Fq k]
    [CommRing S1] [CommRing S2] [Algebra Fq S1] [Algebra k S2] (e : S2 ≃+* S1) (P : HeightOneSpectrum S2)
    [Finite (S1 ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal)] [Finite (S2 ⧸ P.asIdeal)] :
    deg Fq (HeightOneSpectrum.equivOfRingEquiv e P) = Module.finrank Fq k * deg k P := by
  classical
  let _ : Fintype (S1 ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal) := Fintype.ofFinite _
  let _ : Fintype (S2 ⧸ P.asIdeal) := Fintype.ofFinite _
  have hI : (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = P.asIdeal.map (e : S2 →+* S1) :=
    Ideal.comap_symm e
  have hiso : S2 ⧸ P.asIdeal ≃+* S1 ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal :=
    Ideal.quotientEquiv _ _ e hI
  have h1 := Module.card_eq_pow_finrank (K := Fq) (V := S1 ⧸ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal)
  have h2 := Module.card_eq_pow_finrank (K := k) (V := S2 ⧸ P.asIdeal)
  have h3 := Module.card_eq_pow_finrank (K := Fq) (V := k)
  rw [← Fintype.card_congr hiso.toEquiv, h2, h3, ← pow_mul] at h1
  exact (Nat.pow_right_injective (Fintype.one_lt_card (α := Fq)) h1).symm

section PlKc

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

end PlKc

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_C_SWS =====
section

/-!
# S4-GOS-C, part SWS: the Swan conductors at conjugate places agree

`swanQ_conj`: `Sw_{σ Q} = Sw_Q` (S4-Swan's `swan_inertia_conj`); `exists_smul_eq_rinf`: places of `L` over the same
place of `K` are conjugate; **`sum_swanQ_of_conj`**: if all places over `∞` are conjugate to `Q₀`, then
`Σ_Q deg Q |I_Q| Sw_Q = Sw_{Q₀} Σ_Q deg Q |I_Q|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical Module
open scoped Pointwise

namespace RamanujanPetersson.GOS

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf)

section SWS

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M] {Gf : Type*} [Group Gf] [Fintype Gf]
  (ι : G →* Gf) (τ : Representation k Gf M)

theorem exists_smul_eq_rinf (Q Q' : HeightOneSpectrum (Rinf Fq L))
    (h : Q.asIdeal.under (Rinf Fq K) = Q'.asIdeal.under (Rinf Fq K)) :
    letI := actRinf Fq K L G
    ∃ σ : G, σ • Q.asIdeal = Q'.asIdeal := by
  letI := actRinf Fq K L G
  haveI := isGaloisGroup_rinf Fq K L G
  have : Algebra.IsInvariant (Rinf Fq K) (Rinf Fq L) G := IsGaloisGroup.isInvariant
  have : SMulCommClass G (Rinf Fq K) (Rinf Fq L) := IsGaloisGroup.commutes
  have : Algebra.IsIntegral (Rinf Fq K) (Rinf Fq L) :=
    Algebra.IsInvariant.isIntegral (Rinf Fq K) (Rinf Fq L) G
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := Rinf Fq K) (B := Rinf Fq L) (G := G)
    Q.asIdeal Q'.asIdeal h
  exact ⟨σ, hσ.symm⟩

end SWS

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_C_RAT =====
section

/-!
# S4-GOS-C, part RAT: the projective line `𝔽_q(x)`

For `F = 𝔽_q(x)`: `Σ_{P | ∞} ord_P(1/x) deg P = 1` (`degS_rat`), so there is exactly one place over `∞`
(`Subsingleton`), of degree one (`deg_PinfR`); `ℓ(0) = 1` (`ellF_zero_rat`); polynomials of degree `≤ k` lie in
`L(k P_∞)` (`le_ellF_DkR`), so Riemann-Roch gives **`genus_rat : g = 0`** and **`chiC_rat : χ_c(𝔸¹) = 1`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

noncomputable section

open Places ZetaSB RR CP4a.Hyp2

section RAT

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]

theorem piInfR_rat :
    algebraMap (Rinf Fq (RatFunc Fq)) (RatFunc Fq) (piInfR Fq (RatFunc Fq)) = 1 / RatFunc.X := by
  rw [piInfR, ← IsScalarTower.algebraMap_apply]
  rfl

/-- `Σ_{P | ∞} ord_P(1/x) deg P = 1`. -/
theorem degS_rat : degS Fq (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)) = 1 := by
  have h := degS_inf Fq (RatFunc Fq) (piInfR_ne_zero (Fq := Fq) (F := RatFunc Fq))
  rw [piInfR_rat, Algebra.norm_self, MonoidHom.id_apply, one_div, RatFunc.intDegree_inv, RatFunc.intDegree_X, neg_neg,
    ← one_div] at h
  exact h

theorem one_le_ord_invX (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    1 ≤ Places.ord P (1 / RatFunc.X : RatFunc Fq) := by
  have h1 := one_le_ord_of_mem (K := RatFunc Fq) P (piInfR_ne_zero (Fq := Fq) (F := RatFunc Fq))
    (piInfR_mem P)
  rwa [piInfR_rat] at h1

theorem mem_support_invX (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    P ∈ (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)).support := by
  rw [Finsupp.mem_support_iff, divS_apply]
  have := one_le_ord_invX Fq P
  omega

theorem term_nonneg_rat (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    0 ≤ (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)) P * (Places.deg Fq P : ℤ) := by
  rw [divS_apply]
  have := one_le_ord_invX Fq P
  exact mul_nonneg (by omega) (Int.natCast_nonneg _)

theorem ord_deg_le_rat (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    Places.ord P (1 / RatFunc.X : RatFunc Fq) * (Places.deg Fq P : ℤ) ≤ 1 := by
  have h := degS_rat Fq
  rw [degS, Finsupp.sum] at h
  rw [← h]
  exact Finset.single_le_sum
    (f := fun Q => (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)) Q * (Places.deg Fq Q : ℤ))
    (fun Q _ => term_nonneg_rat Fq Q) (mem_support_invX Fq P)

/-- Every place of `𝔽_q(x)` over `∞` has `ord(1/x) = 1` and degree one. -/
theorem ord_deg_rat (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    Places.ord P (1 / RatFunc.X : RatFunc Fq) = 1 ∧ Places.deg Fq P = 1 := by
  have h1 := ord_deg_le_rat Fq P
  have h2 := one_le_ord_invX Fq P
  have h3 : (1 : ℤ) ≤ Places.deg Fq P := by exact_mod_cast Places.deg_pos Fq P
  have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℤ) ≤ Places.ord P (1 / RatFunc.X : RatFunc Fq) by omega)
  have h5 := mul_le_mul_of_nonneg_right h2 (show (0 : ℤ) ≤ Places.deg Fq P by omega)
  constructor
  · linarith
  · have : (Places.deg Fq P : ℤ) ≤ 1 := by linarith
    omega

/-- There is exactly one place of `𝔽_q(x)` over `∞`. -/
theorem infPlace_eq_rat (P P' : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) : P = P' := by
  classical
  by_contra hne
  have h := degS_rat Fq
  rw [degS, Finsupp.sum] at h
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun Q => (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)) Q * (Places.deg Fq Q : ℤ))
    (s := {P, P'}) (t := (divS (Rinf Fq (RatFunc Fq)) (1 / RatFunc.X : RatFunc Fq)).support)
    (fun Q _ => mem_support_invX Fq Q) (fun Q _ _ => term_nonneg_rat Fq Q)
  rw [Finset.sum_pair hne, h] at hle
  simp only [divS_apply] at hle
  rw [(ord_deg_rat Fq P).1, (ord_deg_rat Fq P).2, (ord_deg_rat Fq P').1, (ord_deg_rat Fq P').2] at hle
  norm_num at hle

instance subsingleton_infPlace_rat : Subsingleton (HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :=
  ⟨infPlace_eq_rat Fq⟩

/-- The place `∞` of `𝔽_q(x)`. -/
def PinfR : HeightOneSpectrum (Rinf Fq (RatFunc Fq)) := (nonempty_infPlace Fq (RatFunc Fq)).some

theorem deg_PinfR : Places.deg Fq (PinfR Fq) = 1 := (ord_deg_rat Fq _).2

theorem sum_deg_rat : ∑ R : HeightOneSpectrum (Rinf Fq (RatFunc Fq)), (Places.deg Fq R : ℤ) = 1 := by
  rw [Fintype.sum_subsingleton _ (PinfR Fq), deg_PinfR, Nat.cast_one]

theorem constField_rat : constField Fq (RatFunc Fq) = ⊥ :=
  constField_eq_bot_of_deg_one Fq (RatFunc Fq) (P := Sum.inr (PinfR Fq))
    (by rw [Place.deg_inr]; exact deg_PinfR Fq)

theorem ellF_zero_rat : ellF Fq (RatFunc Fq) 0 = 1 :=
  ellF_zero_of_deg_one (Fq := Fq) (F := RatFunc Fq) (P := Sum.inr (PinfR Fq))
    (by rw [Place.deg_inr]; exact deg_PinfR Fq)

theorem ord_X_rat (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) :
    Places.ord P (algebraMap Fq[X] (RatFunc Fq) X) = -1 := by
  have hX : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  have h1 : algebraMap Fq[X] (RatFunc Fq) X * (1 / RatFunc.X) = 1 := by
    rw [RatFunc.algebraMap_X, mul_one_div_cancel hX]
  have h2 := Places.ord_mul P (f := algebraMap Fq[X] (RatFunc Fq) X) (g := (1 / RatFunc.X : RatFunc Fq))
    (by rw [RatFunc.algebraMap_X]; exact hX) (one_div_ne_zero hX)
  rw [h1, ord_one', (ord_deg_rat Fq P).1] at h2
  omega

theorem ord_fin_poly_nonneg (Q : HeightOneSpectrum (Rfin Fq (RatFunc Fq))) (a : Fq[X]) :
    0 ≤ Places.ord Q (algebraMap Fq[X] (RatFunc Fq) a) := by
  have h := ord_alg_nonneg (K := RatFunc Fq) Q (algebraMap Fq[X] (Rfin Fq (RatFunc Fq)) a)
  rwa [← IsScalarTower.algebraMap_apply] at h

/-- `ord_∞ a ≥ -k` for `deg a ≤ k`. -/
theorem ord_inf_poly_ge (P : HeightOneSpectrum (Rinf Fq (RatFunc Fq))) (k : ℕ) {a : Fq[X]} (ha : a ≠ 0)
    (hk : a.natDegree ≤ k) : -(k : ℤ) ≤ Places.ord P (algebraMap Fq[X] (RatFunc Fq) a) := by
  have hinj := IsFractionRing.injective Fq[X] (RatFunc Fq)
  have hd : (X ^ k : Fq[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have ha' : algebraMap Fq[X] (RatFunc Fq) a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hd' : algebraMap Fq[X] (RatFunc Fq) (X ^ k) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd
  have hX' : algebraMap Fq[X] (RatFunc Fq) X ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hr : algebraMap Fq[X] (RatFunc Fq) a / algebraMap Fq[X] (RatFunc Fq) (X ^ k) ∈ Oinf Fq :=
    (mem_Oinf_iff' Fq (div_ne_zero ha' hd')).mpr (by
      rw [intDegree_div_polys Fq ha hd, natDegree_X_pow]; omega)
  have h1 := ord_alg_nonneg (K := RatFunc Fq) P (algebraMap (Oinf Fq) (Rinf Fq (RatFunc Fq)) ⟨_, hr⟩)
  rw [← IsScalarTower.algebraMap_apply] at h1
  change 0 ≤ Places.ord P (algebraMap Fq[X] (RatFunc Fq) a / algebraMap Fq[X] (RatFunc Fq) (X ^ k)) at h1
  rw [Places.ord_div P ha' hd', map_pow, ord_pow' P hX' k, ord_X_rat] at h1
  omega

/-- The divisor `k P_∞`. -/
abbrev DkR (k : ℕ) : Places.Divisor Fq (RatFunc Fq) := Finsupp.single (Sum.inr (PinfR Fq)) (k : ℤ)

/-- `deg a ≤ k ↦ a`, into `𝔽_q(x)`. -/
def polyLin (k : ℕ) : degreeLT Fq (k + 1) →ₗ[Fq] RatFunc Fq :=
  (IsScalarTower.toAlgHom Fq Fq[X] (RatFunc Fq)).toLinearMap ∘ₗ (degreeLT Fq (k + 1)).subtype

theorem polyLin_injective (k : ℕ) : Function.Injective (polyLin Fq k) :=
  (IsFractionRing.injective Fq[X] (RatFunc Fq)).comp Subtype.val_injective

end RAT

end

end RamanujanPetersson.GOS


end


