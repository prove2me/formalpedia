-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_05
-- name    : RPLib_FX_LisseDual_05
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:42:11.851131+00:00
-- url     : https://prove2.me/theorems/081b8c6e-2af3-4cc1-b6c9-52834e4b15b2
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 05 of 7
-- statement:
--   File 05 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
--   * `S4.Def_RP_LisseDuality_Asm`: S4-CurveDuality O7d-P3b T4: the duality map of `f_* Λ` is a unit times `V`'s pairing
--   * `S4.Def_RP_LisseDuality_AmbAsm`: S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness
--   * `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_F2_040
import Definitions.Def_RPLib_FX_LisseDual_04

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 05 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
* `S4.Def_RP_LisseDuality_Asm`: S4-CurveDuality O7d-P3b T4: the duality map of `f_* Λ` is a unit times `V`'s pairing
* `S4.Def_RP_LisseDuality_AmbAsm`: S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness
* `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
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

-- ===== S4.Def_RP_LisseDuality_Asm =====
section

/-!
# S4-CurveDuality O7d-P3b T4: the duality map of `f_* Λ` is a unit times `V`'s pairing

* `alphaM_eq_unit_mul` (T4a): `α(x, y) = c₀ · constPair_V (Sh_c x) (Sh₁ y)` with `c₀ ∈ Λˣ`
  (`alphaM_eq_sum_trP`, `sum_trP_eq_unit_mul` on the boundary cocycles `cupBd`, `constPairV_dual`);
* **`alphaM_push_bijective`** (T4): `hpush` (bijectivity of `α(f_* Λ)`) from bijectivity of `V`'s constant pairing.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Asm

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)
  {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G} {T : Type} [Fintype T]
  [Nonempty T] {J : T → Subgroup K} {πT : T → S} {xT : T → Γ} {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}
  {t : (s : S) → ↥(Γ ⊓ I s)}

include hK in
/-- **T4a**: `α(x, y) = c₀ · constPair_V (Sh_c x) (Sh₁ y)` with `c₀` a unit. -/
theorem alphaM_eq_unit_mul [Finite Λ] {l n : ℕ} (hall : H2All Λ G Γ l n)
    (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0)
    (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) (hv : H2Van σ Γ ⊤) (D : ConstData σ Γ I t)
    (hX : IsOpen ((pushRep K (Representation.trivial Λ K Λ)).ker : Set G))
    (hJ : InertiaLift Γ K I J πT xT) (hDC : DCover Γ K I πT xT)
    (HV : CupHyp (Representation.trivial Λ K Λ) (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ)
      (geoU Γ K))
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G)) :
    ∃ c₀ : Λ, IsUnit c₀ ∧ ∀ x y,
      alphaM hv (h2kEquiv D hσ).toLinearMap (pushRep K (Representation.trivial Λ K Λ)) hX x y =
        c₀ * constPair HV DV (shapiroH1c Γ K (Representation.trivial Λ K Λ) I J πT xT hJ x)
          (shapiroDual σ π K hK hs Γ R hcov hKo y) := by
  obtain ⟨c₀, hu, hc⟩ := sum_trP_eq_unit_mul σ π K hK hs hallI hΛ hπ hσ D hJ hDC DV R hcov hKo
  refine ⟨c₀, hu, fun x y => ?_⟩
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  haveI := coindV_finite σ π K hK hs
  have van : H2Van (pushRep K (σ.comp K.subtype)) Γ ⊤ :=
    h2Van_top_of_all hall (fun F => Subtype.ext (funext fun x => by simp [hΛ]))
      (isOpen_pushS σ π K hK hπ hσ)
  have H := mulHyp σ π K hK Γ hπ hσ van
  have hd1 : (psiP σ π K hK).compLeft Γ d.1 ∈ Z1 (pushRep K (σ.comp K.subtype)) Γ :=
    push_mem_Z1 Γ (psiP_equiv σ π K hK) d.2
  obtain ⟨U, hU⟩ := exists_prim H p.2.1 hd1
  refine (alphaM_eq_sum_trP σ π K hK hs D hσ hv hX p d U hU).trans ((hc fun s =>
    ⟨cupBd (mulP σ K) Γ I p.1 ((psiP σ π K hK).compLeft Γ d.1) U s, cupBd_mem H p.2 hd1 hU s⟩).trans
    (congrArg (c₀ * ·) (constPairV_dual σ π K hK hs Γ D.triv hJ HV DV R hcov hKo p d U hU
      (fun u => ⟨((gI K hJ t' u : ↥(Γ ⊓ I (πT u))) : G), (Subgroup.mem_inf.1 (gI K hJ t' u).2).1⟩)
      (fun u => rfl)).symm))

include hK hs in
/-- **T4**: `hpush` (bijectivity of `α(f_* Λ)`) from bijectivity of `V`'s constant pairing. -/
theorem alphaM_push_bijective [Finite Λ] {l n : ℕ} (hall : H2All Λ G Γ l n)
    (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0)
    (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) (hv : H2Van σ Γ ⊤) (D : ConstData σ Γ I t)
    (hX : IsOpen ((pushRep K (Representation.trivial Λ K Λ)).ker : Set G))
    (hJ : InertiaLift Γ K I J πT xT) (hDC : DCover Γ K I πT xT) (hDD : DDisj Γ K I πT xT)
    (HV : CupHyp (Representation.trivial Λ K Λ) (σ.comp K.subtype) (σ.comp K.subtype) (LinearMap.mul Λ Λ)
      (geoU Γ K))
    (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G))
    (hP : Function.Bijective (constPair HV DV)) :
    Function.Bijective (alphaM hv (h2kEquiv D hσ).toLinearMap (pushRep K (Representation.trivial Λ K Λ)) hX) := by
  obtain ⟨c₀, hu, h⟩ :=
    alphaM_eq_unit_mul σ π K hK hs hall hallI hΛ hπ hσ hv D hX hJ hDC HV DV R hcov hKo
  refine bijective_of_equiv_pair _ ((LinearEquiv.smulOfUnit hu.unit).toLinearMap ∘ₗ constPair HV DV)
    (shapiroH1cEquiv Γ K (Representation.trivial Λ K Λ) I J πT xT hJ hDC hDD R hcov hKo)
    (shapiroDual σ π K hK hs Γ R hcov hKo) (fun x y => (h x y).trans ?_)
    ((LinearEquiv.smulOfUnit hu.unit).bijective.comp hP)
  rfl

end Asm

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbAsm =====
section

/-!
# S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness

For `π : G →* Gf` onto a finite group with open kernel and residue data `RD : ResDat π Γ I N T`, the cover `V`
need not be connected over `Ū`: replace the ambient group `G` by `H₁ = π⁻¹(π Γ) = ker π · Γ` (`hOne`), which is
open of finite index, and `π` by `π₁ : H₁ ↠ π Γ` (`piOne`). Over `H₁` the cover is connected (`cov_hOne`), so the
connected chain (`alpha_bijective_of_regular` ← `alpha_coindF_of_push` ← `alphaM_push_bijective`) applies to the
data restricted to `H₁` (`h2All_subgroupOf`, `constData_tr'`, `inertiaLift_sub`, ...), and `alphaM_bijective_tr`
carries bijectivity back to `G`. The parabolic hypothesis `hB` is the same as in `lisse_bijective_connected`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Hone

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf : Type} [Group Gf]
  (π : G →* Gf) (Γ : Subgroup G)

end Hone

section Lisse

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf] (π : G →* Gf)
  {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {N : ℕ} {T : Type} [Fintype T]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

/-- **Lisse duality** (O7d-P1d): bijectivity of the duality map for every finite `τ ∘ π`, from `V`'s parabolic
perfectness; no connectedness or surjectivity of `π` is assumed (`[Nonempty T]`: see `rd_nonempty`). -/
theorem lisse_bijective [Nonempty T] [Finite Λ] [Module.Injective Λ Λ] {l n : ℕ} (hsep : SepDual Λ)
    (hall : H2All Λ G Γ l n) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l n) (hallK : H2All Λ G (Γ ⊓ π.ker) l n)
    (hΛ : ∀ a : Λ, (l ^ n) • a = 0) (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))
    (hv : H2Van σ Γ ⊤) (D : ConstData σ Γ I t)
    (RD : ResDat π Γ I N T) [NeZero N] (hN : (N : Λ) = 0)
    (hB : ParabolicPerfect (rdCupHyp π.ker σ hσ (h2Van_top_of_all hallK hΛ hσ))
      (rdConstData RD π.ker (fun _ => MonoidHom.mem_ker) σ D.triv hN))
    {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) :
    Function.Bijective (alphaM hv (h2kEquiv D hσ).toLinearMap (τ.comp π) (isOpen_comp π hπ τ)) := by
  have hK : ∀ g, g ∈ π.ker ↔ π g = 1 := fun _ => MonoidHom.mem_ker
  have hP := (constPair_isPerfPair_of_parabolic _ _ hB).1
  have hΓ : Γ ≤ hOne π Γ := le_hOne π Γ
  have hKH : π.ker ≤ hOne π Γ := ker_le_hOne π Γ
  have hHo : IsOpen (hOne π Γ : Set G) := isOpen_hOne π Γ hπ
  have : Finite (G ⧸ hOne π Γ) := finite_quot_hOne π Γ
  have hπ₁ := isOpen_ker_piOne π Γ hπ
  have hσ₁ : IsOpen ((σ.comp (hOne π Γ).subtype).ker : Set (hOne π Γ)) := isOpen_ker_comp (hOne π Γ) σ hσ
  have hall₁ := h2All_subgroupOf hHo hΓ hall
  have hallI₁ : ∀ s, H2All Λ (hOne π Γ) (Γ.subgroupOf (hOne π Γ) ⊓ (I s).subgroupOf (hOne π Γ)) l n :=
    fun s => by
      rw [← inf_subgroupOf']
      exact h2All_subgroupOf hHo (inf_le_left.trans hΓ) (hallI s)
  have hv₁ : H2Van (σ.comp (hOne π Γ).subtype) (Γ.subgroupOf (hOne π Γ)) ⊤ := h2van_comp (intw_sub σ hΓ) hv
  have hsI := (intw_sub σ hΓ).symm
  have hII := (intwI_sub I hΓ).symm
  let D₁ := constData_tr' hsI hII D
  -- the cover `V` at `G`, then over `H₁`
  have hvK := h2Van_top_of_all hallK hΛ hσ
  have HV := rdCupHyp π.ker σ hσ hvK
  let DV := rdConstData RD π.ker hK σ D.triv hN
  have hgeo := intw_geo σ Γ π.ker hKH
  have hgeoI := intwI_geo Γ π.ker hKH (rdJ RD π.ker)
  let DV₁ := constData_tr' hgeo.symm hgeoI.symm DV
  have HV₁ : CupHyp (Representation.trivial Λ (π.ker.subgroupOf (hOne π Γ)) Λ)
      ((σ.comp (hOne π Γ).subtype).comp (π.ker.subgroupOf (hOne π Γ)).subtype)
      ((σ.comp (hOne π Γ).subtype).comp (π.ker.subgroupOf (hOne π Γ)).subtype) (LinearMap.mul Λ Λ)
      (geoU (Γ.subgroupOf (hOne π Γ)) (π.ker.subgroupOf (hOne π Γ))) :=
    constCupHyp _ _ (isOpen_ker_comp _ _ hσ₁) (h2van_comp hgeo (h2Van_geoU π.ker σ hvK))
  have hP₁ : Function.Bijective (constPair HV₁ DV₁) :=
    constPair_bijective_tr HV₁ HV hgeo hgeoI (fun u => (infTr hgeoI u).apply_symm_apply _) DV₁ DV hP
  obtain ⟨R₁⟩ := exists_cosetReps (Γ.subgroupOf (hOne π Γ)) (π.ker.subgroupOf (hOne π Γ))
  have hb₁ := alpha_bijective_of_regular hv₁ (h2kEquiv D₁ hσ₁).toLinearMap (piOne π Γ) hπ₁ hall₁ hΛ hsep
    (alpha_coindF_of_push hv₁ _ (piOne π Γ) _ (mem_kOne_iff π Γ) (piOne_surjective π Γ) hπ₁
      (alphaM_push_bijective _ (piOne π Γ) _ (mem_kOne_iff π Γ) (piOne_surjective π Γ) hall₁ hallI₁ hΛ hπ₁
        hσ₁ hv₁ D₁ (isOpen_push (piOne π Γ) _ (mem_kOne_iff π Γ) hπ₁)
        (inertiaLift_sub hΓ hKH (inertiaLift_rd RD π.ker)) (dCover_sub hΓ hKH (dCover_rd RD π.ker hK))
        (dDisj_sub hΓ hKH (dDisj_rd RD π.ker hK)) HV₁ DV₁ R₁ (cov_hOne π Γ) (isOpen_kOne π Γ hπ) hP₁))
    (τ.comp (Γ.map π).subtype)
  have hτ : Intw (τ.comp π) ((τ.comp (Γ.map π).subtype).comp (piOne π Γ)) (eSub hΓ).symm := fun _ => rfl
  exact alphaM_bijective_tr hsI hII hv hv₁ (h2kEquiv D hσ).toLinearMap (h2kEquiv D₁ hσ₁).toLinearMap
    (fun z => h2kEquiv_tr hsI hII (fun _ => rfl) D D₁ hσ hσ₁ z) hτ (isOpen_comp π hπ τ) _ hb₁

end Lisse

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VS3b =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart

For an open subgroup `K` of `π₁(U)` (the cover `V`, `K = ker π`):
* `hbasis_S3`: open normal subgroups form a basis at `1` in `π₁(U)` (Krull topology);
* `hallV_S3`, `hallIV_S3`: `H²(Γ_V, -) = 0` and `H²(Γ_V ∩ I_V(t), -) = 0` at `V` (`h2All_closed` for the closed
  subgroups `Γ ∩ K` and `K ∩ x_t (Γ ∩ I_s) x_t⁻¹`, then `h2All_subgroupOf`);
* **`hcount_S3`**: `H²(K)(ρ) ≃ H²_c(ρ)` at `V` for every finite `ρ` with open kernel: a finer unramified cover `L` with
  `ker(π₁ ↠ Gal(L/F)) ⊆ ker ρ` (`exists_resL_ker_le`), its residue data (`exists_resDat_tw`), then `vCount`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
/-- `H²(Γ_V, -) = 0` at an open `K`. -/
theorem hallV_S3 {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (K : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hKo : IsOpen (K : Set (Pi1 (Places.Rfin Fq F) F)))
    (Λ : Type) [CommRing Λ] (n : ℕ) : H2All Λ K (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) K) l n := by
  have : Finite (Pi1 (Places.Rfin Fq F) F ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  have hcl : IsClosed ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ K : Subgroup _) :
      Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [Subgroup.coe_inf]
    exact (pi1geo_isClosed _ _ _).inter (K.isClosed_of_isOpen hKo)
  have h := h2All_subgroupOf hKo inf_le_right (CdOne.h2All_closed (Places.Rfin Fq F) Fq he hq
    (Kummer.perfect_Rfin Fq F) l (CP4a.isUnit_cast_Rfin hl) hPicU _ hcl inf_le_left Λ n)
  rwa [Subgroup.inf_subgroupOf_right] at h

include hq he in
/-- `H²(Γ_V ∩ I_V(t), -) = 0` at `V`. -/
theorem hallIV_S3 {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    {S : Type} [Fintype S] [DecidableEq S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    {Gf : Type} [Group Gf] {π : Pi1 (Places.Rfin Fq F) F →* Gf} {N : ℕ} {T : Type} [Fintype T]
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)]
    (RD : ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia N T)
    (K : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hKo : IsOpen (K : Set (Pi1 (Places.Rfin Fq F) F)))
    (Λ : Type) [CommRing Λ] (n : ℕ) (t : T) :
    H2All Λ K (geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) K ⊓ rdJ RD K t) l n := by
  have : Finite (Pi1 (Places.Rfin Fq F) F ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  have hΓn : (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).Normal := inferInstance
  let c : Pi1 (Places.Rfin Fq F) F →* Pi1 (Places.Rfin Fq F) F := (MulAut.conj (RD.x t)⁻¹).toMonoidHom
  have hc : ∀ g, c g = (RD.x t)⁻¹ * g * (RD.x t)⁻¹⁻¹ := fun g => MulAut.conj_apply _ _
  let Δ : Subgroup (Pi1 (Places.Rfin Fq F) F) := K ⊓ ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⊓ D.inertia (RD.sh t)).comap c
  have hcont : Continuous c := by
    have e : (c : Pi1 (Places.Rfin Fq F) F → Pi1 (Places.Rfin Fq F) F) = fun g => (RD.x t)⁻¹ * g * (RD.x t)⁻¹⁻¹ := funext hc
    rw [e]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hclI : IsClosed (((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⊓ D.inertia (RD.sh t) : Subgroup _) : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [Subgroup.coe_inf]
    exact (pi1geo_isClosed _ _ _).inter (CdOne.inertia_isClosed _ _ _ (D.P (RD.sh t)))
  have hcl : IsClosed (Δ : Set (Pi1 (Places.Rfin Fq F) F)) := by
    show IsClosed ((K ⊓ ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⊓ D.inertia (RD.sh t)).comap c : Subgroup _) : Set (Pi1 (Places.Rfin Fq F) F))
    rw [Subgroup.coe_inf, Subgroup.coe_comap]
    exact (K.isClosed_of_isOpen hKo).inter (hclI.preimage hcont)
  have hΔΓ : Δ ≤ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) := fun g hg => by
    have h1 := (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hg).2)).1
    rw [hc] at h1
    have h2 := hΓn.conj_mem _ h1 (RD.x t)
    rwa [show (RD.x t) * ((RD.x t)⁻¹ * g * (RD.x t)⁻¹⁻¹) * (RD.x t)⁻¹ = g by group] at h2
  have h := h2All_subgroupOf hKo (inf_le_left : Δ ≤ K) (CdOne.h2All_closed (Places.Rfin Fq F) Fq he hq
    (Kummer.perfect_Rfin Fq F) l (CP4a.isUnit_cast_Rfin hl) hPicU Δ hcl hΔΓ Λ n)
  have hEq : geoU (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) K ⊓ rdJ RD K t = Δ.subgroupOf K := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkΓ, hkJ⟩ := Subgroup.mem_inf.1 hk
      have hkJ' := (mem_rdJ RD K t k).1 hkJ
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_comap.2
        (Subgroup.mem_inf.2 ⟨?_, ?_⟩)⟩)
      · rw [hc]
        exact hΓn.conj_mem _ (Subgroup.mem_subgroupOf.1 hkΓ) _
      · rw [hc, inv_inv]
        exact hkJ'
    · intro hk
      obtain ⟨-, hk2⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)
      obtain ⟨hcΓ, hcI⟩ := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hk2)
      rw [hc] at hcΓ hcI
      rw [inv_inv] at hcI
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 ?_, (mem_rdJ RD K t k).2 hcI⟩
      have h2 := hΓn.conj_mem _ hcΓ (RD.x t)
      rwa [show (RD.x t) * ((RD.x t)⁻¹ * (k : Pi1 (Places.Rfin Fq F) F) * (RD.x t)⁻¹⁻¹) * (RD.x t)⁻¹ = k by group] at h2
  rw [hEq]
  exact h

end S3

end

end CupDuality
end RamanujanPetersson


end


