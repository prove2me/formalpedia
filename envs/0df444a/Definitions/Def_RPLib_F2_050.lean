-- Prove2me | Definitions.Def_RPLib_F2_050
-- name    : RPLib_F2_050
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T17:54:39.641391+00:00
-- url     : https://prove2.me/theorems/1918afba-3f72-4d47-b7c3-c94f0bffdbdc
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 050 of 70
-- statement:
--   File 050 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
--   * `S4.Def_RP_CupDuality_GysB`: S4-CurveDuality O4G-2: a unipotent family in the right kernel is zero
--   * `S4.Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_027
import Definitions.Def_RPLib_F2_043

/-!
# Ramanujan-Petersson curve library (flat edition), file 050 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
* `S4.Def_RP_CupDuality_GysB`: S4-CurveDuality O4G-2: a unipotent family in the right kernel is zero
* `S4.Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
-/

set_option autoImplicit false

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

attribute [local instance] GalCover.grp GalCover.fG

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **The cone's `H²` is `H²_c = V_Γ`, with Frobenius `q • ρ(φ⁻¹)`** (S3 chart, `ρ = τ ∘ π`). -/
theorem h2Equiv_S3 {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    {V : Type} [AddCommGroup V] [Module Λ V] [Finite V] (τ : Representation Λ Gf V) :
    ∃ E : H2K (τ.comp π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia (isOpen_comp_ker π τ hπ) ≃ₗ[Λ]
        H2c (τ.comp π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)),
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ → ∀ x,
        E (frobH2K (τ.comp π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹)
            (trueH D φ⁻¹) (isOpen_comp_ker π τ hπ) (trueCompat D φ⁻¹) x) =
          frobH2c (τ.comp π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ (Fintype.card Fq : Λ) (E x) := by
  letI : Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π) := Fintype.ofFinite _
  letI : ∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π) :=
    fun _ => Fintype.ofFinite _
  letI : Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  letI : DecidableEq (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), D.P s' = g • D.P s → s = s' :=
    D.disj
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨D', hTWD⟩ := exists_resDat_tw hq he hNF hPic hM hMU π hπM D.P hP hcov hdis D.inertia (fun _ => rfl)
  have hall := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU Λ n
  have hallI : ∀ s, H2All Λ (Pi1 (Places.Rfin Fq F) F)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s) l n :=
    fun s => cone_h3_eq_zero hq he hl hPicU D s Λ n
  have hMo : ∀ m : MonoidAlgebra Λ Gf, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  refine ⟨(D'.toResHyp hΛ hπ).h2Equiv hπ τ hΛ hall hallI, fun φ hφ x => ?_⟩
  have hu := fun s => trueTau_smul D φ⁻¹ s
  refine (D'.toResHyp hΛ hπ).h2Equiv_frob hπ τ hΛ hall hallI φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹)
    (trueCompat D φ⁻¹) (Fintype.card Fq : Λ) ?_ ?_ ?_ x
  · intro s d
    exact map_inf_conj_iff (I1 := D.inertia (trueTau D φ⁻¹ s)) (I2 := D.inertia s) π _ _
      (fun y => inert_conj_iff (hu s) y) d
  · exact tt_bijective D.P _ hdis φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueTau_spec D φ⁻¹)
  · intro s e
    have hg : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq)
        (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact isFrobLift_geo_mul (inv_mem (trueH D φ⁻¹ s).2) hφ
    have hc : (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ * D'.σ s *
        (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) ∈ D'.J (trueTau D φ⁻¹ s) :=
      (D'.hJ _ _).2 ⟨bdry_mem _ D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) s _ (D'.hσ s),
        by rw [map_mul, map_mul, D'.hσπ s, mul_one, map_inv, inv_mul_cancel]⟩
    have h1 := hTWD s (trueTau D φ⁻¹ s) (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) hg (hu s)
      (MonoidAlgebra Λ Gf) hMo (resK π _ (D'.J (trueTau D φ⁻¹ s)) (D'.hJ (trueTau D φ⁻¹ s)) e)
      (resK_lc π _ _ _ e) (resK_add π _ _ _ e) hc
    exact h1.trans (Nat.cast_smul_eq_nsmul Λ _ _).symm

include hq he in
set_option maxHeartbeats 1600000 in
/-- **S4-PD (4): the cone's `H²` is `H²_c = V_Γ`, Frobenius `q • ρ(φ⁻¹)`, for every lisse `ρ`** (finite `V`, open
kernel; S3 chart, true boundary permutation of `φ⁻¹`). -/
theorem h2Equiv_lisse {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    {V : Type} [AddCommGroup V] [Module Λ V] [Finite V] (ρ : Representation Λ (Pi1 (Places.Rfin Fq F) F) V)
    (hρ : IsOpen (ρ.ker : Set (Pi1 (Places.Rfin Fq F) F))) :
    ∃ E : H2K ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia hρ ≃ₗ[Λ]
        H2c ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)),
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ → ∀ x,
        E (frobH2K ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹)
            (trueH D φ⁻¹) hρ (trueCompat D φ⁻¹) x) =
          frobH2c ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ (Fintype.card Fq : Λ) (E x) := by
  obtain ⟨L, hL, hk⟩ := EtSheaves.TorSec.exists_resL_ker_le (Places.Rfin Fq F) F ρ.ker hρ
  obtain ⟨τ, rfl⟩ : ∃ τ : Representation Λ (coverOf (Places.Rfin Fq F) F L hL).G V,
      τ.comp (EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL) = ρ :=
    ⟨_, EtSheaves.TorSec.factorRep_comp L hL Λ ρ hk⟩
  letI : Fintype (coverOf (Places.Rfin Fq F) F L hL).G := Fintype.ofFinite _
  have key := h2Equiv_S3 hq he hl n hPicU hPic hL (EtSheaves.TorSec.le_maxUnram (Places.Rfin Fq F) F L hL)
    (EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL) (resL_eq_one_iff L hL)
    (EtSheaves.TorSec.isOpen_ker_resL (Places.Rfin Fq F) F L hL) D hDB hΛ τ
  exact key

end S3

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysB =====
section

/-!
# S4-CurveDuality O4G-2: a unipotent family in the right kernel is zero

Route G (session 44). In the S3 chart (`Γ = π₁^geo`, boundary inertia `D.inertia`, finite `Λ` with `lⁿ = 0`), let
`ρ` be a lisse representation on `(ι → Λ) × (ι → Λ)` on which `Γ` acts unipotently through parabolic homs `d_i`
(`IsUniFam`). If every `d_i` lies in the right kernel of `constPair`, then every `d_i` is zero: S4-PD's
`h2Equiv_lisse` gives `#H²(K) = #V_Γ`, while GysA gives `#H²(K) ≥ #(ι → Λ)²` and `#V_Γ < #V` if some `d_i ≠ 0`.
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
/-- **O4G-2.** A parabolic unipotent family in the right kernel of `constPair` vanishes. -/
theorem uniFam_eq_zero {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    {σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ}
    {t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s)}
    (H : CupHyp (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ) σ σ (LinearMap.mul Λ Λ)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)))
    (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
    {ι : Type} [Fintype ι] (ρ : Representation Λ (Pi1 (Places.Rfin Fq F) F) ((ι → Λ) × (ι → Λ)))
    (hρ : IsOpen (ρ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {d : ι → pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) → Λ} (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)),
      (g : Pi1 (Places.Rfin Fq F) F) ∈ D.inertia s → d i g = 0)
    (hd : ∀ i, d i ∈ Z1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)))
    (hR : ∀ i (p : Z1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia),
      constPair H DD (H1c.mk (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia p)
        (H1.mk σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ⟨d i, hd i⟩) = 0) :
    ∀ i g, d i g = 0 := by
  classical
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨i, g, hg⟩ := hne
  obtain ⟨E, -⟩ := h2Equiv_lisse hq he hl n hPicU hPic D hDB hΛ ρ hρ
  have : Finite (H2c ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))) :=
    Finite.of_surjective _ (Representation.Coinvariants.mk_surjective _)
  have : Finite (H2K ρ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia hρ) :=
    Finite.of_equiv _ E.toEquiv.symm
  have h1 := card_sq_le_h2K H DD hρ hρΓ hpar hd hR
  have h2 := card_coinv_lt hρΓ hg
  rw [Nat.card_congr E.toEquiv] at h1
  rw [Nat.card_prod] at h2
  omega

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysF =====
section

/-!
# S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)

Route G (session 44). Let `d` be a parabolic hom in the right kernel of `constPair` (`InR`), with the Frobenius
formula of `constDuality_S3` for a Frobenius lift `φ`. Choose an open normal `N` with `N ∩ Γ ⊆ ker d` (Krull
topology), coinduce (GysC) to a lisse unipotent family with parameters `d ∘ conj(r_i)`; each `r_i⁻¹ = φ^j γ n` (GysD),
so each parameter is `d ∘ conjΓ φ^j` (GysE) and lies in the right kernel. GysB then forces every parameter, hence `d`,
to vanish (`inR_eq_zero`). `isUnit_card`: `q` is a unit in `Λ` (`l ≠ p`).
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
set_option maxHeartbeats 1600000 in
/-- **O4G.** A parabolic hom in the right kernel of `constPair` is zero. -/
theorem inR_eq_zero {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    {σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ}
    (htriv : ∀ (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x)
    {t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s)}
    (H : CupHyp (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ) σ σ (LinearMap.mul Λ Λ)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)))
    (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
    {φ : Pi1 (Places.Rfin Fq F) F} (hφ : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹)
        (trueCompat D φ⁻¹) x) (frobH1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ y) =
      ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * constPair H DD x y)
    {d : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) → Λ} (hR : InR H DD d) : d = 0 := by
  classical
  have hc : IsUnit ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) :=
    (isUnit_card hq hl n hΛ).mul (isUnit_rep_one σ φ⁻¹)
  obtain ⟨hd, hpar, hker⟩ := hR
  have hadd := add_of_Z1 htriv hd
  obtain ⟨N, hNn, hNo, hdN⟩ : ∃ N : Subgroup (Pi1 (Places.Rfin Fq F) F), N.Normal ∧
      IsOpen (N : Set (Pi1 (Places.Rfin Fq F) F)) ∧
      ∀ g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), (g : Pi1 (Places.Rfin Fq F) F) ∈ N → d g = 0 := by
    obtain ⟨U, hU, hUd⟩ := isOpen_induced_iff.mp (hd.1.isOpen_fiber 0)
    have h1U : (1 : Pi1 (Places.Rfin Fq F) F) ∈ U := by
      have : (1 : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) ∈ Subtype.val ⁻¹' U := by
        rw [hUd]
        exact d_one hadd
      exact this
    obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff F (maxUnram (Places.Rfin Fq F) F) U).mp
      (hU.mem_nhds h1U)
    have := hfin
    obtain ⟨N, hNn, hNo, hNE⟩ := CdOne.exists_openNormal_le E.fixingSubgroup E.fixingSubgroup_isOpen
    refine ⟨N, hNn, hNo, fun g hg => ?_⟩
    have hg' : g ∈ Subtype.val ⁻¹' U := hE (hNE hg)
    rw [hUd] at hg'
    exact hg'
  have : Finite (Pi1 (Places.Rfin Fq F) F ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  have : Finite (Cos (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  let _ : Fintype (Cos (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N) := Fintype.ofFinite _
  have hRi : ∀ i : Cos (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N,
      InR H DD (fun g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) =>
        d ⟨repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i * g *
          (repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i)⁻¹,
          Subgroup.Normal.conj_mem inferInstance _ g.2 _⟩) := by
    intro i
    obtain ⟨j, γ, hγ, m, hm, hψ⟩ :=
      exists_frobPow_mul hφ N hNo (repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i)⁻¹
    have e : (fun g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) =>
        d ⟨repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i * g *
          (repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i)⁻¹,
          Subgroup.Normal.conj_mem inferInstance _ g.2 _⟩) =
        fun g => d (conjΓ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (φ ^ j) g) := by
      funext g
      rw [← d_conj_mul htriv hd N hdN (φ ^ j) hγ hm g]
      congr 1
      apply Subtype.ext
      rw [conjΓ_val, ← hψ, inv_inv]
    rw [e]
    exact inR_conj_pow H DD htriv (trueCompat D φ⁻¹) (trueCompat D φ) hc hF j ⟨hd, hpar, hker⟩
  have hall := uniFam_eq_zero hq he hl n hPicU hPic D hDB hΛ H DD
    (rhoV (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N hadd hdN)
    (Subgroup.isOpen_mono (le_ker_rhoV _ N hadd hdN) hNo) (isUniFam_rhoV _ N hadd hdN)
    (fun i => (hRi i).2.1) (fun i => (hRi i).1) (fun i _ => (hRi i).2.2 _)
  funext g0
  obtain ⟨i0⟩ : Nonempty (Cos (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N) := ⟨QuotientGroup.mk 1⟩
  have hmem : (repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i0)⁻¹ * (g0 : Pi1 (Places.Rfin Fq F) F) *
      repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i0 ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) := by
    have := (inferInstance : (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).Normal).conj_mem _ g0.2
      (repG (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) N i0)⁻¹
    rwa [inv_inv] at this
  have h := hall i0 ⟨_, hmem⟩
  rw [Pi.zero_apply]
  convert h using 2
  apply Subtype.ext
  dsimp only
  group

end S3

end

end CupDuality
end RamanujanPetersson


end


