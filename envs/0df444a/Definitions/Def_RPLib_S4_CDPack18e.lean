-- Prove2me | Definitions.Def_RPLib_S4_CDPack18e
-- name    : RPLib_S4_CDPack18e
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:41:36.619874+00:00
-- url     : https://prove2.me/theorems/1e7ef4f2-2e11-4d29-b91c-0df99c8dfaaa
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 18e of 71
-- statement:
--   Part 18e of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack05
import Definitions.Def_RPLib_S4_CDPack07
import Definitions.Def_RPLib_S4_CDPack08b
import Definitions.Def_RPLib_S4_CDPack18b
import Definitions.Def_RPLib_S4_CDPack18d
import Definitions.Def_RPLib_S4_CDPack09c
import Definitions.Def_RPLib_S4_KummerLev
import Definitions.Def_RPLib_S4_EtShGalSurj
import Definitions.Def_RPLib_S4_Tsen
import Definitions.Def_RPLib_S4_TameInertia
import Definitions.Def_RPLib_S4_CDPack08

/-!
# Curve-duality library package, part 18e of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
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

include hq he in
/-- **Cone `H³ = 0`** in the S3 chart: `H²(π₁^geo ⊓ I_s, -) = 0` at every boundary point. -/
theorem cone_h3_eq_zero {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    {S : Type} (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S) (s : S)
    (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 (Places.Rfin Fq F) F) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s) l n :=
  CdOne.h2All_geo_inf_inertia (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU (D.P s) Λ n

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

omit [DecidableEq (RatFunc Fq)] in
/-- `ker (π₁ ↠ Gal(L/K))` is the fixing group of `L`. -/
theorem resL_eq_one_iff (L : IntermediateField F (AlgebraicClosure F)) (hL : L ∈ unramSet (Places.Rfin Fq F) F)
    (σ : Pi1 (Places.Rfin Fq F) F) :
    EtSheaves.TorSec.resL (Places.Rfin Fq F) F L hL σ = 1 ↔
      σ ∈ (IntermediateField.restrict (EtSheaves.TorSec.le_maxUnram (Places.Rfin Fq F) F L hL)).fixingSubgroup := by
  constructor
  · intro h
    refine (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr fun x hx => ?_
    have hx' : (x : AlgebraicClosure F) ∈ L := (IntermediateField.mem_restrict _ _).1 hx
    have ex : x = IntermediateField.inclusion (EtSheaves.TorSec.le_maxUnram (Places.Rfin Fq F) F L hL) ⟨x, hx'⟩ :=
      Subtype.ext rfl
    rw [ex]
    exact EtSheaves.TorSec.fix_of_resL_eq_one (Places.Rfin Fq F) F L hL σ h _
  · intro h
    exact EtSheaves.TorSec.resL_eq_one_of_fix (Places.Rfin Fq F) F L hL σ fun y =>
      (IntermediateField.mem_fixingSubgroup_iff _ σ).mp h _ ((IntermediateField.mem_restrict _ _).2 y.2)

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


