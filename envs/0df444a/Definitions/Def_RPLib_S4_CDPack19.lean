-- Prove2me | Definitions.Def_RPLib_S4_CDPack19
-- name    : RPLib_S4_CDPack19
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T12:04:42.066768+00:00
-- url     : https://prove2.me/theorems/4e25d4d2-080b-4e79-b43a-5a62dd586533
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 19 of 71
-- statement:
--   Part 19 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
--   * `Def_RP_CupDuality_GysB`: S4-CurveDuality O4G-2: a unipotent family in the right kernel is zero
--   * `Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack05
import Definitions.Def_RPLib_S4_CDPack07
import Definitions.Def_RPLib_S4_CDPack18e
import Definitions.Def_RPLib_S4_CDPack15c

/-!
# Curve-duality library package, part 19 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
* `Def_RP_CupDuality_GysB`: S4-CurveDuality O4G-2: a unipotent family in the right kernel is zero
* `Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ConeDuality_S3 =====
section

/-!
# S4-CurveDuality O6c: constant-coefficient duality in the S3 chart

`U = Spec Rfin`, `Γ = π₁^geo`, boundary inertia `D.inertia`, coefficients `Λ` (finite, `lⁿ = 0`), `σ` a character
`Pi1 → Λˣ` (as a representation on `Λ`) trivial on `Γ`, with open kernel. Under `PicDivU` / `PicDivX`:
* there are tame generators `t`, the constant data `ConstData σ Γ I t` (from S4-PD's residue data with trivial
  `π`, `constData_of_resHyp`) and the cup-product hypotheses (`cd ≤ 1`);
* `ParabolicPerfect H D` (the block `H¹_c/im(k^S) × H¹_par`, obligation O5) implies the duality
  `H¹_c(Ū, Λ) × H¹(Ū, σ) → Λ` is perfect;
* Frobenius: `⟨F x, F y⟩ = q · σ(φ⁻¹)(1) · ⟨x, y⟩` for every Frobenius lift `φ` (`F` = `φ⁻¹` with the true boundary
  permutation), via S4-PD's `h2Equiv_lisse` and `constPair_frob_of_equiv`. For `σ = Λ(1)` the scalar is `1`.
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

section Abstract

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)}

/-- The parabolic block `H¹_c / im(k^S) × H¹_par → k` of `constPair` is perfect (obligation O5). -/
def ParabolicPerfect (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) : Prop :=
  (pairQuotSub (constPair H D) _ _ (constPair_h0 H D)).IsPerfPair

theorem constPair_isPerfPair_of_parabolic (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (hB : ParabolicPerfect H D) : (constPair H D).IsPerfPair :=
  constPair_isPerfPair H D hB

end Abstract

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The trivial quotient `π = 1` is cut out by the base field. -/
theorem one_iff_fix_bot (g : Pi1 (Places.Rfin Fq F) F) :
    (1 : Pi1 (Places.Rfin Fq F) F →* PUnit) g = 1 ↔
      g ∈ (IntermediateField.restrict
        (bot_le : (⊥ : IntermediateField F (AlgebraicClosure F)) ≤ maxUnram (Places.Rfin Fq F) F)).fixingSubgroup := by
  refine iff_of_true rfl ((IntermediateField.mem_fixingSubgroup_iff _ g).2 fun x hx => ?_)
  rw [IntermediateField.mem_restrict, IntermediateField.mem_bot] at hx
  obtain ⟨r, hr⟩ := hx
  have hx : x = algebraMap F (maxUnram (Places.Rfin Fq F) F) r := Subtype.ext hr.symm
  rw [hx, AlgEquiv.commutes]

include hq he in
set_option maxHeartbeats 1600000 in
/-- **O6c.** Constant-coefficient duality on `Ū` in the S3 chart, reduced to the parabolic block, with its
Frobenius behaviour. -/
theorem constDuality_S3 {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (Pi1 (Places.Rfin Fq F) F) Λ) (hσ : IsOpen (σ.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    (htriv : ∀ (g : pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) (x : Λ), σ g x = x) :
    ∃ (t : (s : S) → ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s))
      (DD : ConstData σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia t)
      (H : CupHyp (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ) σ σ (LinearMap.mul Λ Λ)
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
      (ParabolicPerfect H DD → (constPair H DD).IsPerfPair) ∧
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ (x : H1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
            (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia)
          (y : H1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))),
        constPair H DD (frobH1c (Representation.trivial Λ (Pi1 (Places.Rfin Fq F) F) Λ)
            (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹)
            (trueCompat D φ⁻¹) x) (frobH1 σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) φ⁻¹ y) =
          ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * constPair H DD x y := by
  letI : Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := Fintype.ofFinite _
  letI : ∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map
      (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)) := fun _ => Fintype.ofFinite _
  letI : Fintype (CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  letI : DecidableEq (CosT (1 : Pi1 (Places.Rfin Fq F) F →* PUnit)
      (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hπ : IsOpen (((1 : Pi1 (Places.Rfin Fq F) F →* PUnit).ker : Subgroup _) : Set (Pi1 (Places.Rfin Fq F) F)) := by
    rw [MonoidHom.ker_one, Subgroup.coe_top]
    exact isOpen_univ
  obtain ⟨D', -⟩ := exists_resDat_tw hq he hNF hPic (bot_mem_unramSet (Places.Rfin Fq F) F) bot_le
    (1 : Pi1 (Places.Rfin Fq F) F →* PUnit) one_iff_fix_bot D.P hP hcov D.disj D.inertia (fun _ => rfl)
  have hall := CdOne.h2All_geo (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU Λ n
  have hL : ∀ m : Λ, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  let H := constCupHyp σ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) hσ (h2Van_top_of_all hall hL hσ)
  let DD := constData_of_resHyp (D'.toResHyp hΛ hπ) htriv
  obtain ⟨E, hE⟩ := h2Equiv_lisse hq he hl n hPicU hPic D hDB hΛ σ hσ
  exact ⟨_, DD, H, constPair_isPerfPair_of_parabolic H DD, fun φ hφ x y =>
    constPair_frob_of_equiv H DD φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) _ E (hE φ hφ) x y⟩

end S3

end

end CupDuality
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

include hq in
/-- `q = #𝔽_q` is a unit in `Λ` when `lⁿ = 0` in `Λ` and `l ≠ p`. -/
theorem isUnit_card {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ) {Λ : Type} [CommRing Λ]
    (hΛ : ((l ^ n : ℕ) : Λ) = 0) : IsUnit ((Fintype.card Fq : ℕ) : Λ) := by
  have hlp : l ≠ p := fun h => hl (by rw [h]; exact CharP.cast_eq_zero F p)
  have hcop : Nat.Coprime (p ^ e) (l ^ n) :=
    Nat.Coprime.pow e n ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : l.Prime)).2 hlp.symm)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h0 : (l : Λ) ^ n = 0 := by exact_mod_cast hΛ
  have h1 := congrArg (Int.cast : ℤ → Λ) hab
  push_cast at h1
  rw [h0, mul_zero, add_zero] at h1
  rw [hq]
  exact IsUnit.of_mul_eq_one (a : Λ) (by rw [Nat.cast_pow, mul_comm]; exact h1)

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


