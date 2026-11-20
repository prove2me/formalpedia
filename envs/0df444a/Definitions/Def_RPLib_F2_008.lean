-- Prove2me | Definitions.Def_RPLib_F2_008
-- name    : RPLib_F2_008
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T07:04:35.708853+00:00
-- url     : https://prove2.me/theorems/1aab07a5-a7d5-4804-979e-1f94915637e4
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 008 of 70
-- statement:
--   File 008 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
--   * `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
--   * `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
--   * `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
--   * `S4.Def_RP_CupDuality_Alg`: S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing
--   * `S4.Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
--   * `S4.Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
--   * `S4.Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
--   * `S4.Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
--   * `S4.Def_RP_EtSheaves_GalGen`: S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`
--   * `S4.Def_RP_EtSheaves_GalSurj`: S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf
--   * `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
--   * `S4.Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
--   * `S4.Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
--   * `S4.Def_RP_CupDuality_GysC`: S4-CurveDuality O4G-3: coinducing a unipotent character
--   * `S4.Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
--   * `S4.Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
--   * `S4.Def_RP_CupDuality_LamSep`: S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings
--   * `S4.Def_RP_CupDuality_LamCoord`: S4-CurveDuality O5d-2: coordinates on the parabolic block
--   * `S4.Def_RP_CupDuality_LamPerf`: S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`
--   * `S4.Def_RP_CupDuality_ParZ`: S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel
--   * `S4.Def_RP_CupDuality_ParS3a`: S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_006

/-!
# Ramanujan-Petersson curve library (flat edition), file 008 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
* `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
* `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
* `S4.Def_RP_CP4a_FrobLift`: S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist
* `S4.Def_RP_CupDuality_Alg`: S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing
* `S4.Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
* `S4.Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
* `S4.Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
* `S4.Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
* `S4.Def_RP_EtSheaves_GalGen`: S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`
* `S4.Def_RP_EtSheaves_GalSurj`: S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf
* `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
* `S4.Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
* `S4.Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
* `S4.Def_RP_CupDuality_GysC`: S4-CurveDuality O4G-3: coinducing a unipotent character
* `S4.Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
* `S4.Def_RP_CupDuality_GysF`: S4-CurveDuality O4G: the parabolic right kernel of `constPair` is zero (S3 chart)
* `S4.Def_RP_CupDuality_LamSep`: S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings
* `S4.Def_RP_CupDuality_LamCoord`: S4-CurveDuality O5d-2: coordinates on the parabolic block
* `S4.Def_RP_CupDuality_LamPerf`: S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`
* `S4.Def_RP_CupDuality_ParZ`: S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel
* `S4.Def_RP_CupDuality_ParS3a`: S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_GalCover =====
section

/-!
# S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson

/-- A connected finite Galois etale cover `Spec B → Spec A` with group `G`: `A = B^G` with `G` acting
faithfully (`IsGaloisGroup`), `B` a finite `A`-algebra and a domain, and every inertia group trivial
(for Galois covers this is equivalent to `A → B` etale, SGA 1 V 2.6). -/
structure GalCover (A : Type) [CommRing A] [IsDomain A] where
  B : Type
  [ring : CommRing B]
  [dom : IsDomain B]
  [alg : Algebra A B]
  [inj : FaithfulSMul A B]
  [fin : Module.Finite A B]
  G : Type
  [grp : Group G]
  [fG : Finite G]
  [act : MulSemiringAction G B]
  [gal : IsGaloisGroup G A B]
  unramified : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

namespace GalCover

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-! ## Constants, the geometric subgroup, Frobenius on constants -/

section Constants

variable (Fq : Type) [Field Fq] [Algebra Fq A] [Algebra Fq C.B] [IsScalarTower Fq A C.B]

/-- The constant field of the cover: the algebraic closure of `Fq` in `B`. -/
noncomputable abbrev constField : Subalgebra Fq C.B := integralClosure Fq C.B

end Constants

/-! ## Morphisms of covers -/

/-! ## Etale Galois extensions have trivial inertia (bridge `ofEtale`) -/

section Etale

variable {B G : Type} [CommRing B] [IsDomain B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

end Etale

end GalCover

/-! ## The etale fundamental group and the finite-quotient bridge -/

section Pi1

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

noncomputable example : TopologicalSpace (Pi1 A K) := inferInstance

section Bridge

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- The Galois cover of `Spec A` given by an unramified finite Galois subextension `L` of `K̄/K`:
`B` = integral closure of `A` in `L`, `G = Gal(L/K)`. -/
noncomputable def coverOf (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    GalCover A :=
  haveI := hL.1
  haveI := hL.2.1
  haveI : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  { B := integralClosure A L
    G := L ≃ₐ[K] L
    inj := (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).mpr fun a b h => by
      have hinj : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      exact hinj (by simpa using congrArg Subtype.val h)
    fin := IsIntegralClosure.finite A K L (integralClosure A L)
    gal := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L
    unramified := hL.2.2 }

theorem coverOf_G (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    (coverOf A K L hL).G = (L ≃ₐ[K] L) := rfl

end Bridge

end Pi1

/-! ## Charts over other base rings: the infinity chart and boundary places (review R5) -/

namespace GalCover

section Charts

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (K L : Type) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra C.B L]
  [IsFractionRing C.B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C.B L]
  [MulSemiringAction C.G L] [SMulDistribClass C.G C.B L]

variable (R0 : Type) [CommRing R0] [IsDomain R0] [IsIntegrallyClosed R0] [Algebra R0 K]
  [IsFractionRing R0 K] [Algebra R0 L] [IsScalarTower R0 K L]

end Charts

/-! ### The two charts of a base curve inside `𝔸¹`: finite (`Fq[X]`) and infinity (`O_∞`) -/

section CurveCharts

open Polynomial

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]

variable [Algebra Fq[X] L] [IsScalarTower Fq[X] (RatFunc Fq) L]

end CurveCharts

end GalCover

end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_CxIso =====
section

/-!
# S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`

For a finite `Gf`-representation `τ` on `M` (pulled back to `G` along `π`), the coinvariants of the free model
`P = [A → E_Γ × A^S → Π_s E_s]` tensored with `M` are identified termwise with the cone complex
`K(M) = [M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)]` (`coinvA`, `iso1`, `iso2`), and the identifications commute with
the differentials (`iso1_map_d0`, `iso2_map_d1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))
  {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

theorem isOpen_comp_ker (hπ : IsOpen (π.ker : Set G)) : IsOpen ((τ.comp π).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hπ
  rw [MonoidHom.mem_ker] at hg ⊢
  show τ (π g) = 1
  rw [hg, map_one]

variable [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_CoinvG =====
section

/-!
# S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`

* `AΓ π Γ := Λ[Gf]_Γ`, the coinvariants of `Γ` acting on `Λ[Gf]` by left multiplication through `π`.
* `rRepΓ π Γ`: `Gf` acting on `AΓ` by right multiplication by `h⁻¹` (it descends: left and right multiplication commute).
* `coinvG π Γ τ : (AΓ ⊗ M)_{Gf} ≃ M_Γ`, `⟦⟦a⟧ ⊗ m⟧ ↦ ⟦a · m⟧`, inverse `⟦m⟧ ↦ ⟦⟦1⟧ ⊗ m⟧`
  (`M_Γ = Coinvariants ((τ.comp π).comp Γ.subtype)`, which is `CurveCoh.H2c (τ.comp π) Γ` by definition).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

section CoinvG

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

/-- `a ↦ (m ↦ ⟦a · m⟧)` on `Λ[Gf]`. -/
def gB0 : MonoidAlgebra Λ Gf →ₗ[Λ] M →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  (τ.asAlgebraHom.toLinearMap : MonoidAlgebra Λ Gf →ₗ[Λ] M →ₗ[Λ] M).compr₂
    (Coinvariants.mk ((τ.comp π).comp Γ.subtype))

theorem gB0_apply (a : MonoidAlgebra Λ Gf) (m : M) :
    gB0 π Γ τ a m = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

end CoinvG

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_FrobLift =====
section

/-!
# S4-CP4a, part f1 + f2: the constants and an arithmetic Frobenius lift exist

For a function field `F/𝔽_q` (`q = p ^ e`) with `constField = 𝔽_q`:
* `cast_ne_zero_of_not_dvd`, `isUnit_cast_Rfin`, `isUnit_cast_Rinf`: `N = l ^ n` with `l ∤ q` is a unit;
* `exists_zeta_geo`: a primitive `N`-th root of unity `ζ ∈ K_U` fixed by `π₁^geo`;
* `exists_zeta_level`: primitive `(q ^ a - 1)`-th roots of unity in `K_U`;
* `exists_frobLift`: there is `φ ∈ π₁(U)` with `φ x = x ^ q` on all constants (a compactness argument over the
  closed sets `T_m = {σ | σ x = x ^ q whenever x ^ (q ^ m) = x}`, each nonempty by lifting `frobF` on `F_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places PicDescent CurveCoh Kummer GalCover

noncomputable section

section FrobSet

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- `T_m`: the automorphisms acting as `x ↦ x ^ q` on `𝔽_{q^m}`. -/
def frobSet (q m : ℕ) : Set (Pi1 A K) := {σ | ∀ x : maxUnram A K, x ^ q ^ m = x → σ x = x ^ q}

theorem isClosed_frobSet (q m : ℕ) : IsClosed (frobSet (A := A) (K := K) q m) := by
  have hs : frobSet (A := A) (K := K) q m =
      ⋂ (x : maxUnram A K) (_ : x ^ q ^ m = x), {σ : Pi1 A K | σ x = x ^ q} := by
    ext σ
    simp only [frobSet, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_setOf_apply_eq x (x ^ q)

theorem frobSet_mono (q a b : ℕ) : frobSet (A := A) (K := K) q (a * b) ⊆ frobSet q a := by
  intro σ hσ x hx
  exact hσ x (by rw [pow_mul]; exact pow_pow_iter hx b)

end FrobSet

section Exist

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hk hq he in
/-- `T_m ≠ ∅`: lift `frobF` on `F_m ⊆ K_U` to `K_U`. -/
theorem frobSet_nonempty (m : ℕ) [NeZero m] :
    (frobSet (A := Rfin Fq F) (K := F) (Fintype.card Fq) m).Nonempty := by
  have hle := Fc_le_maxUnram (F := F) hq he m
  have : IsGalois F (Fc Fq F (AlgebraicClosure F) m) := (Fc_mem_unramSet (F := F) hq he m).2.1
  obtain ⟨g, hg⟩ := exists_lift_level hle (frobF (isConstExt_Fc Fq F (AlgebraicClosure F) hk m))
  refine ⟨g, fun x hx => ?_⟩
  have hxL : (x : AlgebraicClosure F) ∈ Lc Fq (AlgebraicClosure F) m := by
    rw [mem_Lc]
    have h2 := congrArg Subtype.val hx
    rwa [SubmonoidClass.coe_pow] at h2
  have h1 := hg (algebraMap (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m) ⟨x, hxL⟩)
  rw [frobF_algebraMap_L] at h1
  have hy : IntermediateField.inclusion hle
      (algebraMap (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m) ⟨x, hxL⟩) = x :=
    Subtype.ext rfl
  rw [hy] at h1
  rw [h1]
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  show ((frobL Fq (Lc Fq (AlgebraicClosure F) m) ⟨x, hxL⟩ : Lc Fq (AlgebraicClosure F) m) : AlgebraicClosure F) =
    (x : AlgebraicClosure F) ^ Fintype.card Fq
  rw [frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rfl

include hk hq he in
/-- **An arithmetic Frobenius lift exists** in `π₁(U)`. -/
theorem exists_frobLift : ∃ φ : Pi1 (Rfin Fq F) F, IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ := by
  let T : ℕ → Set (Pi1 (Rfin Fq F) F) := fun k => frobSet (Fintype.card Fq) (k + 1)
  have hdir : Directed (· ⊇ ·) T := by
    intro i j
    have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      exact frobSet_mono _ _ _
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      rw [mul_comm]
      exact frobSet_mono _ _ _
  have hne : (⋂ k, T k).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir
      (fun k => frobSet_nonempty hk hq he (k + 1)) (fun k => (isClosed_frobSet _ _).isCompact)
      (fun k => isClosed_frobSet _ _)
  obtain ⟨φ, hφ⟩ := hne
  refine ⟨φ, fun x hx => ?_⟩
  obtain ⟨n, hn, hxn⟩ := hx
  have h := Set.mem_iInter.1 hφ (n - 1)
  exact h x (by rw [Nat.sub_add_cancel hn]; exact hxn)

end Exist

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CupDuality_Alg =====
section

/-!
# S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing

* `pairSubQuot`, `pairQuotSub`: for `P : M × N → Λ` and submodules `M₁ ≤ M`, `N₁ ≤ N` with `P(M₁, N₁) = 0`, the
  induced pairings `M₁ × N/N₁ → Λ` and `M/M₁ × N₁ → Λ`.
* `bijective_of_block`, `isPerfPair_of_block`: if both induced pairings are perfect, so is `P` (any `Λ`).
* `dotL`, `constSub`, `sumKer`, `resPair`: the residue pairing `(S → Λ)/Λ × ker(Σ) → Λ`, `(m, r) ↦ Σ m_s r_s`;
  `resPair_isPerfPair` (any finite `S`, any `Λ`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CupDuality

open Function Module

section Block

variable {Λ M N : Type*} [CommRing Λ] [AddCommGroup M] [AddCommGroup N] [Module Λ M] [Module Λ N]
  (P : M →ₗ[Λ] N →ₗ[Λ] Λ) (M₁ : Submodule Λ M) (N₁ : Submodule Λ N)

/-- The pairing `M₁ × N/N₁ → Λ` induced by `P` when `P(M₁, N₁) = 0`. -/
def pairSubQuot (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) : M₁ →ₗ[Λ] (N ⧸ N₁) →ₗ[Λ] Λ :=
  (N₁.liftQ (P.flip.compl₂ M₁.subtype) (fun n hn => by
    rw [LinearMap.mem_ker]; ext m; simpa using h0 m m.2 n hn)).flip

/-- The pairing `M/M₁ × N₁ → Λ` induced by `P` when `P(M₁, N₁) = 0`. -/
def pairQuotSub (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) : (M ⧸ M₁) →ₗ[Λ] N₁ →ₗ[Λ] Λ :=
  M₁.liftQ (P.compl₂ N₁.subtype) (fun m hm => by
    rw [LinearMap.mem_ker]; ext n; simpa using h0 m hm n n.2)

variable {P M₁ N₁}

@[simp] theorem pairSubQuot_apply (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) (m : M₁) (n : N) :
    pairSubQuot P M₁ N₁ h0 m (Submodule.Quotient.mk n) = P m n := rfl

@[simp] theorem pairQuotSub_apply (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) (m : M) (n : N₁) :
    pairQuotSub P M₁ N₁ h0 (Submodule.Quotient.mk m) n = P m n := rfl

/-- If both induced pairings are left-bijective, so is `P`. -/
theorem bijective_of_block (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0)
    (hA : Bijective (pairSubQuot P M₁ N₁ h0)) (hB : Bijective (pairQuotSub P M₁ N₁ h0)) :
    Bijective P := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : m ∈ M₁ := by
      have hz : pairQuotSub P M₁ N₁ h0 (Submodule.Quotient.mk m) = pairQuotSub P M₁ N₁ h0 0 := by
        rw [map_zero]; ext n; simp [hm]
      have := hB.1 hz
      rwa [Submodule.Quotient.mk_eq_zero] at this
    have hz : pairSubQuot P M₁ N₁ h0 ⟨m, h1⟩ = pairSubQuot P M₁ N₁ h0 0 := by
      rw [map_zero]; ext n; simp [hm]
    exact congrArg Subtype.val (hA.1 hz)
  · intro φ
    obtain ⟨q, hq⟩ := hB.2 (φ.comp N₁.subtype)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective M₁ q
    have hv : N₁ ≤ LinearMap.ker (φ - P m) := fun n hn => by
      have := LinearMap.congr_fun hq ⟨n, hn⟩
      simp only [pairQuotSub_apply, LinearMap.coe_comp, Submodule.coe_subtype, comp_apply] at this
      simp [this]
    obtain ⟨m₁, hm₁⟩ := hA.2 (N₁.liftQ (φ - P m) hv)
    refine ⟨m + m₁, ?_⟩
    ext n
    have := LinearMap.congr_fun hm₁ (Submodule.Quotient.mk n)
    simp only [pairSubQuot_apply, Submodule.liftQ_apply, LinearMap.sub_apply] at this
    simp [this]

/-- Block-triangular perfect pairings: if `P(M₁, N₁) = 0` and the induced pairings `M₁ × N/N₁ → Λ` and
`M/M₁ × N₁ → Λ` are perfect, then `P` is perfect. -/
theorem isPerfPair_of_block (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0)
    [hA : (pairSubQuot P M₁ N₁ h0).IsPerfPair] [hB : (pairQuotSub P M₁ N₁ h0).IsPerfPair] :
    P.IsPerfPair := by
  have h0' : ∀ n ∈ N₁, ∀ m ∈ M₁, P.flip n m = 0 := fun n hn m hm => by
    simpa using h0 m hm n hn
  have eA : pairSubQuot P.flip N₁ M₁ h0' = (pairQuotSub P M₁ N₁ h0).flip :=
    LinearMap.ext fun n => Submodule.linearMap_qext _ (LinearMap.ext fun m => rfl)
  have eB : pairQuotSub P.flip N₁ M₁ h0' = (pairSubQuot P M₁ N₁ h0).flip :=
    Submodule.linearMap_qext _ (LinearMap.ext fun n => LinearMap.ext fun m => rfl)
  refine ⟨bijective_of_block h0 (LinearMap.IsPerfPair.bijective_left _)
    (LinearMap.IsPerfPair.bijective_left _), ?_⟩
  refine bijective_of_block h0' ?_ ?_
  · rw [eA]; exact LinearMap.IsPerfPair.bijective_right _
  · rw [eB]; exact LinearMap.IsPerfPair.bijective_right _

end Block

section Residue

variable (S Λ : Type*) [Fintype S] [CommRing Λ]

/-- `Σ_s m_s r_s` as a bilinear form on `S → Λ`. -/
def dotL : (S → Λ) →ₗ[Λ] (S → Λ) →ₗ[Λ] Λ :=
  LinearMap.mk₂ Λ (fun m r => m ⬝ᵥ r) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

/-- The constant functions `S → Λ`. -/
def constSub : Submodule Λ (S → Λ) := Submodule.span Λ {1}

/-- The functions `S → Λ` of sum `0`. -/
def sumKer : Submodule Λ (S → Λ) := LinearMap.ker (dotL S Λ 1)

/-- The residue pairing `(S → Λ)/Λ × ker(Σ) → Λ`. -/
def resPair : ((S → Λ) ⧸ constSub S Λ) →ₗ[Λ] sumKer S Λ →ₗ[Λ] Λ :=
  pairQuotSub (dotL S Λ) (constSub S Λ) (sumKer S Λ) (fun m hm r hr => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have hr' : (1 : S → Λ) ⬝ᵥ (r : S → Λ) = 0 := hr
    change (c • (1 : S → Λ)) ⬝ᵥ r = 0
    rw [smul_dotProduct, hr', smul_zero])

variable {S Λ}

@[simp] theorem dotL_apply (m r : S → Λ) : dotL S Λ m r = ∑ s, m s * r s := rfl

theorem mem_sumKer (r : S → Λ) : r ∈ sumKer S Λ ↔ ∑ s, r s = 0 := by
  simp [sumKer, dotL_apply]

omit [Fintype S] in
theorem mem_constSub (m : S → Λ) : m ∈ constSub S Λ ↔ ∃ c : Λ, ∀ s, m s = c := by
  rw [constSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, fun s => by simp⟩
  · rintro ⟨c, hc⟩; exact ⟨c, funext fun s => by simp [hc s]⟩

@[simp] theorem resPair_mk (m : S → Λ) (r : sumKer S Λ) :
    resPair S Λ (Submodule.Quotient.mk m) r = ∑ s, m s * (r : S → Λ) s := rfl

theorem dotProductEquiv_symm_dot [DecidableEq S] (ψ : Dual Λ (S → Λ)) (r : S → Λ) :
    (dotProductEquiv Λ S).symm ψ ⬝ᵥ r = ψ r := by
  have h := LinearMap.congr_fun (LinearEquiv.apply_symm_apply (dotProductEquiv Λ S) ψ) r
  exact h

/-- The residue pairing is perfect. -/
theorem resPair_isPerfPair : (resPair S Λ).IsPerfPair := by
  classical
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.Quotient.mk_eq_zero, mem_constSub]
    rcases isEmpty_or_nonempty S with hS | ⟨⟨s0⟩⟩
    · exact ⟨0, fun s => isEmptyElim s⟩
    · refine ⟨m s0, fun s => ?_⟩
      have hr : (Pi.single s 1 - Pi.single s0 1 : S → Λ) ∈ sumKer S Λ := by
        change (1 : S → Λ) ⬝ᵥ (Pi.single s 1 - Pi.single s0 1) = 0
        simp [dotProduct_sub, dotProduct_single]
      have := LinearMap.congr_fun hq ⟨_, hr⟩
      change m ⬝ᵥ (Pi.single s 1 - Pi.single s0 1) = 0 at this
      simp only [dotProduct_sub, dotProduct_single, mul_one] at this
      exact sub_eq_zero.1 this
  · intro φ
    rcases isEmpty_or_nonempty S with hS | ⟨⟨s0⟩⟩
    · refine ⟨0, ?_⟩
      ext ⟨r, hr⟩
      have : (⟨r, hr⟩ : sumKer S Λ) = 0 := Subtype.ext (funext fun s => isEmptyElim s)
      rw [this]; simp
    · let pr : (S → Λ) →ₗ[Λ] (S → Λ) :=
        LinearMap.id - (dotL S Λ 1).smulRight (Pi.single s0 1 : S → Λ)
      have hpr : ∀ r, pr r ∈ sumKer S Λ := fun r => by
        change (1 : S → Λ) ⬝ᵥ (r - ((1 : S → Λ) ⬝ᵥ r) • Pi.single s0 1) = 0
        simp [dotProduct_sub, dotProduct_smul, dotProduct_single]
      let ψ : Dual Λ (S → Λ) := φ.comp (LinearMap.codRestrict (sumKer S Λ) pr hpr)
      refine ⟨Submodule.Quotient.mk ((dotProductEquiv Λ S).symm ψ), ?_⟩
      ext ⟨r, hr⟩
      have hr' : (1 : S → Λ) ⬝ᵥ r = 0 := hr
      change (dotProductEquiv Λ S).symm ψ ⬝ᵥ r = φ ⟨r, hr⟩
      rw [dotProductEquiv_symm_dot]
      change φ ⟨pr r, hpr r⟩ = φ ⟨r, hr⟩
      congr 1
      apply Subtype.ext
      change r - ((1 : S → Λ) ⬝ᵥ r) • Pi.single s0 1 = r
      rw [hr', zero_smul, sub_zero]
  · rw [injective_iff_map_eq_zero]
    rintro ⟨r, hr⟩ hq
    apply Subtype.ext
    funext s
    have := LinearMap.congr_fun hq (Submodule.Quotient.mk (Pi.single s 1))
    change Pi.single s 1 ⬝ᵥ r = 0 at this
    simpa [single_dotProduct] using this
  · intro ψ
    let ψ' : Dual Λ (S → Λ) := ψ.comp (constSub S Λ).mkQ
    let r := (dotProductEquiv Λ S).symm ψ'
    have hr : r ∈ sumKer S Λ := by
      change (1 : S → Λ) ⬝ᵥ r = 0
      rw [dotProduct_comm, dotProductEquiv_symm_dot]
      change ψ (Submodule.Quotient.mk 1) = 0
      have h1 : (Submodule.Quotient.mk (1 : S → Λ) : (S → Λ) ⧸ constSub S Λ) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
      rw [h1, map_zero]
    refine ⟨⟨r, hr⟩, ?_⟩
    refine Submodule.linearMap_qext _ (LinearMap.ext fun m => ?_)
    change m ⬝ᵥ r = ψ (Submodule.Quotient.mk m)
    rw [dotProduct_comm, dotProductEquiv_symm_dot]
    rfl

end Residue

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_Cup =====
section

/-!
# S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone

For an equivariant bilinear `β : M × M' → L`, `ρ'` with open kernel and `H²(Γ, L) = 0` (`H2Van σ Γ ⊤`):
for `(c, m) ∈ Z1c` and `d ∈ Z1` choose `u` with `δu = c ∪ d` (`(c ∪ d)(g, h) = β (c g) (g · d h)`), and put
`cup((c, m), d) := [s ↦ (g ↦ β m_s (d g) - u g)|_{Γ ⊓ I s}] ∈ H2K σ Γ I`. It is independent of `u`, bilinear,
and vanishes on `B1c` and on `B1`: `cupPair : H1c ρ Γ I →ₗ H1 ρ' Γ →ₗ H2K σ Γ I`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {M' : Type} [AddCommGroup M'] [Module k M']
  {L : Type} [AddCommGroup L] [Module k L]
  (ρ : Representation k G M) (ρ' : Representation k G M') (σ : Representation k G L)
  (β : M →ₗ[k] M' →ₗ[k] L) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The cup product of 1-cochains, `(c ∪ d)(g, h) = β (c g) (g · d h)`. -/
def cupCochain (c : Γ → M) (d : Γ → M') : Γ × Γ → L := fun x => β (c x.1) (ρ' x.1 (d x.2))

/-- `u` is a primitive of `c ∪ d`: `c ∪ d = δu` (locally constant). -/
def IsPrim (c : Γ → M) (d : Γ → M') (u : Γ → L) : Prop :=
  IsLocallyConstant u ∧ ∀ g h : Γ, cupCochain ρ' β Γ c d (g, h) = σ g (u h) - u (g * h) + u g

/-- The boundary cochains `g ↦ β m_s (d g) - u g` on `Γ ⊓ I s`. -/
def cupBd (p : (Γ → M) × (S → M)) (d : Γ → M') (u : Γ → L) (s : S) : ↥(Γ ⊓ I s) → L :=
  fun g => β (p.2 s) (d ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) - u ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩

variable {ρ ρ' σ β Γ I}

/-! ## Bilinearity -/

theorem prim_add_left {c₁ c₂ : Γ → M} {d : Γ → M'} {u₁ u₂ : Γ → L} (h₁ : IsPrim ρ' σ β Γ c₁ d u₁)
    (h₂ : IsPrim ρ' σ β Γ c₂ d u₂) : IsPrim ρ' σ β Γ (c₁ + c₂) d (u₁ + u₂) := by
  refine ⟨h₁.1.add h₂.1, fun g h => ?_⟩
  have a : β (c₁ g) (ρ' g (d h)) = σ g (u₁ h) - u₁ (g * h) + u₁ g := h₁.2 g h
  have b : β (c₂ g) (ρ' g (d h)) = σ g (u₂ h) - u₂ (g * h) + u₂ g := h₂.2 g h
  show β (c₁ g + c₂ g) (ρ' g (d h)) = σ g (u₁ h + u₂ h) - (u₁ (g * h) + u₂ (g * h)) + (u₁ g + u₂ g)
  simp only [map_add, LinearMap.add_apply]
  rw [a, b]; abel

theorem prim_smul_left (a : k) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (h : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ (a • c) d (a • u) := by
  refine ⟨h.1.comp (a • ·), fun g j => ?_⟩
  have e : β (c g) (ρ' g (d j)) = σ g (u j) - u (g * j) + u g := h.2 g j
  show β (a • c g) (ρ' g (d j)) = σ g (a • u j) - a • u (g * j) + a • u g
  simp only [map_smul, LinearMap.smul_apply]
  rw [e, smul_add, smul_sub]

theorem prim_add_right {c : Γ → M} {d₁ d₂ : Γ → M'} {u₁ u₂ : Γ → L} (h₁ : IsPrim ρ' σ β Γ c d₁ u₁)
    (h₂ : IsPrim ρ' σ β Γ c d₂ u₂) : IsPrim ρ' σ β Γ c (d₁ + d₂) (u₁ + u₂) := by
  refine ⟨h₁.1.add h₂.1, fun g h => ?_⟩
  have a : β (c g) (ρ' g (d₁ h)) = σ g (u₁ h) - u₁ (g * h) + u₁ g := h₁.2 g h
  have b : β (c g) (ρ' g (d₂ h)) = σ g (u₂ h) - u₂ (g * h) + u₂ g := h₂.2 g h
  show β (c g) (ρ' g (d₁ h + d₂ h)) = σ g (u₁ h + u₂ h) - (u₁ (g * h) + u₂ (g * h)) + (u₁ g + u₂ g)
  simp only [map_add]
  rw [a, b]; abel

theorem prim_smul_right (a : k) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (h : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ c (a • d) (a • u) := by
  refine ⟨h.1.comp (a • ·), fun g j => ?_⟩
  have e : β (c g) (ρ' g (d j)) = σ g (u j) - u (g * j) + u g := h.2 g j
  show β (c g) (ρ' g (a • d j)) = σ g (a • u j) - a • u (g * j) + a • u g
  simp only [map_smul]
  rw [e, smul_add, smul_sub]

/-! ## Vanishing on coboundaries -/

/-! ## The cup product on cohomology -/

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_ConeDuality_Const =====
section

/-!
# S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block

Constant coefficients: `M = k` with the trivial action, `M' = L = k` with a twist `σ` that is trivial on `Γ`,
`β = mul`. Under the abstract tame-inertia / residue hypotheses `ConstData σ Γ I t` (`t s` generates tame inertia):
* `h2kEquiv : H2K σ Γ I hσ ≃ₗ[k] k`, `[e] ↦ Σ_s e_s(t_s)`;
* `constPair H D : H1c (trivial) Γ I →ₗ H1 σ Γ →ₗ k` (cup product, then `h2kEquiv`); `constPair_mk`;
* `constPair_bdry`: on boundary classes `[(0, m)]` it is `Σ_s m_s d(t_s)`; `constPair_h0`: zero on `im × H1par`;
* `blockA_isPerfPair`: the block `im(k^S → H¹_c) × H¹/H¹_par → k` is the residue pairing `resPair`, so perfect;
* `constPair_isPerfPair`: `constPair` is perfect once the parabolic block `H¹_c/im × H¹_par → k` is (O5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation k G k) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (t : (s : S) → ↥(Γ ⊓ I s))

variable {Γ I} in
/-- `t s ∈ Γ ⊓ I s`, viewed in `Γ`. -/
def tG (s : S) : Γ := ⟨(t s).1, (Subgroup.mem_inf.1 (t s).2).1⟩

variable [Fintype S]

/-- Constant-coefficient data: `σ` trivial on `Γ`; `Hom(Γ ⊓ I s, k) ≅ k` by evaluation at `t s`; the residue
theorem `Σ_s d(t_s) = 0` on `Z¹(Γ, k(1))` and its converse (divisibility of `Pic⁰`). -/
structure ConstData : Prop where
  triv : ∀ (g : Γ) (x : k), σ g x = x
  inj : ∀ (s : S) (e : Z1 σ (Γ ⊓ I s)), (e : ↥(Γ ⊓ I s) → k) (t s) = 0 → e = 0
  surj : ∀ (s : S) (a : k), ∃ e : Z1 σ (Γ ⊓ I s), (e : ↥(Γ ⊓ I s) → k) (t s) = a
  resSum : ∀ d : Z1 σ Γ, ∑ s, (d : Γ → k) (tG t s) = 0
  resOnto : ∀ r : S → k, ∑ s, r s = 0 → ∃ d : Z1 σ Γ, ∀ s, (d : Γ → k) (tG t s) = r s

/-- `e ↦ Σ_s e_s(t_s)` on `Π_s Z¹(Γ ⊓ I s, k)`. -/
def evalSum : ((s : S) → Z1 σ (Γ ⊓ I s)) →ₗ[k] k where
  toFun e := ∑ s, (e s : ↥(Γ ⊓ I s) → k) (t s)
  map_add' e e' := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a e := by
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem evalSum_apply (e : (s : S) → Z1 σ (Γ ⊓ I s)) :
    evalSum σ Γ I t e = ∑ s, (e s : ↥(Γ ⊓ I s) → k) (t s) := rfl

variable {σ Γ I t}

/-! ## The pairing and its boundary block -/

variable (Γ I) in
theorem zero_mem_Z1c (m : S → k) : ((0 : Γ → k), m) ∈ Z1c (Representation.trivial k G k) Γ I :=
  ⟨(Z1 _ Γ).zero_mem, fun s g _ => by simp⟩

variable (Γ I) in
/-- `k^S → H¹_c(Ū, k)`, `m ↦ [(0, m)]`. -/
def bdryMap : (S → k) →ₗ[k] H1c (Representation.trivial k G k) Γ I :=
  H1c.mk (Representation.trivial k G k) Γ I ∘ₗ
    LinearMap.codRestrict (Z1c (Representation.trivial k G k) Γ I) (LinearMap.inr k (Γ → k) (S → k))
      (zero_mem_Z1c Γ I)

theorem bdryMap_apply (m : S → k) :
    bdryMap (k := k) Γ I m =
      H1c.mk (Representation.trivial k G k) Γ I ⟨((0 : Γ → k), m), zero_mem_Z1c Γ I m⟩ := rfl

variable [Nonempty S]

theorem par_eval (D : ConstData σ Γ I t) {d : Z1 σ Γ} (hd : (d : Γ → k) ∈ Z1par σ Γ I) (s : S) :
    (d : Γ → k) (tG t s) = 0 := by
  obtain ⟨-, hd'⟩ := hd
  obtain ⟨b, hb⟩ := hd' s
  rw [hb (tG t s) (Subgroup.mem_inf.1 (t s).2).2, D.triv, sub_self]

/-! ## Residues `H¹(Ū, k(1)) / H¹_par → ker Σ` -/

variable (σ t) in
/-- Residues `d ↦ (d(t_s))_s`. -/
def resZ : Z1 σ Γ →ₗ[k] (S → k) := LinearMap.pi fun s => LinearMap.proj (tG t s) ∘ₗ (Z1 σ Γ).subtype

/-- Residues land in `ker Σ` (residue theorem). -/
def resZ' (D : ConstData σ Γ I t) : Z1 σ Γ →ₗ[k] sumKer S k :=
  LinearMap.codRestrict (sumKer S k) (resZ σ t) (fun d => (mem_sumKer _).2 (D.resSum d))

/-- Residues on `H¹(Γ, k(1))`. -/
def resH (D : ConstData σ Γ I t) : H1 σ Γ →ₗ[k] sumKer S k :=
  ((B1 σ Γ).comap (Z1 σ Γ).subtype).liftQ (resZ' D) (by
    intro d hd
    obtain ⟨-, b, hb⟩ := hd
    rw [LinearMap.mem_ker]
    refine Subtype.ext (funext fun s => ?_)
    show (d : Γ → k) (tG t s) = 0
    rw [show (d : Γ → k) (tG t s) = σ (tG t s : G) b - b from hb (tG t s), D.triv, sub_self])

theorem resH_mk (D : ConstData σ Γ I t) (d : Z1 σ Γ) : resH D (H1.mk σ Γ d) = resZ' D d := rfl

theorem resH_surjective (D : ConstData σ Γ I t) : Function.Surjective (resH D) := by
  rintro ⟨r, hr⟩
  obtain ⟨d, hd⟩ := D.resOnto r ((mem_sumKer r).1 hr)
  exact ⟨H1.mk σ Γ d, Subtype.ext (funext hd)⟩

variable (k Γ I) in
theorem ker_bdryMap : LinearMap.ker (bdryMap (k := k) Γ I) = constSub S k := by
  ext m
  rw [LinearMap.mem_ker, mem_constSub, bdryMap_apply, H1c.mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  constructor
  · rintro ⟨-, c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨zero_mem_Z1c Γ I m, c, fun g => by simp, hc⟩

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_ConeDuality_ConstRes =====
section

/-!
# S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses

`constData_of_resHyp`: the residue input `ResHyp` of S4-PD, taken for the trivial quotient `π : G → PUnit`
(so `Λ[Gf] = k`), gives `ConstData σ Γ I H.sg` for any `σ` that is trivial on `Γ`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `Λ[PUnit] ≅ Λ`. -/
abbrev unitE (k : Type) [CommRing k] : MonoidAlgebra k PUnit ≃+* k :=
  MonoidAlgebra.uniqueRingEquiv (R := k) (M := PUnit)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `σ` trivial on `Γ` is trivial on `Γ ⊓ I s`. -/
theorem triv_inf {σ : Representation k G k} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
    (htriv : ∀ (g : Γ) (x : k), σ g x = x) (s : S) : ∀ (g : ↥(Γ ⊓ I s)) (x : k), σ g x = x :=
  fun g x => htriv ⟨g, (Subgroup.mem_inf.1 g.2).1⟩ x

variable (σ : Representation k G k) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map (1 : G →* PUnit))] [∀ s, Fintype ((Γ ⊓ I s).map (1 : G →* PUnit))]

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_ConeDuality_Frob =====
section

/-!
# S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing

* `frobH2c_eq_smul`: on `H²_c` with one-dimensional coefficients `σ : Representation k G k`, Frobenius
  `frobH2c σ Γ ψ χ` is the scalar `χ · σ(ψ)(1)` (no hypothesis on `σ`);
* `frobH2K_eq_smul`: hence the same holds on the cone's `H²(K)` as soon as some `k`-linear `E : H²(K) ≃ H²_c`
  intertwines the two Frobenius maps (S4-PD's `h2Equiv_lisse` provides such an `E`);
* `constPair_frob`: if Frobenius is the scalar `c` on `H²(K)`, the constant-coefficient pairing satisfies
  `⟨F x, F y⟩ = c · ⟨x, y⟩`; `constPair_frob_of_equiv` with `c = χ · σ(ψ)(1)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-- A map conjugate (through a linear equivalence) to a scalar is that scalar. -/
theorem eq_smul_of_conj {k : Type} [CommRing k] {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (E : A ≃ₗ[k] B) {FA : A →ₗ[k] A} {FB : B →ₗ[k] B} {c : k} (hE : ∀ x, E (FA x) = FB (E x))
    (hB : ∀ y, FB y = c • y) (x : A) : FA x = c • x :=
  E.injective (by rw [hE, hB, map_smul])

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation k G k) (Γ : Subgroup G) [Γ.Normal]

/-- On `H²_c` with one-dimensional coefficients, Frobenius is the scalar `χ · σ(ψ)(1)`. -/
theorem frobH2c_eq_smul (ψ : G) (χ : k) (z : H2c σ Γ) : frobH2c σ Γ ψ χ z = (χ * σ ψ 1) • z := by
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  have hx : σ ψ x = σ ψ 1 • x := by
    rw [smul_eq_mul, mul_comm]
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul x (1 : k), map_smul, smul_eq_mul]
  rw [frobH2c_mk, hx, map_smul, smul_smul]

variable {S : Type} (I : S → Subgroup G)

variable [Fintype S] [Nonempty S] {σ Γ I} {t : (s : S) → ↥(Γ ⊓ I s)}

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtSheaves_GalGen =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`

For a finite Galois subextension `L ⊆ K_U` unramified over `A` and its cover `C = coverOf L`
(`B` = integral closure of `A` in `L`, `G = Gal(L/K)`), restriction is a hom `resL : π₁ = Gal(K_U/K) →* G`
(`resL_spec`). The embedding `K_U → κ(η)^sep` of `GenBr` gives a lift `lGen : Spec κ(η)^sep → Spec B` of the
generic geometric point `η̄` (`hlGen`), and for it `galFV = resL ∘ genToPi1` (`galFV_gen`). Hence the Galois
representation on `(F_V)_η̄` is `ρ ∘ resL ∘ genToPi1` (`stalkFVGen_galRep`): it factors through `π₁`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
variable (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

theorem le_maxUnram (hL' : L ∈ unramSet A K) : L ≤ maxUnram A K := by
  rw [maxUnram_eq_sSup]
  exact le_sSup hL'

/-- Restriction `π₁ = Gal(K_U/K) →* Gal(L/K)`, the group of `coverOf L`. -/
def resL : Pi1 A K →* (coverOf A K L hL).G :=
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  AlgEquiv.restrictNormalHom L

theorem resL_spec (τ : Pi1 A K) (x : L) :
    IntermediateField.inclusion (le_maxUnram A K L hL) ((show L ≃ₐ[K] L from resL A K L hL τ) x) =
      τ (IntermediateField.inclusion (le_maxUnram A K L hL) x) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact τ.restrictNormal_commutes L x

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]
  (ρ : Representation Λ (coverOf A K L hL).G V)

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_GalSurj =====
section

/-!
# S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf

For `π₁ = Pi1 A K = Gal(K_U/K)` and a finite unramified Galois `L ⊆ K_U` with cover `C = coverOf L`:
* `resL_surjective`, `isOpen_ker_resL`: restriction `resL : π₁ ↠ Gal(L/K)` is onto with open kernel;
* `exists_resL_ker_le`: every open subgroup of `π₁` contains `ker resL` for some such `L`;
* `factorRep`: a representation `ρ'` of `π₁` with `ker resL ≤ ker ρ'` factors as `ρ ∘ resL` (`factorRep_resL`);
* `isOpen_ker_piRep`: for every `G`-module `V`, the `π₁`-representation `ρ ∘ resL` has open kernel;
* **`exists_lisse_of_rep`**: a representation of `π₁` on a finite `Λ`-module with open kernel is, up to
  isomorphism of the stalk, the Galois representation on the generic stalk `(F_V)_η̄` of the lisse sheaf `F_V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]

theorem resL_surjective (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    Function.Surjective (resL A K L hL) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact AlgEquiv.restrictNormalHom_surjective (maxUnram A K)

/-- `σ ∈ ker resL` iff `σ` fixes the image of `L`. -/
theorem resL_eq_one_of_fix (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
    (σ : Pi1 A K) (h : ∀ y : L, σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
      IntermediateField.inclusion (le_maxUnram A K L hL) y) :
    resL A K L hL σ = 1 := by
  show (show L ≃ₐ[K] L from resL A K L hL σ) = 1
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.one_apply]
  exact Subtype.ext (congrArg (fun z : maxUnram A K => (z : AlgebraicClosure K))
    ((resL_spec A K L hL σ y).trans (h y)))

theorem fix_of_resL_eq_one (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
    (σ : Pi1 A K) (hσ : resL A K L hL σ = 1) (y : L) :
    σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
      IntermediateField.inclusion (le_maxUnram A K L hL) y := by
  have h1 : (show L ≃ₐ[K] L from resL A K L hL σ) = 1 := hσ
  rw [← resL_spec A K L hL σ y, h1, AlgEquiv.one_apply]

/-- `ker (π₁ ↠ Gal(L/K))` is open: it contains the fixing group of the finite extension `L ⊆ K_U`. -/
theorem isOpen_ker_resL (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    IsOpen ((resL A K L hL).ker : Set (Pi1 A K)) := by
  haveI := hL.1
  haveI : FiniteDimensional K (IntermediateField.restrict (le_maxUnram A K L hL)) :=
    (IntermediateField.restrictAlgEquiv (le_maxUnram A K L hL)).toLinearEquiv.finiteDimensional
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.restrict (le_maxUnram A K L hL)).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  refine resL_eq_one_of_fix A K L hL σ fun y => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    ((IntermediateField.mem_restrict (le_maxUnram A K L hL) _).2 y.2)

/-- **Every open subgroup of `π₁` contains `ker (π₁ ↠ Gal(L/K))` for a finite unramified Galois `L`.** -/
theorem exists_resL_ker_le (N : Subgroup (Pi1 A K)) (hN : IsOpen (N : Set (Pi1 A K))) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K), (resL A K L hL).ker ≤ N := by
  classical
  obtain ⟨E, hE, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff K (maxUnram A K) N).mp (hN.mem_nhds N.one_mem)
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr hE
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
    (htfin.toFinset.image (fun x : maxUnram A K => (x : AlgebraicClosure K))) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2)
  refine ⟨L, hL, ?_⟩
  intro σ hσ
  have hσ' : resL A K L hL σ = 1 := MonoidHom.mem_ker.mp hσ
  apply hEN
  have hgen : ∀ x ∈ t, σ x = x := by
    intro x hx
    have hxL : (x : AlgebraicClosure K) ∈ L := by
      apply hle
      apply IntermediateField.subset_adjoin
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hx, rfl⟩)
    have hx' : x = IntermediateField.inclusion (le_maxUnram A K L hL) ⟨x, hxL⟩ := Subtype.ext rfl
    rw [hx']
    exact fix_of_resL_eq_one A K L hL σ hσ' ⟨x, hxL⟩
  have hEfix : E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← hadj, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hgen x hx, ih (Subgroup.zpow_mem_zpowers σ _)]
    | pred n ih =>
      have hinv : σ⁻¹ x = x := by
        conv_lhs => rw [← hgen x hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih (Subgroup.zpow_mem_zpowers σ _)]
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hEfix hx) σ (Subgroup.mem_zpowers σ)

variable {A K} (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]

/-- A representation of `π₁` killed by `ker resL` descends to `Gal(L/K)`. -/
def factorRep (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker) :
    Representation Λ (coverOf A K L hL).G V :=
  (QuotientGroup.lift (resL A K L hL).ker ρ' hk).comp
    (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm.toMonoidHom

theorem factorRep_resL (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker)
    (σ : Pi1 A K) : factorRep L hL Λ ρ' hk (resL A K L hL σ) = ρ' σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm
      (resL A K L hL σ) = (σ : Pi1 A K ⧸ (resL A K L hL).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [factorRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

theorem factorRep_comp (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker) :
    (factorRep L hL Λ ρ' hk).comp (resL A K L hL) = ρ' :=
  MonoidHom.ext (factorRep_resL L hL Λ ρ' hk)

variable (A K)

end RamanujanPetersson.EtSheaves.TorSec

end

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

open CurveCoh Kummer CP4a
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

end S3

end

end PerfectCx
end RamanujanPetersson


end

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

open CurveCoh Kummer CP4a PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section Abstract

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)}

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

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysA =====
section

/-!
# S4-CurveDuality O4G-1: the Gysin count for a unipotent family

Route G (session 44). On `V = (ι → k) × (ι → k)` let `Γ` act by `(a, b) ↦ (a + (d_i g · b_i)_i, b)` (`IsUniFam`) with
parabolic `d_i` (zero on every `Γ ⊓ I s`). If every `d_i` is in the right kernel of `constPair`, the cone's `H²(K)`
has at least `#(ι → k)²` elements (`card_sq_le_h2K`); the coinvariants of `V` have fewer than `#V` elements as soon as
some `d_i ≠ 0` (`card_coinv_lt`). With `H²(K) ≃ H²_c` (S4-PD) this forces `d = 0`.
* `card_sq_le_quot`: an abstract count (`(a₁, a₂) ↦ [z₁ a₁ + z₂ a₂]` is injective);
* `rho_inf`, `cx1_inf`: the action and `d¹` on `Γ ⊓ I s`; `zmk`: a cocycle on `Γ ⊓ I s` with a prescribed value;
* `snd_mem_Z1`, `prim_fst`: the components of a `V`-cocycle, and the primitive `C₁ - C₂ d` of `C₂ ∪ d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-- An abstract count: `p₂` onto and killing `B ⊔ Z'`, `p₁` onto on `Z'` and killing `B ⊓ Z'`. -/
theorem card_sq_le_quot {k Z A : Type} [CommRing k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    (B Z' : Submodule k Z) (p1 p2 : Z →ₗ[k] A) (h2 : Function.Surjective p2)
    (h1 : ∀ a, ∃ z ∈ Z', p1 z = a) (hB2 : ∀ z ∈ B, p2 z = 0) (hZ2 : ∀ z ∈ Z', p2 z = 0)
    (hB1 : ∀ z ∈ B, z ∈ Z' → p1 z = 0) [Finite (Z ⧸ B)] :
    Nat.card A * Nat.card A ≤ Nat.card (Z ⧸ B) := by
  classical
  choose z1 hz1 hp1 using h1
  choose z2 hp2 using h2
  have hinj : Function.Injective (fun a : A × A => (Submodule.Quotient.mk (z1 a.1 + z2 a.2) : Z ⧸ B)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    have h' : (z1 a1 + z2 a2) - (z1 b1 + z2 b2) ∈ B := (Submodule.Quotient.eq B).1 h
    have hm := hB2 _ h'
    rw [map_sub, map_add, map_add, hp2, hp2, hZ2 _ (hz1 a1), hZ2 _ (hz1 b1), zero_add, zero_add,
      sub_eq_zero] at hm
    subst hm
    have hd : z1 a1 - z1 b1 ∈ B := by
      have : (z1 a1 + z2 a2) - (z1 b1 + z2 a2) = z1 a1 - z1 b1 := by abel
      rwa [this] at h'
    have h0 := hB1 _ hd (Z'.sub_mem (hz1 a1) (hz1 b1))
    rw [map_sub, hp1, hp1, sub_eq_zero] at h0
    rw [h0]
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

section Gys

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {ι : Type} [Fintype ι]

/-- `Γ` acts on `(ι → k) × (ι → k)` by `(a, b) ↦ (a + (d_i g · b_i)_i, b)`. -/
def IsUniFam (ρ : Representation k G ((ι → k) × (ι → k))) (d : ι → Γ → k) : Prop :=
  ∀ (g : Γ) (v : (ι → k) × (ι → k)), ρ (g : G) v = (v.1 + fun i => d i g * v.2 i, v.2)

variable {ρ : Representation k G ((ι → k) × (ι → k))} {d : ι → Γ → k}

theorem rho_inf (hρΓ : IsUniFam ρ d) (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (s : S)
    (g : ↥(Γ ⊓ I s)) (v : (ι → k) × (ι → k)) : ρ (g : G) v = v := by
  have h0 : ∀ i, d i ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ = 0 := fun i => hpar i s _ (Subgroup.mem_inf.1 g.2).2
  have := hρΓ ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ v
  refine this.trans ?_
  ext i <;> simp [h0]

/-- `g ↦ e(g) • v` is a cocycle on `Γ ⊓ I s` (`e` a hom, the action trivial there). -/
def zmk (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0)
    (s : S) (e : Z1 σ (Γ ⊓ I s)) (v : (ι → k) × (ι → k)) : Z1 ρ (Γ ⊓ I s) :=
  ⟨fun g => (e : ↥(Γ ⊓ I s) → k) g • v, (mem_Z1 ρ _ _).2 ⟨((mem_Z1 σ _ _).1 e.2).1.comp (· • v), fun g h => by
    rw [((mem_Z1 σ _ _).1 e.2).2 g h, DD.triv ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, rho_inf hρΓ hpar s g, add_smul]⟩⟩

theorem zmk_apply (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (s : S) (e : Z1 σ (Γ ⊓ I s)) (v : (ι → k) × (ι → k))
    (g : ↥(Γ ⊓ I s)) :
    (zmk DD hρΓ hpar s e v : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g = (e : ↥(Γ ⊓ I s) → k) g • v := rfl

variable (ρ t) in
/-- `z ↦ Σ_s r(z_s(t_s))`. -/
def prR (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] (ι → k) where
  toFun z := ∑ s, r ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) (t s))
  map_add' z z' := by simp [Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.smul_sum]

theorem prR_apply (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) (z : (s : S) → Z1 ρ (Γ ⊓ I s)) :
    prR t ρ r z = ∑ s, r ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) (t s)) := rfl

variable (ρ I) in
/-- Boundary families with vanishing second component. -/
def zSnd0 : Submodule k ((s : S) → Z1 ρ (Γ ⊓ I s)) where
  carrier := {z | ∀ (s : S) (g : ↥(Γ ⊓ I s)), ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g).2 = 0}
  add_mem' := by
    intro z z' hz hz' s g
    simp [hz s g, hz' s g]
  zero_mem' := fun s g => by simp
  smul_mem' := by
    intro a z hz s g
    simp [hz s g]

theorem mem_zSnd0 (z : (s : S) → Z1 ρ (Γ ⊓ I s)) : z ∈ zSnd0 I ρ ↔
    ∀ (s : S) (g : ↥(Γ ⊓ I s)), ((z s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g).2 = 0 := Iff.rfl

/-- The `i`-th second component of a `V`-cocycle is a hom, i.e. lies in `Z¹(Γ, k(1))`. -/
theorem snd_mem_Z1 (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (C : Z1 ρ Γ) (i : ι) :
    (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) ∈ Z1 σ Γ := by
  refine (mem_Z1 σ Γ _).2 ⟨((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i), fun g h => ?_⟩
  rw [((mem_Z1 ρ Γ _).1 C.2).2 g h, DD.triv g, hρΓ g]
  rfl

theorem snd_mem_Z1_triv (hρΓ : IsUniFam ρ d) (C : Z1 ρ Γ) (i : ι) :
    (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) ∈ Z1 (Representation.trivial k G k) Γ := by
  refine (mem_Z1 _ Γ _).2 ⟨((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i), fun g h => ?_⟩
  rw [((mem_Z1 ρ Γ _).1 C.2).2 g h, Representation.trivial_apply, hρΓ g]
  rfl

/-- `C₁ - C₂ d` is a primitive of `C₂ ∪ d` (componentwise). -/
theorem prim_fst (DD : ConstData σ Γ I t) (hρΓ : IsUniFam ρ d) (hd : ∀ i, d i ∈ Z1 σ Γ) (C : Z1 ρ Γ) (i : ι) :
    IsPrim σ σ (LinearMap.mul k k) Γ (fun g => ((C : Γ → (ι → k) × (ι → k)) g).2 i) (d i)
      (fun g => ((C : Γ → (ι → k) × (ι → k)) g).1 i - ((C : Γ → (ι → k) × (ι → k)) g).2 i * d i g) := by
  have hC := ((mem_Z1 ρ Γ _).1 C.2).2
  have hdi := ((mem_Z1 σ Γ _).1 (hd i)).2
  refine ⟨(((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.1 i)).sub
    ((((mem_Z1 ρ Γ _).1 C.2).1.comp (fun v => v.2 i)).mul ((mem_Z1 σ Γ _).1 (hd i)).1), fun g h => ?_⟩
  simp only [cupCochain, LinearMap.mul_apply', DD.triv]
  have e1 : ((C : Γ → (ι → k) × (ι → k)) (g * h)).1 i =
      ((C : Γ → (ι → k) × (ι → k)) g).1 i + ((C : Γ → (ι → k) × (ι → k)) h).1 i +
        d i g * ((C : Γ → (ι → k) × (ι → k)) h).2 i := by
    rw [hC g h, hρΓ g]
    simp only [Prod.fst_add, Pi.add_apply]
    ring
  have e2 : ((C : Γ → (ι → k) × (ι → k)) (g * h)).2 i =
      ((C : Γ → (ι → k) × (ι → k)) g).2 i + ((C : Γ → (ι → k) × (ι → k)) h).2 i := by
    rw [hC g h, hρΓ g]
    rfl
  have e3 : d i (g * h) = d i g + d i h := by rw [hdi g h, DD.triv]
  rw [e1, e2, e3]
  ring

variable [DecidableEq S] [Nonempty S]

omit [DecidableEq S] [Nonempty S] in
/-- The coinvariants are smaller than `V` as soon as some `d_i ≠ 0`. -/
theorem card_coinv_lt [Finite k] (hρΓ : IsUniFam ρ d) {i : ι} {g : Γ} (hg : d i g ≠ 0) :
    Nat.card (H2c ρ Γ) < Nat.card ((ι → k) × (ι → k)) := by
  classical
  let v : (ι → k) × (ι → k) := (0, Pi.single i 1)
  have hw : (ρ.comp Γ.subtype) g v - v ∈ Representation.Coinvariants.ker (ρ.comp Γ.subtype) :=
    Representation.Coinvariants.sub_mem_ker g v
  have hne : (ρ.comp Γ.subtype) g v - v ≠ 0 := by
    intro h
    have h1 := congrArg (fun w : (ι → k) × (ι → k) => w.1 i) h
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hρΓ g, v] at h1
    simp at h1
    exact hg h1
  have hK : 1 < Nat.card (Representation.Coinvariants.ker (ρ.comp Γ.subtype)) := by
    have : Nontrivial (Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
      ⟨⟨⟨_, hw⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hcard := Submodule.card_eq_card_quotient_mul_card (Representation.Coinvariants.ker (ρ.comp Γ.subtype))
  have hQ : Nat.card (H2c ρ Γ) =
      Nat.card (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) := rfl
  have hfin : Finite (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hpos : 0 < Nat.card (((ι → k) × (ι → k)) ⧸ Representation.Coinvariants.ker (ρ.comp Γ.subtype)) :=
    Nat.card_pos
  rw [hQ, hcard]
  exact lt_mul_of_one_lt_left hpos hK

end Gys

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysC =====
section

/-!
# S4-CurveDuality O4G-3: coinducing a unipotent character

Route G (session 44). Let `Γ ⊴ G` and `d : Γ → k` additive, zero on `Γ ∩ N` for an open normal `N` of finite index.
Coinduce the unipotent representation `v ↦ (v.1 + d g * v.2, v.2)` of `Γ` along `Γ → G ⧸ N` (Mathlib's
`Representation.coind`) and pull it back to `G`. In the coordinates `f ↦ (f(r_i))_i` at representatives `r_i` of
`(G ⧸ N) ⧸ Γ̄` this is a representation on `(ι → k) × (ι → k)` with open kernel on which `Γ` acts unipotently through
the conjugates `g ↦ d(r_i g r_i⁻¹)` (`exists_coind`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

section Uni

variable {k : Type} [CommRing k] {G : Type} [Group G] {Γ : Subgroup G}

theorem d_one {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) : d 1 = 0 := by
  have := hd 1 1
  rw [mul_one] at this
  linear_combination -this

theorem d_inv {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) (a : Γ) : d a⁻¹ = -d a := by
  have := hd a⁻¹ a
  rw [inv_mul_cancel, d_one hd] at this
  linear_combination -this

/-- The unipotent representation `v ↦ (v.1 + d g * v.2, v.2)` of `Γ` attached to an additive `d`. -/
def uni2 (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) : Representation k Γ (k × k) where
  toFun g :=
    { toFun := fun v => (v.1 + d g * v.2, v.2)
      map_add' := fun v w => by
        refine Prod.ext ?_ rfl
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := fun c v => by
        refine Prod.ext ?_ rfl
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := LinearMap.ext fun v => by
    refine Prod.ext ?_ rfl
    simp [d_one hd]
  map_mul' g h := LinearMap.ext fun v => by
    refine Prod.ext ?_ rfl
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, hd]
    ring

theorem uni2_apply (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) (g : Γ) (v : k × k) :
    uni2 d hd g v = (v.1 + d g * v.2, v.2) := rfl

theorem uni2_congr {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) {g h : Γ} (e : d g = d h) :
    uni2 d hd g = uni2 d hd h :=
  LinearMap.ext fun v => by rw [uni2_apply, uni2_apply, e]

end Uni

section Coind

variable {k : Type} [CommRing k] {G : Type} [Group G] (Γ N : Subgroup G) [N.Normal]

/-- `Γ → G ⧸ N`. -/
abbrev phiN : Γ →* G ⧸ N := (QuotientGroup.mk' N).comp Γ.subtype

/-- The index set: `(G ⧸ N) ⧸ Γ̄`. -/
abbrev Cos : Type := (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)

/-- A representative in `G` of a coset `i`. -/
def repG (i : Cos Γ N) : G := Quotient.out (Quotient.out i : G ⧸ N)

theorem repG_spec (i : Cos Γ N) :
    (QuotientGroup.mk (QuotientGroup.mk (repG Γ N i) : G ⧸ N) : Cos Γ N) = i := by
  unfold repG
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq']

theorem phi_mem (γ : Γ) : phiN Γ N γ ∈ Γ.map (QuotientGroup.mk' N) := Subgroup.mem_map_of_mem _ γ.2

variable {Γ N} in
theorem d_eq_of_phi {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) {a b : Γ} (h : phiN Γ N a = phiN Γ N b) : d a = d b := by
  have h' : (QuotientGroup.mk (a : G) : G ⧸ N) = QuotientGroup.mk (b : G) := h
  have hm : ((a⁻¹ * b : Γ) : G) ∈ N := QuotientGroup.eq.1 h'
  have h0 := hdN _ hm
  rw [hd, d_inv hd] at h0
  linear_combination -h0

theorem exists_gam [hΓ : Γ.Normal] (x : G ⧸ N) :
    ∃ γ : Γ, phiN Γ N γ * (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N) = x := by
  have hn : (Γ.map (QuotientGroup.mk' N)).Normal := hΓ.map _ (QuotientGroup.mk'_surjective N)
  have h := repG_spec Γ N (QuotientGroup.mk x)
  have h2 := hn.mem_comm (QuotientGroup.eq.1 h)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h2
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [show phiN Γ N ⟨y, hy⟩ = _ from hyx, inv_mul_cancel_right]

/-- The `Γ`-part of `x = γ̄ · r_{[x]}`. -/
def gam [Γ.Normal] (x : G ⧸ N) : Γ := Classical.choose (exists_gam Γ N x)

theorem gam_spec [Γ.Normal] (x : G ⧸ N) :
    phiN Γ N (gam Γ N x) * (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N) = x :=
  Classical.choose_spec (exists_gam Γ N x)

/-- The coinduced function with prescribed values `v` at the representatives. -/
def extF [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b)
    (v : (Cos Γ N → k) × (Cos Γ N → k)) (x : G ⧸ N) : k × k :=
  uni2 d hd (gam Γ N x) (v.1 (QuotientGroup.mk x), v.2 (QuotientGroup.mk x))

theorem extF_mem [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (v : (Cos Γ N → k) × (Cos Γ N → k)) :
    extF Γ N d hd v ∈ Representation.coindV (phiN Γ N) (uni2 d hd) := by
  have hn : (Γ.map (QuotientGroup.mk' N)).Normal := hΓ.map _ (QuotientGroup.mk'_surjective N)
  rw [Representation.mem_coindV]
  intro γ0 x
  have hc : (QuotientGroup.mk (phiN Γ N γ0 * x) : Cos Γ N) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    have := hn.conj_mem _ (inv_mem (phi_mem Γ N γ0)) x⁻¹
    convert this using 1
    group
  have hy := gam_spec Γ N (phiN Γ N γ0 * x)
  have hx := gam_spec Γ N x
  rw [hc] at hy
  have hφ : phiN Γ N (gam Γ N (phiN Γ N γ0 * x)) = phiN Γ N (γ0 * gam Γ N x) := by
    apply mul_right_cancel (b := (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N))
    rw [hy, map_mul, mul_assoc, hx]
  simp only [extF]
  rw [hc, uni2_congr hd (d_eq_of_phi hd hdN hφ), map_mul, Module.End.mul_apply]

theorem extF_rep [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (v : (Cos Γ N → k) × (Cos Γ N → k)) (i : Cos Γ N) :
    extF Γ N d hd v (QuotientGroup.mk (repG Γ N i)) = (v.1 i, v.2 i) := by
  have hi := repG_spec Γ N i
  have hy := gam_spec Γ N (QuotientGroup.mk (repG Γ N i))
  rw [hi] at hy
  have h1 : phiN Γ N (gam Γ N (QuotientGroup.mk (repG Γ N i))) = phiN Γ N 1 := by
    rw [map_one]
    exact mul_right_cancel (hy.trans (one_mul _).symm)
  simp only [extF]
  rw [hi, uni2_congr hd (d_eq_of_phi hd hdN h1), map_one]
  rfl

/-- Evaluation at the representatives. -/
def evalW [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Representation.coindV (phiN Γ N) (uni2 d hd) →ₗ[k] (Cos Γ N → k) × (Cos Γ N → k) where
  toFun f := (fun i => ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).1,
    fun i => ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalW_inj [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Function.Injective (evalW Γ N d hd) := by
  intro f g hfg
  have hr : ∀ i, (f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i)) =
      (g : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i)) := fun i =>
    Prod.ext (congrFun (congrArg Prod.fst hfg) i) (congrFun (congrArg Prod.snd hfg) i)
  apply Subtype.ext
  funext x
  have hx := gam_spec Γ N x
  rw [← hx, (Representation.mem_coindV _ _ _).1 f.2, (Representation.mem_coindV _ _ _).1 g.2, hr]

theorem evalW_surj [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : Function.Surjective (evalW Γ N d hd) := by
  intro v
  refine ⟨⟨extF Γ N d hd v, extF_mem Γ N hd hdN v⟩, ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrArg Prod.fst (extF_rep Γ N hd hdN v i)
  · exact congrArg Prod.snd (extF_rep Γ N hd hdN v i)

/-- The coordinate equivalence. -/
def eW [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) :
    Representation.coindV (phiN Γ N) (uni2 d hd) ≃ₗ[k] (Cos Γ N → k) × (Cos Γ N → k) :=
  LinearEquiv.ofBijective (evalW Γ N d hd) ⟨evalW_inj Γ N d hd, evalW_surj Γ N hd hdN⟩

theorem eW_fst [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (f : Representation.coindV (phiN Γ N) (uni2 d hd))
    (i : Cos Γ N) : (eW Γ N hd hdN f).1 i = ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).1 := rfl

theorem eW_snd [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (f : Representation.coindV (phiN Γ N) (uni2 d hd))
    (i : Cos Γ N) : (eW Γ N hd hdN f).2 i = ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).2 := rfl

/-- The coinduced representation, pulled back to `G`. -/
def rhoW (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Representation k G (Representation.coindV (phiN Γ N) (uni2 d hd)) :=
  (Representation.coind (phiN Γ N) (uni2 d hd)).comp (QuotientGroup.mk' N)

theorem rhoW_apply (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) (g : G)
    (f : Representation.coindV (phiN Γ N) (uni2 d hd)) (x : G ⧸ N) :
    ((rhoW Γ N d hd g f : Representation.coindV (phiN Γ N) (uni2 d hd)) : G ⧸ N → k × k) x =
      (f : G ⧸ N → k × k) (x * QuotientGroup.mk g) := rfl

/-- The coinduced representation in coordinates. -/
def rhoV [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : Representation k G ((Cos Γ N → k) × (Cos Γ N → k)) where
  toFun g := (eW Γ N hd hdN).toLinearMap ∘ₗ rhoW Γ N d hd g ∘ₗ (eW Γ N hd hdN).symm.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp

theorem rhoV_apply [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (g : G) (v : (Cos Γ N → k) × (Cos Γ N → k)) :
    rhoV Γ N hd hdN g v = eW Γ N hd hdN (rhoW Γ N d hd g ((eW Γ N hd hdN).symm v)) := rfl

theorem le_ker_rhoV [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : N ≤ (rhoV Γ N hd hdN).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  have h1 : rhoW Γ N d hd n = 1 := by
    have : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    simp only [rhoW, MonoidHom.comp_apply, this, map_one]
  refine LinearMap.ext fun v => ?_
  rw [rhoV_apply, h1, Module.End.one_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply]

theorem rhoW_conj [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) (g : Γ)
    (f : Representation.coindV (phiN Γ N) (uni2 d hd)) (i : Cos Γ N) :
    ((rhoW Γ N d hd g f : Representation.coindV (phiN Γ N) (uni2 d hd)) : G ⧸ N → k × k)
        (QuotientGroup.mk (repG Γ N i)) =
      uni2 d hd ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩
        ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))) := by
  rw [rhoW_apply]
  have : (QuotientGroup.mk (repG Γ N i) : G ⧸ N) * QuotientGroup.mk (g : G) =
      phiN Γ N ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩ *
        QuotientGroup.mk (repG Γ N i) := by
    show _ = (QuotientGroup.mk (repG Γ N i * g * (repG Γ N i)⁻¹) : G ⧸ N) * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, inv_mul_cancel_right]
  rw [this, (Representation.mem_coindV _ _ _).1 f.2]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isUniFam_rhoV [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) [Fintype (Cos Γ N)] :
    IsUniFam (rhoV Γ N hd hdN) (fun i (g : Γ) => d ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩) := by
  intro g v
  obtain ⟨f, rfl⟩ := (eW Γ N hd hdN).surjective v
  rw [rhoV_apply, LinearEquiv.symm_apply_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrArg Prod.fst (rhoW_conj Γ N hd g f i)
  · have h := congrArg Prod.snd (rhoW_conj Γ N hd g f i)
    exact h

end Coind

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysE =====
section

/-!
# S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation

Route G (session 44). `InR H DD d`: `d` is a parabolic cocycle (a hom, `σ` trivial on `Γ`) in the right kernel of
`constPair`. If `⟨F x, F y⟩ = c ⟨x, y⟩` with `c` a unit (`F` = Frobenius of `φ⁻¹`), then `InR d` implies
`InR (d ∘ conjΓ φ)` (`inR_conj`): `F [d ∘ conjΓ φ] = σ(φ⁻¹)(1) · [d]`, so `c ⟨x, [d ∘ conjΓ φ]⟩ = 0`; parabolicity
uses a boundary compatibility of `φ`. Iterating gives `d ∘ conjΓ φ^j` (`inR_conj_pow`). Conjugation by `Γ · N`
(`N ∩ Γ ⊆ ker d`, `N` normal) does not change `d` (`d_conj_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

/-- `σ(g)(1)` is a unit for a representation on the ring itself. -/
theorem isUnit_rep_one {k : Type} [CommRing k] {G : Type} [Group G] (σ : Representation k G k) (g : G) :
    IsUnit (σ g 1) := by
  refine IsUnit.of_mul_eq_one (σ g⁻¹ 1) ?_
  have h : σ g (σ g⁻¹ 1) = 1 := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one σ, Module.End.one_apply]
  calc σ g 1 * σ g⁻¹ 1 = σ g⁻¹ 1 • σ g 1 := by rw [smul_eq_mul, mul_comm]
    _ = σ g (σ g⁻¹ 1 • 1) := (map_smul _ _ _).symm
    _ = 1 := by rw [smul_eq_mul, mul_one, h]

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

theorem add_of_Z1 (htriv : ∀ (g : Γ) (x : k), σ g x = x) {d : Γ → k} (hd : d ∈ Z1 σ Γ) (a b : Γ) :
    d (a * b) = d a + d b := by
  rw [hd.2, htriv]

theorem conj_conj_inv (φ : G) (g : Γ) : conjΓ Γ φ (conjΓ Γ φ⁻¹ g) = g :=
  Subtype.ext (by simp only [conjΓ_val]; group)

/-- **O4G-5c.** Conjugation by `γ n` (`γ ∈ Γ`, `n ∈ N`, `N ∩ Γ ⊆ ker d`) does not change `d`. -/
theorem d_conj_mul (htriv : ∀ (g : Γ) (x : k), σ g x = x) {d : Γ → k} (hd : d ∈ Z1 σ Γ) (N : Subgroup G)
    [hN : N.Normal] (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (ψ : G) {γ : G} (hγ : γ ∈ Γ) {n : G}
    (hn : n ∈ N) (g : Γ) : d (conjΓ Γ (ψ * γ * n) g) = d (conjΓ Γ ψ g) := by
  have hadd := add_of_Z1 htriv hd
  have hγ' : ((⟨γ, hγ⟩ : Γ) : G) = γ := rfl
  have h1 : d ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩) = d (conjΓ Γ ψ g) := by
    rw [hadd, hadd, d_inv hadd]
    ring
  have hw : ((conjΓ Γ (ψ * γ * n) g * ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩)⁻¹ : Γ) : G) ∈ N := by
    have e : ((conjΓ Γ (ψ * γ * n) g * ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩)⁻¹ : Γ) : G) =
        n⁻¹ * ((((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩ : Γ) : G) * n *
          ((((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩ : Γ) : G))⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjΓ_val]
      group
    rw [e]
    exact N.mul_mem (N.inv_mem hn) (hN.conj_mem n hn _)
  have h2 := hdN _ hw
  rw [hadd, d_inv hadd] at h2
  linear_combination h2 + h1

end Gen

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

open CurveCoh Kummer CP4a PerfectCx
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

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_LamSep =====
section

/-!
# S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings

* `exists_zmod_hom_ne_zero`: an `N`-torsion abelian group is separated by homomorphisms to `ℤ/N`;
* `span_of_zmod`: if the `ℤ/N`-valued parabolic homomorphisms have a dual basis `χ_i`, `e_i`, then every
  `k`-valued one (`k` a `ℤ/N`-algebra) is `x g = Σ_i χ_i(g) x(e_i)`;
* `isPerfPair_toLinearMap₂'`: the pairing `(v, w) ↦ v ⬝ (A w)` on `R^n` is perfect for invertible `A`;
  `exists_inv_of_isPerfPair`: a perfect matrix pairing has an invertible matrix; `map_mul_eq_one`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

section Sep

variable {N : ℕ} [NeZero N] {A : Type*} [AddCommGroup A]

end Sep

section Span

variable {N : ℕ} [NeZero N] {k : Type*} [CommRing k] (ι : ZMod N →+* k)

theorem nsmul_eq_zero_of_hom (ι : ZMod N →+* k) (a : k) : N • a = 0 := by
  rw [nsmul_eq_mul, ← map_natCast ι N, ZMod.natCast_self, map_zero, zero_mul]

theorem zmod_hom_map_mul (ψ : k →+ ZMod N) (c : ZMod N) (y : k) : ψ (ι c * y) = c * ψ y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c, map_natCast, ← nsmul_eq_mul, map_nsmul]
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- Locally constant homomorphisms `Γ → A` vanishing on the elements satisfying `P` (parabolic homs). -/
def IsParHom {A : Type*} [AddCommGroup A] (P : Γ → Prop) (x : Γ → A) : Prop :=
  IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + x h) ∧ ∀ g, P g → x g = 0

theorem IsParHom.comp {A B : Type*} [AddCommGroup A] [AddCommGroup B] {P : Γ → Prop} {x : Γ → A}
    (hx : IsParHom P x) (ψ : A →+ B) : IsParHom P (fun g => ψ (x g)) :=
  ⟨hx.1.comp ψ, fun g h => by show ψ (x (g * h)) = ψ (x g) + ψ (x h); rw [hx.2.1, map_add],
    fun g hg => by show ψ (x g) = 0; rw [hx.2.2 g hg, map_zero]⟩

end Span

section Mat

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem toLinearMap₂'_eq_dot (A : Matrix n n R) (v w : n → R) :
    Matrix.toLinearMap₂' R A v w = (v ᵥ* A) ⬝ᵥ w := by
  rw [Matrix.toLinearMap₂'_apply', dotProduct_mulVec]

theorem toLinearMap₂'_single (A : Matrix n n R) (v : n → R) (j : n) :
    Matrix.toLinearMap₂' R A v (Pi.single j (1 : R)) = (v ᵥ* A) j := by
  rw [toLinearMap₂'_eq_dot, dotProduct_single, mul_one]

theorem bijective_toLinearMap₂' {A B : Matrix n n R} (hBA : B * A = 1) (hAB : A * B = 1) :
    Function.Bijective (Matrix.toLinearMap₂' R A : (n → R) →ₗ[R] (n → R) →ₗ[R] R) := by
  refine ⟨fun v v' h => ?_, fun φ => ?_⟩
  · have h2 : v ᵥ* A = v' ᵥ* A := funext fun j => by
      rw [← toLinearMap₂'_single, ← toLinearMap₂'_single, h]
    calc v = v ᵥ* A ᵥ* B := by rw [vecMul_vecMul, hAB, vecMul_one]
      _ = v' ᵥ* A ᵥ* B := by rw [h2]
      _ = v' := by rw [vecMul_vecMul, hAB, vecMul_one]
  · refine ⟨(fun j => φ (fun i => if j = i then 1 else 0)) ᵥ* B, LinearMap.ext fun w => ?_⟩
    rw [toLinearMap₂'_eq_dot, vecMul_vecMul, hBA, vecMul_one, LinearMap.pi_apply_eq_sum_univ φ w,
      dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]

/-- The matrix pairing of an invertible matrix is perfect. -/
theorem isPerfPair_toLinearMap₂' {A B : Matrix n n R} (hBA : B * A = 1) (hAB : A * B = 1) :
    (Matrix.toLinearMap₂' R A).IsPerfPair :=
  LinearMap.IsPerfPair.of_bijective _ (bijective_toLinearMap₂' hBA hAB)

/-- A perfect matrix pairing has an invertible matrix. -/
theorem exists_inv_of_isPerfPair {A : Matrix n n R} (h : (Matrix.toLinearMap₂' R A).IsPerfPair) :
    ∃ B : Matrix n n R, B * A = 1 ∧ A * B = 1 := by
  have hs := (LinearMap.IsPerfPair.bijective_left (Matrix.toLinearMap₂' R A)).2
  choose v hv using fun j : n => hs (LinearMap.proj j)
  have hBA : Matrix.of (fun j i => v j i) * A = 1 := by
    ext j l
    have h1 := LinearMap.congr_fun (hv j) (Pi.single l (1 : R))
    rw [toLinearMap₂'_single, LinearMap.proj_apply, Pi.single_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
    simp only [Matrix.of_apply, Matrix.vecMul, dotProduct]
  exact ⟨_, hBA, mul_eq_one_comm.1 hBA⟩

theorem map_mul_eq_one {S : Type*} [CommRing S] (ι : R →+* S) {A B : Matrix n n R} (h : B * A = 1) :
    B.map ι * A.map ι = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one ι (map_zero ι) (map_one ι)]

/-- Perfectness of a matrix pairing is preserved by a ring homomorphism. -/
theorem isPerfPair_map {S : Type*} [CommRing S] (ι : R →+* S) {A : Matrix n n R}
    (h : (Matrix.toLinearMap₂' R A).IsPerfPair) : (Matrix.toLinearMap₂' S (A.map ι)).IsPerfPair := by
  obtain ⟨B, hBA, hAB⟩ := exists_inv_of_isPerfPair h
  exact isPerfPair_toLinearMap₂' (map_mul_eq_one ι hBA) (map_mul_eq_one ι hAB)

end Mat

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_LamCoord =====
section

/-!
# S4-CurveDuality O5d-2: coordinates on the parabolic block

Constant coefficients (`σ` trivial on `Γ`). Given `ℤ/N`-valued parabolic homomorphisms `χ_i` (vanishing on every
boundary inertia group), a dual family `e_j` (`χ_i(e_j) = δ_ij`) whose coordinates span all `ℤ/N`-valued parabolic
homomorphisms, and a ring hom `ι : ℤ/N → k`:
* `eR : k^r ≃ H¹_par(Γ, k(1))`, `λ ↦ [Σ λ_i ι∘χ_i]`;
* `eL : k^r ≃ H¹_c(Γ, k) / im(k^S)`, `λ ↦ [(Σ λ_i ι∘χ_i, 0)]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

variable {N : ℕ} [NeZero N] {k : Type} [CommRing k] (ι : ZMod N →+* k)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G} {r : ℕ} (χ : Fin r → Γ → ZMod N)
  {e : Fin r → Γ}

variable (I) in
/-- `g ∈ Γ` lies in some boundary inertia group. -/
def InBdry (g : Γ) : Prop := ∃ s, (g : G) ∈ I s

/-- `λ ↦ Σ_i λ_i ι(χ_i)`. -/
def parHomL : (Fin r → k) →ₗ[k] (Γ → k) where
  toFun l g := ∑ i, l i * ι (χ i g)
  map_add' l l' := funext fun g => by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a l := funext fun g => by simp [Finset.mul_sum, mul_assoc]

theorem parHomL_apply (l : Fin r → k) (g : Γ) : parHomL ι χ l g = ∑ i, l i * ι (χ i g) := rfl

variable {ι χ}

theorem parHomL_e (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) (l : Fin r → k) (j : Fin r) :
    parHomL ι χ l (e j) = l j := by
  rw [parHomL_apply, Finset.sum_eq_single j]
  · rw [hδ, if_pos rfl, map_one, mul_one]
  · intro i _ hij
    rw [hδ, if_neg hij, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem parHomL_isParHom (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (l : Fin r → k) :
    IsParHom (InBdry I) (parHomL ι χ l) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun i => (hχ i).1.eventually_eq x).mono fun y hy => ?_, fun g h => ?_,
    fun g hg => ?_⟩
  · simp only [parHomL_apply, hy]
  · have ha : ∀ i, χ i (g * h) = χ i g + χ i h := fun i => (hχ i).2.1 g h
    simp only [parHomL_apply, ha, map_add, mul_add, Finset.sum_add_distrib]
  · have h0 : ∀ i, χ i g = 0 := fun i => (hχ i).2.2 g hg
    simp only [parHomL_apply, h0, map_zero, mul_zero, Finset.sum_const_zero]

variable {σ : Representation k G k}

theorem mem_Z1_of_isParHom {P : Γ → Prop} (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : IsParHom P x) : x ∈ Z1 σ Γ :=
  (mem_Z1 σ Γ x).2 ⟨hx.1, fun g h => by rw [htriv, hx.2.1]⟩

theorem mem_Z1par_of_isParHom (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : IsParHom (InBdry I) x) : x ∈ Z1par σ Γ I :=
  ⟨mem_Z1_of_isParHom htriv hx, fun s => ⟨0, fun g hg => by
    rw [map_zero, sub_zero]
    exact hx.2.2 g ⟨s, hg⟩⟩⟩

theorem isParHom_of_mem_Z1par (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : x ∈ Z1par σ Γ I) : IsParHom (InBdry I) x := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hlc, hco⟩ := (mem_Z1 σ Γ x).1 hx1
  refine ⟨hlc, fun g h => by rw [hco, htriv], fun g ⟨s, hg⟩ => ?_⟩
  obtain ⟨b, hb⟩ := hx2 s
  rw [hb g hg, htriv, sub_self]

theorem mem_Z1c_of_isParHom {x : Γ → k} (hx : IsParHom (InBdry I) x) (m : S → k) :
    (x, m) ∈ Z1c (Representation.trivial k G k) Γ I :=
  ⟨mem_Z1_of_isParHom (fun _ _ => rfl) hx, fun s g hg => by
    rw [Representation.trivial_apply, sub_self]
    exact hx.2.2 g ⟨s, hg⟩⟩

theorem isParHom_of_mem_Z1c {p : (Γ → k) × (S → k)} (hp : p ∈ Z1c (Representation.trivial k G k) Γ I) :
    IsParHom (InBdry I) p.1 := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hlc, hco⟩ := (mem_Z1 _ Γ _).1 hp1
  refine ⟨hlc, fun g h => by rw [hco, Representation.trivial_apply], fun g ⟨s, hg⟩ => ?_⟩
  rw [hp2 s g hg, Representation.trivial_apply, sub_self]

theorem mk_mem_H1par {z : Z1 σ Γ} (hz : (z : Γ → k) ∈ Z1par σ Γ I) : H1.mk σ Γ z ∈ H1par σ Γ I :=
  Submodule.mem_map_of_mem (Submodule.mem_comap.2 hz)

variable (ι)

/-- `λ ↦ Σ λ_i ι∘χ_i ∈ Z¹(Γ, k(1))`. -/
def parZ1 (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] Z1 σ Γ :=
  LinearMap.codRestrict _ (parHomL ι χ) fun l => mem_Z1_of_isParHom htriv (parHomL_isParHom hχ l)

/-- `λ ↦ [Σ λ_i ι∘χ_i] ∈ H¹_par`. -/
def eRlin (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] H1par σ Γ I :=
  LinearMap.codRestrict _ (H1.mk σ Γ ∘ₗ parZ1 ι htriv hχ) fun l =>
    mk_mem_H1par (mem_Z1par_of_isParHom htriv (parHomL_isParHom hχ l))

theorem eRlin_injective (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) : Function.Injective (eRlin ι htriv hχ) := by
  refine (injective_iff_map_eq_zero _).2 fun l hl => funext fun j => ?_
  have h1 : H1.mk σ Γ (parZ1 ι htriv hχ l) = 0 := congrArg Subtype.val hl
  rw [H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨-, m, hm⟩ := h1
  have h2 : parHomL ι χ l (e j) = σ (e j : G) m - m := hm (e j)
  rw [htriv, sub_self, parHomL_e hδ] at h2
  exact h2

/-- `λ ↦ (Σ λ_i ι∘χ_i, 0) ∈ Z¹_c(Γ, k)`. -/
def parZ1c (hχ : ∀ i, IsParHom (InBdry I) (χ i)) : (Fin r → k) →ₗ[k] Z1c (Representation.trivial k G k) Γ I :=
  LinearMap.codRestrict _ (LinearMap.inl k (Γ → k) (S → k) ∘ₗ parHomL ι χ) fun l =>
    mem_Z1c_of_isParHom (parHomL_isParHom hχ l) 0

theorem parZ1c_snd (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (l : Fin r → k) :
    (parZ1c ι hχ l : (Γ → k) × (S → k)).2 = 0 := rfl

/-- `λ ↦ [(Σ λ_i ι∘χ_i, 0)] ∈ H¹_c / im(k^S)`. -/
def eLlin (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] H1c (Representation.trivial k G k) Γ I ⧸ LinearMap.range (bdryMap (k := k) Γ I) :=
  (LinearMap.range (bdryMap (k := k) Γ I)).mkQ ∘ₗ H1c.mk _ Γ I ∘ₗ parZ1c ι hχ

theorem eLlin_injective (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) : Function.Injective (eLlin ι hχ) := by
  refine (injective_iff_map_eq_zero _).2 fun l hl => funext fun j => ?_
  have h1 : H1c.mk (Representation.trivial k G k) Γ I (parZ1c ι hχ l) ∈ LinearMap.range (bdryMap (k := k) Γ I) :=
    (Submodule.Quotient.mk_eq_zero _).1 hl
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h1
  rw [bdryMap_apply, H1c.mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    Submodule.mem_comap] at hm
  obtain ⟨-, m', hm', -⟩ := hm
  have h2 : (0 : k) - parHomL ι χ l (e j) = Representation.trivial k G k (e j : G) m' - m' := hm' (e j)
  rw [Representation.trivial_apply, sub_self, zero_sub, neg_eq_zero, parHomL_e hδ] at h2
  exact h2

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_LamPerf =====
section

/-!
# S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`

In the coordinates `eL`, `eR` of `LamCoord`, the parabolic block of the constant pairing at any coefficient ring
`k ← ℤ/N` is the matrix pairing of `ι(M)`, `M_ij = -Σ_s U_ij(t_s)` (`U_ij` primitives of `χ_i ∪ χ_j` over `ℤ/N`).
Hence perfectness over `ℤ/N` (an invertible `M`) gives perfectness over every `Λ` (`parabolic_of_zmod`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

variable {N : ℕ} [NeZero N] {k : Type} [CommRing k] (ι : ZMod N →+* k)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}
  {r : ℕ} {χ : Fin r → Γ → ZMod N} {e : Fin r → Γ}

/-- Level-`ℤ/N` primitives: `χ_i(g) χ_j(h) = U_ij(h) - U_ij(gh) + U_ij(g)`, `U_ij` locally constant. -/
def IsPrimFam (χ : Fin r → Γ → ZMod N) (U : Fin r → Fin r → Γ → ZMod N) : Prop :=
  ∀ i j, IsLocallyConstant (U i j) ∧ ∀ g h, χ i g * χ j h = U i j h - U i j (g * h) + U i j g

variable (t) in
/-- The intersection matrix `M_ij = -Σ_s U_ij(t_s)`. -/
def lamMat (U : Fin r → Fin r → Γ → ZMod N) : Matrix (Fin r) (Fin r) (ZMod N) :=
  Matrix.of fun i j => -∑ s, U i j (tG t s)

/-- The level-`k` primitive `Σ_ij λ_i μ_j ι(U_ij)`. -/
def primL (U : Fin r → Fin r → Γ → ZMod N) (l μ : Fin r → k) (g : Γ) : k :=
  ∑ i, ∑ j, l i * (μ j * ι (U i j g))

theorem isPrim_primL {σ : Representation k G k} (htriv : ∀ (g : Γ) (x : k), σ g x = x)
    {U : Fin r → Fin r → Γ → ZMod N} (hU : IsPrimFam χ U) (l μ : Fin r → k) :
    IsPrim σ σ (LinearMap.mul k k) Γ (parHomL ι χ l) (parHomL ι χ μ) (primL ι U l μ) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hU i j).1.eventually_eq x).mono
      fun y hy => ?_, fun g h => ?_⟩
  · simp only [primL, hy]
  · simp only [cupCochain, LinearMap.mul_apply', htriv, parHomL_apply, primL, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := congrArg ι ((hU i j).2 g h)
    simp only [map_mul, map_add, map_sub] at this
    linear_combination (l i * μ j) * this

variable [Nonempty S]

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_ParZ =====
section

/-!
# S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel

`exists_dualBasis`: an additive `(ℤ/N)^r ≃ P` onto a group `P` of homomorphisms `Γ → ℤ/N` gives `χ_i = Ψ(δ_i)`
with dual elements `e_j ∈ Γ` (`χ_i(e_j) = δ_ij`) spanning `P` (the evaluation `Γ → (ℤ/N)^r` is onto: a character
of `(ℤ/N)^r` killing its image is a relation among the `χ_i`). `parabolic_of_rightKer`: with such a dual basis
of the parabolic homomorphisms, a zero right kernel of `constPair` over `ℤ/N` makes the intersection matrix
injective, hence invertible over the finite ring `ℤ/N`, so the parabolic block is perfect.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh Matrix

noncomputable section

section Basis

variable {N : ℕ} [NeZero N] {Γ : Type*} [Group Γ] {r : ℕ}

/-- The standard vector `δ_i`. -/
def stdV (i : Fin r) : Fin r → ZMod N := fun j => if i = j then 1 else 0

theorem addHom_apply_sum {B : Type*} [AddCommGroup B] [Module (ZMod N) B] (f : (Fin r → ZMod N) →+ B)
    (v : Fin r → ZMod N) : f v = ∑ i, v i • f (stdV i) :=
  LinearMap.pi_apply_eq_sum_univ (f.toZModLinearMap N) v

variable (P : AddSubgroup (Γ → ZMod N)) (Ψ : (Fin r → ZMod N) ≃+ P)

/-- `χ_i := Ψ(δ_i)`. -/
def chiOf (i : Fin r) : Γ → ZMod N := (Ψ (stdV i) : Γ → ZMod N)

theorem chiOf_mem (i : Fin r) : chiOf P Ψ i ∈ P := (Ψ (stdV i)).2

theorem psi_apply (v : Fin r → ZMod N) (g : Γ) : (Ψ v : Γ → ZMod N) g = ∑ i, v i * chiOf P Ψ i g :=
  addHom_apply_sum ((Pi.evalAddMonoidHom (fun _ : Γ => ZMod N) g).comp (P.subtype.comp Ψ.toAddMonoidHom)) v

theorem span_of_dual (e : Fin r → Γ) (he : ∀ i j, chiOf P Ψ i (e j) = if i = j then 1 else 0)
    {y : Γ → ZMod N} (hy : y ∈ P) (g : Γ) : y g = ∑ i, y (e i) * chiOf P Ψ i g := by
  classical
  have hv : ∀ x, y x = ∑ i, (Ψ.symm ⟨y, hy⟩) i * chiOf P Ψ i x := fun x => by
    rw [← psi_apply, AddEquiv.apply_symm_apply]
  have he' : ∀ j, y (e j) = (Ψ.symm ⟨y, hy⟩) j := fun j => by
    rw [hv, Finset.sum_eq_single j (fun i _ hij => by rw [he, if_neg hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), he, if_pos rfl, mul_one]
  rw [hv]
  exact Finset.sum_congr rfl fun i _ => by rw [he']

end Basis

section Perf

variable {N : ℕ} [NeZero N] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {r : ℕ} {χ : Fin r → Γ → ZMod N} {e : Fin r → Γ}

end Perf

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_ParS3a =====
section

/-!
# S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)

`parSub I`: the parabolic homomorphisms `Γ → ℤ/N` (locally constant, additive, zero on every `I_s`);
`parEquiv`: `parSub I ≃+ H¹_par(Γ, ℤ/N)` for coefficients trivial on `Γ` (no coboundaries). In the S3 chart,
`H¹_par(π₁^geo, ℤ/lⁿ) ≃ Pic⁰(X̄)[lⁿ]` (Kummer, `exists_kummerPicEquiv`) and `Pic⁰(X̄)[lⁿ] ≃ (ℤ/lⁿ)^(2g)` (Tate
coordinates `tatePicN_bijective` with CB1 divisibility), so `exists_dualBasis` gives `χ_i`, `e_j`
(`exists_parBasis`): the input `hχ hδ hspan` of `LamCoord` / `LamPerf`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a
open scoped Polynomial

section Gen

variable {N : ℕ} [NeZero N] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G}

variable (N Γ I) in
/-- The parabolic homomorphisms `Γ → ℤ/N`. -/
def parSub : AddSubgroup (Γ → ZMod N) where
  carrier := {y | IsParHom (InBdry I) y}
  add_mem' := fun {x y} hx hy => ⟨hx.1.add hy.1, fun a b => by
    simp only [Pi.add_apply, hx.2.1, hy.2.1]
    abel, fun g hg => by simp only [Pi.add_apply, hx.2.2 g hg, hy.2.2 g hg, add_zero]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => (add_zero 0).symm, fun _ _ => rfl⟩
  neg_mem' := fun {x} hx => ⟨hx.1.neg, fun a b => by simp only [Pi.neg_apply, hx.2.1, neg_add],
    fun g hg => by simp only [Pi.neg_apply, hx.2.2 g hg, neg_zero]⟩

theorem mem_parSub (y : Γ → ZMod N) : y ∈ parSub N Γ I ↔ IsParHom (InBdry I) y := Iff.rfl

variable {σ : Representation (ZMod N) G (ZMod N)}

/-- `y ↦ [y] ∈ H¹_par`. -/
def parToH1 (htriv : ∀ (g : Γ) (x : ZMod N), σ g x = x) : parSub N Γ I →+ H1par σ Γ I :=
  AddMonoidHom.mk' (fun y => ⟨H1.mk σ Γ ⟨y, mem_Z1_of_isParHom htriv y.2⟩,
      mk_mem_H1par (mem_Z1par_of_isParHom htriv y.2)⟩)
    (fun x y => Subtype.ext (by
      show H1.mk σ Γ ⟨(x : Γ → ZMod N) + y, _⟩ = H1.mk σ Γ ⟨x, _⟩ + H1.mk σ Γ ⟨y, _⟩
      rw [← map_add]
      rfl))

theorem parToH1_bijective (htriv : ∀ (g : Γ) (x : ZMod N), σ g x = x) :
    Function.Bijective (parToH1 (I := I) htriv) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, ?_⟩
  · have h1 : H1.mk σ Γ ⟨y, mem_Z1_of_isParHom htriv y.2⟩ = 0 := congrArg Subtype.val hy
    rw [H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
    obtain ⟨-, m, hm⟩ := h1
    refine Subtype.ext (funext fun g => ?_)
    have h2 : (y : Γ → ZMod N) g = σ (g : G) m - m := hm g
    rw [htriv, sub_self] at h2
    exact h2
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨⟨z, isParHom_of_mem_Z1par htriv (Submodule.mem_comap.1 hz)⟩, rfl⟩

/-- `parSub I ≃+ H¹_par(Γ, ℤ/N)` for coefficients trivial on `Γ`. -/
def parEquiv (htriv : ∀ (g : Γ) (x : ZMod N), σ g x = x) : parSub N Γ I ≃+ H1par σ Γ I :=
  AddEquiv.ofBijective _ (parToH1_bijective htriv)

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end S3

end

end CupDuality
end RamanujanPetersson


end


