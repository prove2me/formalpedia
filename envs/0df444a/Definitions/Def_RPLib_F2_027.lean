-- Prove2me | Definitions.Def_RPLib_F2_027
-- name    : RPLib_F2_027
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T12:11:17.174879+00:00
-- url     : https://prove2.me/theorems/0b6a72c6-d0b4-497b-bdc6-24073187dd96
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 027 of 70
-- statement:
--   File 027 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
--   * `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
--   * `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
--   * `S4.Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
--   * `S4.Def_RP_Cone_H2`: S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius
--   * `S4.Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
--   * `S4.Def_RP_CupDuality_CupFrob`: S4-CurveDuality O2b: Frobenius compatibility of the cup product
--   * `S4.Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
--   * `S4.Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
--   * `S4.Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
--   * `S4.Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
--   * `S4.Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
--   * `S4.Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
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
import Definitions.Def_RPLib_F2_008
import Definitions.Def_RPLib_F2_024

/-!
# Ramanujan-Petersson curve library (flat edition), file 027 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
* `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
* `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
* `S4.Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
* `S4.Def_RP_Cone_H2`: S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius
* `S4.Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
* `S4.Def_RP_CupDuality_CupFrob`: S4-CurveDuality O2b: Frobenius compatibility of the cup product
* `S4.Def_RP_ConeDuality_Const`: S4-CurveDuality O3: constant coefficients, the cone `H²` and the boundary block
* `S4.Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
* `S4.Def_RP_ConeDuality_Frob`: S4-CurveDuality O6b: Frobenius on the constant-coefficient pairing
* `S4.Def_RP_ConeDuality_S3`: S4-CurveDuality O6c: constant-coefficient duality in the S3 chart
* `S4.Def_RP_CupDuality_GysA`: S4-CurveDuality O4G-1: the Gysin count for a unipotent family
* `S4.Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
* `S4.Def_RP_CupDuality_LamSep`: S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings
* `S4.Def_RP_CupDuality_LamCoord`: S4-CurveDuality O5d-2: coordinates on the parabolic block
* `S4.Def_RP_CupDuality_LamPerf`: S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`
* `S4.Def_RP_CupDuality_ParZ`: S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel
* `S4.Def_RP_CupDuality_ParS3a`: S4-CurveDuality O9-2: a dual basis of the parabolic homomorphisms `π₁^geo → ℤ/lⁿ` (S3 chart)
-/

set_option autoImplicit false

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

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))
  {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

variable [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

/-- The degree-1 square: `iso2 ∘ (d¹ ⊗ M) = d¹_K ∘ iso1`. -/
theorem iso2_map_d1 [Fintype S] [DecidableEq S] (u : Coinvariants ((rho1 Λ π Γ S).tprod τ)) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ) u) =
      cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) (iso1 π Γ S hπ τ hΛ hall u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    refine funext fun s => Subtype.ext (funext fun g => ?_)
    simp only [Coinvariants.map_mk, IntertwiningMap.rTensor_apply, iso1_mk_tmul, iso2_mk_tmul, Phi_mk_tmul,
      d1I_val_apply, cx1_apply, map_sub, LinearMap.sub_apply, act_single_mul, MonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem iso2_comp_d1 [Fintype S] [DecidableEq S] :
    (iso2 π Γ I hπ τ hΛ hallI).toLinearMap ∘ₗ Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ) =
      cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ∘ₗ (iso1 π Γ S hπ τ hΛ hall).toLinearMap :=
  LinearMap.ext (iso2_map_d1 π Γ I hπ τ hΛ hall hallI)

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_FrobIso =====
section

/-!
# S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula

The cone Frobenius (`frob1`, `frob2` of `Def_RP_PerfectCx_Frob`) preserves `ker d¹` (`frobKer`), where it is the
`twistc` operator of `CurveCoh_Pair` (`kerEquivZ1c_frobKer`), so it induces `frobH1c` on `H¹_c` (`frobH1c_kerEquiv`);
it also induces `frobH2K` on `H²(K) = coker d¹`. On the perfect complex `PC` the Frobenius `frobPC` is
`Gf`-equivariant (`frobPC_equiv`) and the identifications `(PC i ⊗ M)_{Gf} ≅ K^i(M)` carry `frobPC i ⊗ id` to the
cone Frobenius with coefficients `τ ∘ π` (`pcIso0_frob`, `pcIso1_frob`, `pcIso2_frob`). Hence (`lefschetz_frob`)
`Tr(F | M) - Tr(F | K¹(M)) + Tr(F | K²(M)) = Σ_c L(frobPC)[c] · Tr(τ(c)⁻¹ | M)` (SGA 4½, *Rapport*).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [Γ.Normal] {S : Type}
  (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hρ : IsOpen (ρ.ker : Set G))

theorem frobH2K_mk (hI : BdryCompat Γ I ψ t h) (e : (s : S) → Z1 ρ (Γ ⊓ I s)) :
    frobH2K ρ Γ I ψ t h hρ hI (Submodule.Quotient.mk e) = Submodule.Quotient.mk (frob2 ρ Γ I ψ t h hI e) :=
  rfl

end H

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

end Model

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

theorem gB0_inv (g : Γ) : gB0 π Γ τ ∘ₗ ((regRep Λ π).comp Γ.subtype) g = gB0 π Γ τ := by
  refine LinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [LinearMap.comp_apply, regRepΓ_apply, gB0_apply, gB0_apply, map_mul, Module.End.mul_apply,
    Representation.asAlgebraHom_single_one]
  exact Coinvariants.mk_self_apply ((τ.comp π).comp Γ.subtype) g _

/-- `⟦a⟧ ⊗ m ↦ ⟦a · m⟧`. -/
def gF : AΓ (Λ := Λ) π Γ ⊗[Λ] M →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  TensorProduct.lift (Coinvariants.lift _ (gB0 π Γ τ) (gB0_inv π Γ τ))

theorem gF_mk_tmul (a : MonoidAlgebra Λ Gf) (m : M) :
    gF π Γ τ (Coinvariants.mk _ a ⊗ₜ m) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

theorem gF_inv (h : Gf) : gF π Γ τ ∘ₗ ((rRepΓ π Γ).tprod τ) h = gF π Γ τ := by
  refine TensorProduct.ext' fun x m => ?_
  induction x using Coinvariants.induction_on with
  | h a =>
    have hinv : τ h⁻¹ (τ h m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, rRepΓ_mk, gF_mk_tmul,
      gF_mk_tmul, map_mul, Module.End.mul_apply, Representation.asAlgebraHom_single_one, hinv]

/-- Forward map `(A_Γ ⊗ M)_{Gf} → M_Γ`. -/
def gFwd : Coinvariants ((rRepΓ π Γ).tprod τ) →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  Coinvariants.lift _ (gF π Γ τ) (gF_inv π Γ τ)

theorem gFwd_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    gFwd π Γ τ (Coinvariants.mk _ (Coinvariants.mk _ a ⊗ₜ m)) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

/-- Balancedness: `⟦⟦b a⟧ ⊗ m⟧ = ⟦⟦b⟧ ⊗ a · m⟧`. -/
theorem gmk_mul_tmul (b a : MonoidAlgebra Λ Gf) (m : M) :
    Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ (b * a) ⊗ₜ m) =
      Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ b ⊗ₜ τ.asAlgebraHom a m) := by
  induction a using MonoidAlgebra.induction_on with
  | of x =>
    rw [Representation.asAlgebraHom_of, of_apply]
    have hb : (Coinvariants.mk ((regRep Λ π).comp Γ.subtype) (b * single x 1) : AΓ (Λ := Λ) π Γ) =
        rRepΓ π Γ x⁻¹ (Coinvariants.mk _ b) := by rw [rRepΓ_mk, inv_inv]
    rw [hb, Coinvariants.mk_inv_tmul]
  | add a a' ha ha' => simp only [mul_add, map_add, add_tmul, ha, ha', LinearMap.add_apply, tmul_add]
  | smul r a ha => simp only [mul_smul_comm, map_smul, ← smul_tmul', ha, LinearMap.smul_apply, tmul_smul]

theorem gBk_inv (g : Γ) :
    (Coinvariants.mk ((rRepΓ π Γ).tprod τ) ∘ₗ TensorProduct.mk Λ (AΓ (Λ := Λ) π Γ) M (Coinvariants.mk _ 1)) ∘ₗ
        ((τ.comp π).comp Γ.subtype) g =
      Coinvariants.mk ((rRepΓ π Γ).tprod τ) ∘ₗ TensorProduct.mk Λ (AΓ (Λ := Λ) π Γ) M (Coinvariants.mk _ 1) := by
  refine LinearMap.ext fun m => ?_
  show Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ 1 ⊗ₜ τ (π (g : G)) m) =
    Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ 1 ⊗ₜ m)
  rw [← Coinvariants.mk_inv_tmul (rRepΓ π Γ) τ, rRepΓ_mk, inv_inv, one_mul]
  have h1 : (Coinvariants.mk ((regRep Λ π).comp Γ.subtype) (single (π (g : G)) 1) : AΓ (Λ := Λ) π Γ) =
      Coinvariants.mk _ 1 := by
    have := Coinvariants.mk_self_apply ((regRep Λ π).comp Γ.subtype) g (1 : MonoidAlgebra Λ Gf)
    rw [← this]
    show _ = Coinvariants.mk _ (single (π (g : G)) 1 * 1)
    rw [mul_one]
  rw [h1]

/-- Backward map `M_Γ → (A_Γ ⊗ M)_{Gf}`, `⟦m⟧ ↦ ⟦⟦1⟧ ⊗ m⟧`. -/
def gBwd : Coinvariants ((τ.comp π).comp Γ.subtype) →ₗ[Λ] Coinvariants ((rRepΓ π Γ).tprod τ) :=
  Coinvariants.lift _ _ (gBk_inv π Γ τ)

theorem gBwd_mk (m : M) :
    gBwd π Γ τ (Coinvariants.mk _ m) = Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ m) := rfl

/-- **`(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`** (`= H²_c` of `CurveCoh`). -/
def coinvG : Coinvariants ((rRepΓ π Γ).tprod τ) ≃ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  LinearEquiv.ofLinearMap (gFwd π Γ τ) (gBwd π Γ τ)
    (Coinvariants.hom_ext (LinearMap.ext fun m => by
      show Coinvariants.mk _ (τ.asAlgebraHom 1 m) = Coinvariants.mk _ m
      rw [map_one, Module.End.one_apply]))
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      induction x using Coinvariants.induction_on with
      | h a =>
        show Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ τ.asAlgebraHom a m) =
          Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ a ⊗ₜ m)
        rw [← gmk_mul_tmul, one_mul]))

theorem coinvG_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    coinvG π Γ τ (Coinvariants.mk _ (Coinvariants.mk _ a ⊗ₜ m)) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

theorem coinvG_symm_mk (m : M) :
    (coinvG π Γ τ).symm (Coinvariants.mk _ m) = Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ m) := rfl

end CoinvG

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_Top =====
section

/-!
# S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact

* `cokRep f`, `cokMk f`: the representation on `coker f` for an intertwining map `f`, and `W → coker f`.
* `coinvCokEquiv`: `((W ⊗ M)_G) / im (V ⊗ M)_G ≃ (coker f ⊗ M)_G` (right exactness of `(· ⊗ M)_G`).
* `topEquiv`: for the perfect complex, `H²(K(M)) = coker d¹_K ≃ (C ⊗ M)_{Gf}` with `C := coker d¹` on `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

section RExact

variable {k G : Type} [CommRing k] [Group G] {V W M : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] [AddCommGroup M] [Module k M] {σ : Representation k G V} {ρ : Representation k G W}
  (f : IntertwiningMap σ ρ) (τ : Representation k G M)

/-- `W → coker f` as an intertwining map. -/
def cokMk : IntertwiningMap ρ (cokRep f) :=
  ⟨(LinearMap.range f.toLinearMap).mkQ, fun _ => LinearMap.ext fun _ => rfl⟩

theorem cokMk_apply (w : W) : cokMk f w = Submodule.Quotient.mk w := rfl

theorem cokMk_map (u : Coinvariants (σ.tprod τ)) :
    Coinvariants.map _ _ ((cokMk f).rTensor τ) (Coinvariants.map _ _ (f.rTensor τ) u) = 0 := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v m =>
    rw [Coinvariants.map_mk, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, IntertwiningMap.rTensor_apply]
    have h0 : cokMk f (f v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨v, rfl⟩)
    rw [h0, zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- `(W ⊗ M)_G / im (V ⊗ M)_G → (coker f ⊗ M)_G`. -/
def cokFwd : (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) →ₗ[k]
    Coinvariants ((cokRep f).tprod τ) :=
  Submodule.liftQ _ (Coinvariants.map _ _ ((cokMk f).rTensor τ)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (cokMk_map f τ u))

/-- The bilinear map `W × M → (W ⊗ M)_G / im`, `(w, m) ↦ [w ⊗ m]`. -/
def cokB : W →ₗ[k] M →ₗ[k] (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  (TensorProduct.mk k W M).compr₂ ((Submodule.mkQ _) ∘ₗ Coinvariants.mk (ρ.tprod τ))

theorem cokB_apply (w : W) (m : M) :
    cokB f τ w m = Submodule.Quotient.mk (Coinvariants.mk (ρ.tprod τ) (w ⊗ₜ m)) := rfl

theorem range_le_ker_cokB : LinearMap.range f.toLinearMap ≤ LinearMap.ker (cokB f τ) := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
  refine LinearMap.mem_ker.2 (LinearMap.ext fun m => ?_)
  rw [cokB_apply, LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (LinearMap.mem_range.2 ⟨Coinvariants.mk _ (v ⊗ₜ m), rfl⟩)

/-- `coker f ⊗ M → (W ⊗ M)_G / im`. -/
def cokT : (W ⧸ LinearMap.range f.toLinearMap) ⊗[k] M →ₗ[k]
    (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  TensorProduct.lift (Submodule.liftQ _ (cokB f τ) (range_le_ker_cokB f τ))

theorem cokT_mk_tmul (w : W) (m : M) :
    cokT f τ (Submodule.Quotient.mk w ⊗ₜ m) = Submodule.Quotient.mk (Coinvariants.mk (ρ.tprod τ) (w ⊗ₜ m)) := rfl

theorem cokT_inv (g : G) : cokT f τ ∘ₗ ((cokRep f).tprod τ) g = cokT f τ := by
  refine TensorProduct.ext' fun x m => ?_
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, quotient_apply, Submodule.mapQ_apply,
    cokT_mk_tmul, cokT_mk_tmul]
  congr 1
  have := Coinvariants.mk_self_apply (ρ.tprod τ) g (w ⊗ₜ m)
  rw [Representation.tprod_apply, TensorProduct.map_tmul] at this
  exact this

/-- `(coker f ⊗ M)_G → (W ⊗ M)_G / im`. -/
def cokBwd : Coinvariants ((cokRep f).tprod τ) →ₗ[k]
    (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  Coinvariants.lift _ (cokT f τ) (cokT_inv f τ)

/-- **Right exactness of `(· ⊗ M)_G`**: `(W ⊗ M)_G / im (V ⊗ M)_G ≃ (coker f ⊗ M)_G`. -/
def coinvCokEquiv : (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) ≃ₗ[k]
    Coinvariants ((cokRep f).tprod τ) :=
  LinearEquiv.ofLinearMap (cokFwd f τ) (cokBwd f τ)
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl))
    (Submodule.linearMap_qext _ (Coinvariants.hom_ext (TensorProduct.ext' fun w m => rfl)))

theorem coinvCokEquiv_mk (w : W) (m : M) :
    coinvCokEquiv f τ (Submodule.Quotient.mk (Coinvariants.mk _ (w ⊗ₜ m))) =
      Coinvariants.mk _ (Submodule.Quotient.mk w ⊗ₜ m) := rfl

end RExact

section Top

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G)) {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)
  [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

include hall in
theorem map_iso2_range_d1 [Fintype S] [DecidableEq S] :
    (LinearMap.range (Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ))).map
        (iso2 π Γ I hπ τ hΛ hallI).toLinearMap =
      LinearMap.range (cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ)) := by
  rw [← LinearMap.range_comp, iso2_comp_d1 π Γ I hπ τ hΛ hall hallI,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

include hall in
/-- **Top degree of the perfect complex**: `H²(K(M)) ≃ (C ⊗ M)_{Gf}`, `C = coker (d¹ : P¹ → P²)`. -/
def topEquiv [Fintype S] [DecidableEq S] :
    H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ≃ₗ[Λ] Coinvariants ((cokRep (d1I Λ π Γ I hπ)).tprod τ) :=
  (Submodule.Quotient.equiv _ _ (iso2 π Γ I hπ τ hΛ hallI) (map_iso2_range_d1 π Γ I hπ τ hΛ hall hallI)).symm ≪≫ₗ
    coinvCokEquiv (d1I Λ π Γ I hπ) τ

include hall in
theorem topEquiv_mk [Fintype S] [DecidableEq S] (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    topEquiv π Γ I hπ τ hΛ hall hallI (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m)))) =
      Coinvariants.mk _ (Submodule.Quotient.mk e ⊗ₜ m) := by
  simp only [topEquiv, LinearEquiv.trans_apply, Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

end Top

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_H2 =====
section

/-!
# S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius

From a `ResHyp` (E4S): `h2Equiv : H²(K(M)) ≃ M_Γ` (`topEquiv`, then `coinvRes` = `(cokResEquiv ⊗ 1)_{Gf}`, then
`coinvG`), and `h2Equiv_frob`: it carries the cone Frobenius `frobH2K` to `frobH2c ψ c` (`c • ρ(ψ)` on `M_Γ`) under
the twist hypothesis `hTW` of `cokResEquiv_frob`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation TensorProduct

section H2

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G)) {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

namespace ResHyp

variable (H : ResHyp Λ π Γ I)

/-- `cokResEquiv` as an intertwining map. -/
def resI : IntertwiningMap (cokRep (d1I Λ π Γ I hπ)) (rRepΓ π Γ) :=
  ⟨(H.cokResEquiv hπ).toLinearMap, fun g => LinearMap.ext fun y => H.cokResEquiv_equiv hπ g y⟩

/-- Its inverse as an intertwining map. -/
def resIinv : IntertwiningMap (rRepΓ π Γ) (cokRep (d1I Λ π Γ I hπ)) :=
  ⟨(H.cokResEquiv hπ).symm.toLinearMap, fun g => LinearMap.ext fun y => by
    apply (H.cokResEquiv hπ).injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [H.cokResEquiv_equiv hπ g, LinearEquiv.apply_symm_apply]⟩

/-- `(C ⊗ M)_{Gf} ≃ (A_Γ ⊗ M)_{Gf}`. -/
def coinvRes : Coinvariants ((cokRep (d1I Λ π Γ I hπ)).tprod τ) ≃ₗ[Λ] Coinvariants ((rRepΓ π Γ).tprod τ) :=
  LinearEquiv.ofLinearMap (Coinvariants.map _ _ ((H.resI hπ).rTensor τ))
    (Coinvariants.map _ _ ((H.resIinv hπ).rTensor τ))
    (Coinvariants.hom_ext (TensorProduct.ext' fun y m => by
      show Coinvariants.mk _ ((H.cokResEquiv hπ) ((H.cokResEquiv hπ).symm y) ⊗ₜ m) = Coinvariants.mk _ (y ⊗ₜ m)
      rw [LinearEquiv.apply_symm_apply]))
    (Coinvariants.hom_ext (TensorProduct.ext' fun y m => by
      show Coinvariants.mk _ ((H.cokResEquiv hπ).symm ((H.cokResEquiv hπ) y) ⊗ₜ m) = Coinvariants.mk _ (y ⊗ₜ m)
      rw [LinearEquiv.symm_apply_apply]))

theorem coinvRes_mk (y : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap)
    (m : M) : H.coinvRes hπ τ (Coinvariants.mk _ (y ⊗ₜ m)) = Coinvariants.mk _ (H.cokResEquiv hπ y ⊗ₜ m) := rfl

variable [Finite Λ] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

include hall in
/-- **The cone's `H²` is `H²_c = M_Γ`** (S4-PD item (4)). -/
def h2Equiv : H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ≃ₗ[Λ] H2c (τ.comp π) Γ :=
  topEquiv π Γ I hπ τ hΛ hall hallI ≪≫ₗ H.coinvRes hπ τ ≪≫ₗ coinvG π Γ τ

include hall in
theorem h2Equiv_mk (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    H.h2Equiv hπ τ hΛ hall hallI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m)))) =
      coinvG π Γ τ (Coinvariants.mk _ (H.cokResEquiv hπ (Submodule.Quotient.mk e) ⊗ₜ m)) := by
  simp only [h2Equiv, LinearEquiv.trans_apply, topEquiv_mk]
  rfl

include hall in
/-- **Frobenius on the cone's `H²` is `c • ρ(ψ)` on `M_Γ`** (for the geometric Frobenius `c = q`: `M_Γ(-1)`). -/
theorem h2Equiv_frob (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ)
    (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (ht : Function.Bijective t)
    (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
      (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
        c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))
    (x : H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ)) :
    H.h2Equiv hπ τ hΛ hall hallI (frobH2K (τ.comp π) Γ I ψ t h (isOpen_comp_ker π τ hπ) hI x) =
      frobH2c (τ.comp π) Γ ψ c (H.h2Equiv hπ τ hΛ hall hallI x) := by
  have key : ∀ (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M),
      H.h2Equiv hπ τ hΛ hall hallI (frobH2K (τ.comp π) Γ I ψ t h (isOpen_comp_ker π τ hπ) hI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m))))) =
      frobH2c (τ.comp π) Γ ψ c (H.h2Equiv hπ τ hΛ hall hallI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m))))) := by
    intro e m
    rw [frobH2K_mk, ← iso2_frob_mk (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (p := e) (m := m),
      H.h2Equiv_mk, H.h2Equiv_mk, H.cokResEquiv_frob hπ ψ t h hI c hD ht hTW e]
    obtain ⟨a, ha⟩ := Coinvariants.mk_surjective _ (H.cokResEquiv hπ (Submodule.Quotient.mk e))
    rw [← ha, lftΓ_mk, ← TensorProduct.smul_tmul', map_smul, map_smul, coinvG_mk, coinvG_mk, frobH2c_mk,
      map_mul τ.asAlgebraHom, Module.End.mul_apply, asAlgebraHom_single_one]
    rfl
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, rfl⟩ := (iso2 π Γ I hπ τ hΛ hallI).surjective y
  induction z using Coinvariants.induction_on with
  | h w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.Quotient.mk_zero]
    | tmul e m => exact key e m
    | add w w' hw hw' =>
      simp only [map_add, Submodule.Quotient.mk_add] at hw hw' ⊢
      rw [hw, hw']

end ResHyp

end H2

end

end PerfectCx
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

/-- Hypotheses for the cup product: `β` equivariant, open kernels, `H²(Γ, L) = 0`. -/
structure CupHyp : Prop where
  equiv : ∀ (g : G) (x : M) (y : M'), β (ρ g x) (ρ' g y) = σ g (β x y)
  open' : IsOpen (ρ'.ker : Set G)
  openL : IsOpen (σ.ker : Set G)
  van : H2Van σ Γ ⊤

variable {ρ ρ' σ β Γ I}

theorem cupCochain_cocycle (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) (g h j : Γ) :
    cupCochain ρ' β Γ c d (g * h, j) + cupCochain ρ' β Γ c d (g, h) =
      σ g (cupCochain ρ' β Γ c d (h, j)) + cupCochain ρ' β Γ c d (g, h * j) := by
  show β (c (g * h)) (ρ' (g * h : Γ) (d j)) + β (c g) (ρ' g (d h)) =
      σ g (β (c h) (ρ' h (d j))) + β (c g) (ρ' g (d (h * j)))
  rw [((mem_Z1 ρ Γ c).1 hc).2 g h, ((mem_Z1 ρ' Γ d).1 hd).2 h j, ← H.equiv]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply]
  abel

theorem cupCochain_lc (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : IsLocallyConstant c)
    (hd : IsLocallyConstant d) : IsLocallyConstant (cupCochain ρ' β Γ c d) :=
  IsLocallyConstant.comp₂ (hc.comp_continuous continuous_fst)
    (lc_act_comp ρ' Γ (lcRep_of_isOpen ρ' Γ H.open') hd) fun x y => β x y

theorem exists_prim (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) : ∃ u, IsPrim ρ' σ β Γ c d u := by
  obtain ⟨b, hb, -, hb'⟩ := H.van (cupCochain ρ' β Γ c d)
    (cupCochain_lc H ((mem_Z1 ρ Γ c).1 hc).1 ((mem_Z1 ρ' Γ d).1 hd).1) (fun _ => Submodule.mem_top)
    (cupCochain_cocycle H hc hd)
  exact ⟨b, hb, hb'⟩

theorem cupBd_mem (H : CupHyp ρ ρ' σ β Γ) {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) {d : Γ → M'}
    (hd : d ∈ Z1 ρ' Γ) {u : Γ → L} (hu : IsPrim ρ' σ β Γ p.1 d u) (s : S) :
    cupBd β Γ I p d u s ∈ Z1 σ (Γ ⊓ I s) := by
  have hi : Continuous fun g : ↥(Γ ⊓ I s) => (⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : Γ) :=
    continuous_subtype_val.subtype_mk _
  refine (mem_Z1 σ (Γ ⊓ I s) _).2 ⟨?_, ?_⟩
  · exact ((((mem_Z1 ρ' Γ d).1 hd).1.comp_continuous hi).comp (β (p.2 s))).sub
      (hu.1.comp_continuous hi)
  rintro ⟨g, hg⟩ ⟨h, hh⟩
  obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hhΓ, -⟩ := Subgroup.mem_inf.1 hh
  have e1 : d (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) = d ⟨g, hgΓ⟩ + ρ' g (d ⟨h, hhΓ⟩) :=
    ((mem_Z1 ρ' Γ d).1 hd).2 _ _
  have e3 : p.1 ⟨g, hgΓ⟩ = ρ g (p.2 s) - p.2 s := ((mem_Z1c ρ Γ I p).1 hp).2 s ⟨g, hgΓ⟩ hgI
  have e4 := H.equiv g (p.2 s) (d ⟨h, hhΓ⟩)
  have e2' : u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) =
      σ g (u ⟨h, hhΓ⟩) + u ⟨g, hgΓ⟩ - β (p.1 ⟨g, hgΓ⟩) (ρ' g (d ⟨h, hhΓ⟩)) := by
    have e2 : β (p.1 ⟨g, hgΓ⟩) (ρ' g (d ⟨h, hhΓ⟩)) =
        σ g (u ⟨h, hhΓ⟩) - u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) + u ⟨g, hgΓ⟩ := hu.2 _ _
    rw [e2]; abel
  change β (p.2 s) (d (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩)) - u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) =
    (β (p.2 s) (d ⟨g, hgΓ⟩) - u ⟨g, hgΓ⟩) + σ g (β (p.2 s) (d ⟨h, hhΓ⟩) - u ⟨h, hhΓ⟩)
  rw [e1, e2', e3]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  rw [e4]
  abel

/-- The boundary cocycles of the cup product (for a chosen primitive `u`). -/
def cupZ (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) : (s : S) → Z1 σ (Γ ⊓ I s) :=
  fun s => ⟨cupBd β Γ I p d u s, cupBd_mem H p.2 d.2 hu s⟩

theorem cupZ_apply (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) (s : S) (g : ↥(Γ ⊓ I s)) :
    (cupZ H p d u hu s : ↥(Γ ⊓ I s) → L) g =
      β ((p : (Γ → M) × (S → M)).2 s) ((d : Γ → M') ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) -
        u ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ := rfl

theorem cupZ_sub_mem (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) {u₁ u₂ : Γ → L}
    (h₁ : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u₁)
    (h₂ : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u₂) :
    cupZ H p d u₁ h₁ - cupZ H p d u₂ h₂ ∈ LinearMap.range (cx1 σ Γ I H.openL) := by
  refine ⟨(⟨u₂ - u₁, (mem_Z1 σ Γ _).2 ⟨h₂.1.sub h₁.1, fun g h => ?_⟩⟩, 0), ?_⟩
  · have a := h₁.2 g h
    have b := h₂.2 g h
    have hab : σ g (u₂ h) - u₂ (g * h) + u₂ g - (σ g (u₁ h) - u₁ (g * h) + u₁ g) = 0 := by
      rw [← b, ← a, sub_self]
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero, ← neg_eq_zero, ← hab]
    abel
  · funext s
    apply Subtype.ext
    funext g
    rw [cx1_apply]
    simp only [Pi.sub_apply, Submodule.coe_sub, cupZ_apply, Pi.zero_apply, map_zero,
      sub_zero]
    abel

/-- The cup product of cocycles, as a class in `H2K`. -/
def cupH (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) : H2K σ Γ I H.openL :=
  Submodule.Quotient.mk (cupZ H p d _
    (exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2).choose_spec)

theorem cupH_eq (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) :
    cupH H p d = Submodule.Quotient.mk (cupZ H p d u hu) := by
  rw [cupH, Submodule.Quotient.eq]
  exact cupZ_sub_mem H p d _ hu

/-! ## Bilinearity -/

variable (H : CupHyp ρ ρ' σ β Γ)

theorem cupH_add_left (p₁ p₂ : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H (p₁ + p₂) d = cupH H p₁ d + cupH H p₂ d := by
  obtain ⟨u₁, h₁⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p₁.2).1 d.2
  obtain ⟨u₂, h₂⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p₂.2).1 d.2
  rw [cupH_eq H p₁ d u₁ h₁, cupH_eq H p₂ d u₂ h₂, cupH_eq H (p₁ + p₂) d (u₁ + u₂) (prim_add_left h₁ h₂),
    ← Submodule.Quotient.mk_add]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.add_apply, Submodule.coe_add, cupZ_apply, Prod.snd_add, map_add, LinearMap.add_apply]
  abel

theorem cupH_smul_left (a : k) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H (a • p) d = a • cupH H p d := by
  obtain ⟨u, h⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2
  rw [cupH_eq H p d u h, cupH_eq H (a • p) d (a • u) (prim_smul_left a h), ← Submodule.Quotient.mk_smul]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.smul_apply, Submodule.coe_smul, cupZ_apply, Prod.smul_snd, Pi.smul_apply, map_smul,
    LinearMap.smul_apply, smul_sub]

theorem cupH_add_right (p : Z1c ρ Γ I) (d₁ d₂ : Z1 ρ' Γ) :
    cupH H p (d₁ + d₂) = cupH H p d₁ + cupH H p d₂ := by
  obtain ⟨u₁, h₁⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d₁.2
  obtain ⟨u₂, h₂⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d₂.2
  rw [cupH_eq H p d₁ u₁ h₁, cupH_eq H p d₂ u₂ h₂, cupH_eq H p (d₁ + d₂) (u₁ + u₂) (prim_add_right h₁ h₂),
    ← Submodule.Quotient.mk_add]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.add_apply, Submodule.coe_add, cupZ_apply, map_add]
  abel

theorem cupH_smul_right (a : k) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H p (a • d) = a • cupH H p d := by
  obtain ⟨u, h⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2
  rw [cupH_eq H p d u h, cupH_eq H p (a • d) (a • u) (prim_smul_right a h), ← Submodule.Quotient.mk_smul]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.smul_apply, Submodule.coe_smul, cupZ_apply, map_smul, smul_sub]

/-! ## Vanishing on coboundaries -/

theorem cupH_B1c (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (hp : (p : (Γ → M) × (S → M)) ∈ B1c ρ Γ I) :
    cupH H p d = 0 := by
  obtain ⟨-, m, h1, h2⟩ := (mem_B1c ρ Γ I _).1 hp
  have hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d (fun g => β m ((d : Γ → M') g)) := by
    refine ⟨((mem_Z1 ρ' Γ _).1 d.2).1.comp (β m), fun g h => ?_⟩
    have e1 : (d : Γ → M') (g * h) = (d : Γ → M') g + ρ' g ((d : Γ → M') h) := ((mem_Z1 ρ' Γ _).1 d.2).2 g h
    show β ((p : (Γ → M) × (S → M)).1 g) (ρ' g ((d : Γ → M') h)) =
      σ g (β m ((d : Γ → M') h)) - β m ((d : Γ → M') (g * h)) + β m ((d : Γ → M') g)
    rw [h1 g, e1, ← H.equiv]
    simp only [map_add, map_sub, LinearMap.sub_apply]
    abel
  have hz : cupZ H p d _ hu = 0 := by
    funext s; apply Subtype.ext; funext g
    rw [cupZ_apply, h2 s, sub_self]
    rfl
  rw [cupH_eq H p d _ hu, hz, Submodule.Quotient.mk_zero]

theorem cupH_B1 (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (hd : (d : Γ → M') ∈ B1 ρ' Γ) :
    cupH H p d = 0 := by
  obtain ⟨-, y, hy⟩ := (mem_B1 ρ' Γ _).1 hd
  obtain ⟨hpZ, hpI⟩ := (mem_Z1c ρ Γ I _).1 p.2
  have hc := (mem_Z1 ρ Γ _).1 hpZ
  have hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d
      (fun g => -β ((p : (Γ → M) × (S → M)).1 g) (ρ' g y)) := by
    refine ⟨IsLocallyConstant.comp₂ hc.1 (lcRep_of_isOpen ρ' Γ H.open' y) fun x z => -β x z,
      fun g h => ?_⟩
    have e1 := hc.2 g h
    show β ((p : (Γ → M) × (S → M)).1 g) (ρ' g ((d : Γ → M') h)) =
      σ g (-β ((p : (Γ → M) × (S → M)).1 h) (ρ' h y)) -
        -β ((p : (Γ → M) × (S → M)).1 (g * h)) (ρ' (g * h : Γ) y) +
        -β ((p : (Γ → M) × (S → M)).1 g) (ρ' g y)
    rw [hy h, e1, map_neg, ← H.equiv]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, map_sub, LinearMap.add_apply]
    abel
  rw [cupH_eq H p d _ hu, Submodule.Quotient.mk_eq_zero]
  refine ⟨(0, fun s => -β ((p : (Γ → M) × (S → M)).2 s) y), ?_⟩
  funext s; apply Subtype.ext; funext ⟨g, hg⟩
  obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
  have e3 : (p : (Γ → M) × (S → M)).1 ⟨g, hgΓ⟩ = ρ g ((p : (Γ → M) × (S → M)).2 s) -
      (p : (Γ → M) × (S → M)).2 s := hpI s ⟨g, hgΓ⟩ hgI
  have e4 := H.equiv g ((p : (Γ → M) × (S → M)).2 s) y
  rw [cx1_apply, cupZ_apply]
  change (0 : Γ → L) ⟨g, hgΓ⟩ - (σ g (-β ((p : (Γ → M) × (S → M)).2 s) y) -
      -β ((p : (Γ → M) × (S → M)).2 s) y) =
    β ((p : (Γ → M) × (S → M)).2 s) ((d : Γ → M') ⟨g, hgΓ⟩) -
      -β ((p : (Γ → M) × (S → M)).1 ⟨g, hgΓ⟩) (ρ' g y)
  rw [hy, e3]
  simp only [Pi.zero_apply, map_neg, map_sub, LinearMap.sub_apply]
  rw [e4]
  abel

/-! ## The cup product on cohomology -/

/-- The cup product on cocycles, bilinear. -/
def cupZZ : Z1c ρ Γ I →ₗ[k] Z1 ρ' Γ →ₗ[k] H2K σ Γ I H.openL :=
  LinearMap.mk₂ k (cupH H) (cupH_add_left H) (cupH_smul_left H) (cupH_add_right H) (cupH_smul_right H)

/-- **The cup product** `H¹_c(Γ, {I_s}; M) × H¹(Γ, M') → H²(K(L))`. -/
def cupPair : H1c ρ Γ I →ₗ[k] H1 ρ' Γ →ₗ[k] H2K σ Γ I H.openL :=
  ((B1c ρ Γ I).comap (Z1c ρ Γ I).subtype).liftQ
    (((B1 ρ' Γ).comap (Z1 ρ' Γ).subtype).liftQ (cupZZ H).flip
      (fun d hd => LinearMap.ext fun p => cupH_B1 H p d hd)).flip
    (fun p hp => Submodule.linearMap_qext _ (LinearMap.ext fun d => cupH_B1c H p d hp))

theorem cupPair_mk (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupPair H (H1c.mk ρ Γ I p) (H1.mk ρ' Γ d) = cupH H p d := rfl

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_CupFrob =====
section

/-!
# S4-CurveDuality O2b: Frobenius compatibility of the cup product

`cupPair (frobH1c x) (frobH1 y) = frobH2K (cupPair x y)` for a Frobenius lift `ψ` with boundary data `(τ, h)`
(`BdryCompat`). On cocycles: the twisted primitive is `g ↦ σ ψ (u (ψ⁻¹ g ψ))`, and the two boundary cocycles differ
by `d¹ (0, s ↦ -σ ψ w_s)` with `w_s = β (c x) (d x) + u x - β (ρ x m_{τ s}) (d x)`, `x = h s` (`frob_core`).
Also `CupHyp` from `H2All` (`cupHyp_of_all`).
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
  {ρ : Representation k G M} {ρ' : Representation k G M'} {σ : Representation k G L}
  {β : M →ₗ[k] M' →ₗ[k] L} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}

/-- `H²(Γ, L) = 0` from `H2All`. -/
theorem h2Van_top_of_all {l n : ℕ} (hall : H2All k G Γ l n) [Finite L] (hL : ∀ m : L, (l ^ n) • m = 0)
    (hσ : IsOpen (σ.ker : Set G)) : H2Van σ Γ ⊤ := fun f hf _ hc => by
  obtain ⟨b, hb, hfb⟩ := hall L σ hL hσ f hf hc
  exact ⟨b, hb, fun _ => Submodule.mem_top, hfb⟩

/-- The algebraic core of Frobenius compatibility (`gt x = x g2`, `g2 ∈ I`). -/
theorem frob_core (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) (hu : IsPrim ρ' σ β Γ c d u) (x gt g2 : Γ) (m : M) (hmul : gt * x = x * g2)
    (hcg : c g2 = ρ (g2 : G) m - m) :
    β (ρ (x : G) m - c x) (d gt) - u gt - σ (x : G) (β m (d g2) - u g2) =
      σ (gt : G) (β (c x) (d x) + u x - β (ρ (x : G) m) (d x)) -
        (β (c x) (d x) + u x - β (ρ (x : G) m) (d x)) := by
  have R1 : β (c gt) (ρ' (gt : G) (d x)) = σ (gt : G) (u x) - u (gt * x) + u gt := hu.2 gt x
  have R2 : β (c x) (ρ' (x : G) (d g2)) = σ (x : G) (u g2) - u (x * g2) + u x := hu.2 x g2
  have D1 : d (gt * x) = d gt + ρ' (gt : G) (d x) := hd.2 gt x
  have D2 : d (x * g2) = d x + ρ' (x : G) (d g2) := hd.2 x g2
  have C1 : c (gt * x) = c gt + ρ (gt : G) (c x) := hc.2 gt x
  have C2 : c (x * g2) = c x + ρ (x : G) (c g2) := hc.2 x g2
  rw [hmul] at R1 D1 C1
  have Dx : ρ' (x : G) (d g2) = d gt + ρ' (gt : G) (d x) - d x := by
    rw [← D1, D2]; abel
  have Cgt : c gt = c x + ρ (x : G) (c g2) - ρ (gt : G) (c x) := by
    rw [eq_sub_iff_add_eq, ← C1, C2]
  have Rgx : ρ (x : G) (ρ (g2 : G) m) = ρ (gt : G) (ρ (x : G) m) := by
    have e := congrArg (fun z : Γ => ρ (z : G) m) hmul
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply] at e
    exact e.symm
  rw [Cgt, hcg, map_sub (ρ (x : G)), Rgx] at R1
  rw [Dx] at R2
  rw [map_sub (σ (x : G)), ← H.equiv (x : G) m (d g2), Dx]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, H.equiv] at R1 R2 ⊢
  linear_combination (norm := module) R1 - R2

section Frob

variable [Γ.Normal] (H : CupHyp ρ ρ' σ β Γ) (ψ : G) (τ : S → S) (h : S → Γ)

include H in
/-- The twisted primitive: `T_ψ u` is a primitive of `T_ψ c ∪ T_ψ d`. -/
theorem prim_twist {c : Γ → M} {d : Γ → M'} {u : Γ → L} (hu : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ (twist ρ Γ ψ c) (twist ρ' Γ ψ d) (twist σ Γ ψ u) := by
  refine ⟨(hu.1.comp_continuous (continuous_conjΓ Γ ψ)).comp (σ ψ), fun g j => ?_⟩
  have e : β (c (conjΓ Γ ψ g)) (ρ' (conjΓ Γ ψ g : G) (d (conjΓ Γ ψ j))) =
      σ (conjΓ Γ ψ g : G) (u (conjΓ Γ ψ j)) - u (conjΓ Γ ψ g * conjΓ Γ ψ j) + u (conjΓ Γ ψ g) := hu.2 _ _
  show β (ρ ψ (c (conjΓ Γ ψ g))) (ρ' (g : G) (ρ' ψ (d (conjΓ Γ ψ j)))) =
    σ (g : G) (σ ψ (u (conjΓ Γ ψ j))) - σ ψ (u (conjΓ Γ ψ (g * j))) + σ ψ (u (conjΓ Γ ψ g))
  rw [← rho_conj ρ' Γ ψ g, H.equiv, ← rho_conj σ Γ ψ g, conjΓ_mul, e, map_add, map_sub]

/-- Frobenius compatibility of the cup product on cocycles. -/
theorem cupH_frob (hI : BdryCompat Γ I ψ τ h) {c : Γ → M} {mv : S → M} (hp : (c, mv) ∈ Z1c ρ Γ I)
    {dd : Γ → M'} (hd : dd ∈ Z1 ρ' Γ) :
    cupH H ⟨twistc ρ Γ ψ τ h (c, mv), twistc_mem_Z1c ρ Γ I ψ τ h hI hp⟩
        ⟨twist ρ' Γ ψ dd, twist_mem_Z1 ρ' Γ ψ hd⟩ =
      frobH2K σ Γ I ψ τ h H.openL hI (cupH H ⟨(c, mv), hp⟩ ⟨dd, hd⟩) := by
  obtain ⟨u, hu⟩ := exists_prim H hp.1 hd
  rw [cupH_eq H ⟨(c, mv), hp⟩ ⟨dd, hd⟩ u hu, frobH2K_mk,
    cupH_eq H ⟨twistc ρ Γ ψ τ h (c, mv), twistc_mem_Z1c ρ Γ I ψ τ h hI hp⟩
      ⟨twist ρ' Γ ψ dd, twist_mem_Z1 ρ' Γ ψ hd⟩ (twist σ Γ ψ u) (prim_twist H ψ hu),
    Submodule.Quotient.eq]
  refine ⟨(0, fun s => -σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))), ?_⟩
  funext s
  apply Subtype.ext
  funext ⟨g, hg⟩
  obtain ⟨hgΓ, -⟩ := Subgroup.mem_inf.1 hg
  have hb := bdry_mem Γ I ψ τ h hI s g hg
  have hm2 : (ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)) ∈ Γ := (Subgroup.mem_inf.1 hb).1
  have hcg : c ⟨_, hm2⟩ = ρ ((ψ * (h s : G))⁻¹ * g * (ψ * (h s : G))) (mv (τ s)) - mv (τ s) :=
    hp.2 (τ s) ⟨_, hm2⟩ (Subgroup.mem_inf.1 hb).2
  have hmul : conjΓ Γ ψ ⟨g, hgΓ⟩ * h s = h s * ⟨_, hm2⟩ := by
    apply Subtype.ext
    show ψ⁻¹ * g * ψ * (h s : G) = (h s : G) * ((ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)))
    group
  have K := frob_core H hp.1 hd hu (h s) (conjΓ Γ ψ ⟨g, hgΓ⟩) ⟨_, hm2⟩ (mv (τ s)) hmul hcg
  have e5 : σ g (σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) =
      σ ψ (σ (conjΓ Γ ψ ⟨g, hgΓ⟩ : G)
        (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) :=
    (rho_conj σ Γ ψ ⟨g, hgΓ⟩ _).symm
  change (0 : Γ → L) ⟨g, hgΓ⟩ -
      (σ g (-σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) -
        -σ ψ (β (c (h s)) (dd (h s)) + u (h s) - β (ρ (h s : G) (mv (τ s))) (dd (h s)))) =
    (β (ρ ψ (ρ (h s : G) (mv (τ s)) - c (h s))) (ρ' ψ (dd (conjΓ Γ ψ ⟨g, hgΓ⟩))) -
        σ ψ (u (conjΓ Γ ψ ⟨g, hgΓ⟩))) -
      σ (ψ * (h s : G)) (β (mv (τ s)) (dd ⟨_, hm2⟩) - u ⟨_, hm2⟩)
  rw [H.equiv, map_mul σ ψ (h s : G), Module.End.mul_apply, ← map_sub (σ ψ), ← map_sub (σ ψ), K, map_neg,
    e5, Pi.zero_apply]
  simp only [map_sub, map_add]
  abel

/-- **Frobenius compatibility of the cup product**: `F(x) ∪ F(y) = F(x ∪ y)`. -/
theorem cupPair_frob (hI : BdryCompat Γ I ψ τ h) (x : H1c ρ Γ I) (y : H1 ρ' Γ) :
    cupPair H (frobH1c ρ Γ I ψ τ h hI x) (frobH1 ρ' Γ ψ y) =
      frobH2K σ Γ I ψ τ h H.openL hI (cupPair H x y) := by
  obtain ⟨⟨⟨c, mv⟩, hp⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨dd, hd⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact cupH_frob H ψ τ h hI hp hd

end Frob

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

/-- `CupHyp` for constant coefficients `k × k(1) → k(1)`. -/
theorem constCupHyp (hσ : IsOpen (σ.ker : Set G)) (van : H2Van σ Γ ⊤) :
    CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ :=
  ⟨fun g x y => by
    rw [Representation.trivial_apply, LinearMap.mul_apply', LinearMap.mul_apply']
    have h := map_smul (σ g) x y
    exact h.symm, hσ, hσ, van⟩

variable [Fintype S]

variable {σ Γ I t}

theorem cx1_eval (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (p : Z1 σ Γ × (S → k)) (s : S) :
    (cx1 σ Γ I hσ p s : ↥(Γ ⊓ I s) → k) (t s) = (p.1 : Γ → k) (tG t s) := by
  show (p.1 : Γ → k) (tG t s) - (σ (tG t s : G) (p.2 s) - p.2 s) = _
  rw [D.triv (tG t s) (p.2 s), sub_self, sub_zero]

theorem evalSum_cx1 (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (p : Z1 σ Γ × (S → k)) :
    evalSum σ Γ I t (cx1 σ Γ I hσ p) = 0 := by
  rw [evalSum_apply]
  simp only [cx1_eval D hσ p]
  exact D.resSum p.1

/-- `H²(K) → k`, `[e] ↦ Σ_s e_s(t_s)`. -/
def h2kMap (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) : H2K σ Γ I hσ →ₗ[k] k :=
  (LinearMap.range (cx1 σ Γ I hσ)).liftQ (evalSum σ Γ I t) (by
    intro x hx
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (evalSum_cx1 D hσ p))

theorem h2kMap_mk (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) (e : (s : S) → Z1 σ (Γ ⊓ I s)) :
    h2kMap D hσ (Submodule.Quotient.mk e) = evalSum σ Γ I t e := rfl

theorem h2kMap_injective (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) :
    Function.Injective (h2kMap D hσ) := by
  rw [← LinearMap.ker_eq_bot, h2kMap]
  apply Submodule.ker_liftQ_eq_bot
  intro e he
  rw [LinearMap.mem_ker, evalSum_apply] at he
  obtain ⟨d, hd⟩ := D.resOnto (fun s => (e s : ↥(Γ ⊓ I s) → k) (t s)) he
  refine LinearMap.mem_range.2 ⟨(d, 0), funext fun s => ?_⟩
  have h0 : cx1 σ Γ I hσ (d, 0) s - e s = 0 := D.inj s _ (by
    show (cx1 σ Γ I hσ (d, 0) s : ↥(Γ ⊓ I s) → k) (t s) - (e s : ↥(Γ ⊓ I s) → k) (t s) = 0
    rw [cx1_eval D hσ]
    exact sub_eq_zero.2 (hd s))
  exact sub_eq_zero.1 h0

theorem h2kMap_surjective [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) :
    Function.Surjective (h2kMap D hσ) := by
  classical
  intro a
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  choose E hE using D.surj
  refine ⟨Submodule.Quotient.mk (fun s => E s (if s = s0 then a else 0)), ?_⟩
  rw [h2kMap_mk, evalSum_apply]
  simp only [hE]
  simp

/-- `H²(K) ≃ k` for constant coefficients. -/
def h2kEquiv [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G)) : H2K σ Γ I hσ ≃ₗ[k] k :=
  LinearEquiv.ofBijective (h2kMap D hσ) ⟨h2kMap_injective D hσ, h2kMap_surjective D hσ⟩

theorem h2kEquiv_mk [Nonempty S] (D : ConstData σ Γ I t) (hσ : IsOpen (σ.ker : Set G))
    (e : (s : S) → Z1 σ (Γ ⊓ I s)) : h2kEquiv D hσ (Submodule.Quotient.mk e) = evalSum σ Γ I t e := rfl

/-! ## The pairing and its boundary block -/

variable [Nonempty S]

/-- The constant-coefficient pairing `H¹_c(Ū, k) × H¹(Ū, k(1)) → H²(K) ≅ k`. -/
def constPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (D : ConstData σ Γ I t) :
    H1c (Representation.trivial k G k) Γ I →ₗ[k] H1 σ Γ →ₗ[k] k :=
  (cupPair (I := I) H).compr₂ (h2kEquiv D H.openL).toLinearMap

theorem constPair_mk (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (p : Z1c (Representation.trivial k G k) Γ I) (d : Z1 σ Γ) (u : Γ → k)
    (hu : IsPrim σ σ (LinearMap.mul k k) Γ (p : (Γ → k) × (S → k)).1 d u) :
    constPair H D (H1c.mk (Representation.trivial k G k) Γ I p) (H1.mk σ Γ d) =
      ∑ s, ((p : (Γ → k) × (S → k)).2 s * (d : Γ → k) (tG t s) - u (tG t s)) := by
  show h2kEquiv D H.openL (cupH H p d) = _
  rw [cupH_eq H p d u hu, h2kEquiv_mk, evalSum_apply]
  rfl

theorem constPair_bdry (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (m : S → k) (d : Z1 σ Γ) :
    constPair H D (bdryMap (k := k) Γ I m) (H1.mk σ Γ d) = ∑ s, m s * (d : Γ → k) (tG t s) := by
  have hu : IsPrim σ σ (LinearMap.mul k k) Γ (0 : Γ → k) d 0 :=
    ⟨IsLocallyConstant.const 0, fun g h => by simp [cupCochain]⟩
  rw [bdryMap_apply, constPair_mk H D ⟨((0 : Γ → k), m), zero_mem_Z1c Γ I m⟩ d 0 hu]
  simp

theorem constPair_h0 (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) :
    ∀ x ∈ LinearMap.range (bdryMap (k := k) Γ I), ∀ y ∈ H1par σ Γ I, constPair H D x y = 0 := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.1 hy
  rw [constPair_bdry]
  simp [par_eval D (Submodule.mem_comap.1 hd)]

/-! ## Residues `H¹(Ū, k(1)) / H¹_par → ker Σ` -/

theorem ker_resH (D : ConstData σ Γ I t) : LinearMap.ker (resH D) = H1par σ Γ I := by
  ext x
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h' : ∀ s, (d : Γ → k) (tG t s) = 0 := fun s => congrFun (congrArg Subtype.val h) s
    refine Submodule.mem_map.2 ⟨d, ?_, rfl⟩
    refine ⟨d.2, fun s => ⟨0, fun g hg => ?_⟩⟩
    have he := D.inj s (PerfectCx.res σ Γ inf_le_left d) (h' s)
    have h2 : (d : Γ → k) g = 0 := congrFun (congrArg Subtype.val he) ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩
    rw [map_zero, sub_zero]
    exact h2
  · intro h
    obtain ⟨d', hd', hdd⟩ := Submodule.mem_map.1 h
    rw [← hdd, resH_mk]
    exact Subtype.ext (funext fun s => par_eval D (Submodule.mem_comap.1 hd') s)

variable (Γ I) in
/-- `k^S / k ≃ im(k^S → H¹_c)`. -/
def bdryQuotEquiv : ((S → k) ⧸ constSub S k) ≃ₗ[k] LinearMap.range (bdryMap (k := k) Γ I) :=
  (Submodule.quotEquivOfEq _ _ (ker_bdryMap k Γ I).symm).trans (bdryMap (k := k) Γ I).quotKerEquivRange

theorem bdryQuotEquiv_mk (m : S → k) :
    (bdryQuotEquiv (k := k) Γ I (Submodule.Quotient.mk m) : H1c (Representation.trivial k G k) Γ I) =
      bdryMap (k := k) Γ I m := rfl

/-- `H¹ / H¹_par ≃ ker Σ` via residues. -/
def h1QuotEquiv (D : ConstData σ Γ I t) : (H1 σ Γ ⧸ H1par σ Γ I) ≃ₗ[k] sumKer S k :=
  (Submodule.quotEquivOfEq _ _ (ker_resH D).symm).trans ((resH D).quotKerEquivOfSurjective (resH_surjective D))

theorem h1QuotEquiv_mk (D : ConstData σ Γ I t) (d : Z1 σ Γ) :
    h1QuotEquiv D (Submodule.Quotient.mk (H1.mk σ Γ d)) = resZ' D d := rfl

/-- Block A is the residue pairing. -/
theorem blockA_eq (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) :
    pairSubQuot (constPair H D) _ _ (constPair_h0 H D) =
      (resPair S k).compl₁₂ (bdryQuotEquiv (k := k) Γ I).symm.toLinearMap (h1QuotEquiv D).toLinearMap := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨q, rfl⟩ := (bdryQuotEquiv (k := k) Γ I).surjective x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    pairSubQuot_apply, bdryQuotEquiv_mk, show (Submodule.Quotient.mk d : H1 σ Γ) = H1.mk σ Γ d from rfl,
    constPair_bdry, h1QuotEquiv_mk, resPair_mk]
  rfl

theorem blockA_isPerfPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) : (pairSubQuot (constPair H D) _ _ (constPair_h0 H D)).IsPerfPair := by
  have : (resPair S k).IsPerfPair := resPair_isPerfPair
  rw [blockA_eq H D]
  infer_instance

/-- Constant-coefficient duality, reduced to the parabolic block (O5). -/
theorem constPair_isPerfPair (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (hB : (pairQuotSub (constPair H D) _ _ (constPair_h0 H D)).IsPerfPair) :
    (constPair H D).IsPerfPair := by
  have := blockA_isPerfPair H D
  exact isPerfPair_of_block (constPair_h0 H D)

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

theorem regRep_one_apply (g : G) (a : MonoidAlgebra k PUnit) :
    regRep k (1 : G →* PUnit) g a = a := by
  rw [regRep_apply, MonoidHom.one_apply, ← MonoidAlgebra.one_def, one_mul]

theorem nrmS_punit (D : Subgroup PUnit) [Fintype D] : nrmS k D = 1 := by
  unfold nrmS
  rw [Fintype.sum_subsingleton _ (1 : D)]
  rfl

/-- Transport `Z¹(Γ', k(1)) → Z¹(Γ', k[PUnit])` when `σ` is trivial on `Γ'`. -/
theorem up_mem (σ : Representation k G k) (Γ' : Subgroup G) (h : ∀ (g : Γ') (x : k), σ g x = x)
    (e : Z1 σ Γ') : (fun g => (unitE k).symm ((e : Γ' → k) g)) ∈ Z1 (regRep k (1 : G →* PUnit)) Γ' := by
  obtain ⟨he1, he2⟩ := (mem_Z1 σ Γ' _).1 e.2
  refine (mem_Z1 _ Γ' _).2 ⟨he1.comp _, fun g g' => ?_⟩
  simp only [he2 g g', h, map_add, regRep_one_apply]

/-- Transport `Z¹(Γ', k[PUnit]) → Z¹(Γ', k(1))` when `σ` is trivial on `Γ'`. -/
theorem down_mem (σ : Representation k G k) (Γ' : Subgroup G) (h : ∀ (g : Γ') (x : k), σ g x = x)
    (e : Z1 (regRep k (1 : G →* PUnit)) Γ') :
    (fun g => unitE k ((e : Γ' → MonoidAlgebra k PUnit) g)) ∈ Z1 σ Γ' := by
  obtain ⟨he1, he2⟩ := (mem_Z1 _ Γ' _).1 e.2
  refine (mem_Z1 σ Γ' _).2 ⟨he1.comp _, fun g g' => ?_⟩
  simp only [he2 g g', h, map_add, regRep_one_apply]

variable (σ : Representation k G k) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map (1 : G →* PUnit))] [∀ s, Fintype ((Γ ⊓ I s).map (1 : G →* PUnit))]

variable {σ Γ I} in
/-- **O6a.** S4-PD's residue hypotheses for the trivial quotient give the constant-coefficient data. -/
theorem constData_of_resHyp (H : ResHyp k (1 : G →* PUnit) Γ I) (htriv : ∀ (g : Γ) (x : k), σ g x = x) :
    ConstData σ Γ I H.sg := by
  have hN : ∀ s, H.Ns s = 1 := fun s => by
    have h := H.hNs s
    rwa [nrmS_punit, nrmS_punit, mul_one] at h
  have htG : ∀ s, tG H.sg s = H.sG s := fun s => rfl
  refine ⟨htriv, fun s e he => ?_, fun s a => ?_, fun d => ?_, fun r hr => ?_⟩
  · -- inj
    let e' : Z1 (regRep k (1 : G →* PUnit)) (Γ ⊓ I s) := ⟨_, up_mem σ _ (triv_inf htriv s) e⟩
    have h0 : (e' : ↥(Γ ⊓ I s) → MonoidAlgebra k PUnit) (H.sg s) = 0 := by
      show (unitE k).symm ((e : ↥(Γ ⊓ I s) → k) (H.sg s)) = 0
      rw [he, map_zero]
    apply Subtype.ext
    funext j
    have hj := H.Ldet' s e' h0 j (Subsingleton.elim _ _)
    have hj' : (unitE k).symm ((e : ↥(Γ ⊓ I s) → k) j) = 0 := hj
    exact (unitE k).symm.injective (hj'.trans (map_zero _).symm)
  · -- surj
    obtain ⟨ε, hε⟩ := H.Lex' s
    refine ⟨a • ⟨_, down_mem σ _ (triv_inf htriv s) ε⟩, ?_⟩
    show a • unitE k ((ε : ↥(Γ ⊓ I s) → MonoidAlgebra k PUnit) (H.sg s)) = a
    rw [hε, nrmS_punit, map_one, smul_eq_mul, mul_one]
  · -- resSum
    have h := congrArg (unitE k) (H.GR ⟨_, up_mem σ Γ htriv d⟩)
    simp only [hN, one_mul, map_sum, map_zero, RingEquiv.apply_symm_apply] at h
    exact h
  · -- resOnto
    choose c hc using H.GE1
    have hc' : ∀ s s', (c s : Γ → MonoidAlgebra k PUnit) (H.sG s') =
        (if s' = s then 1 else 0) - (if s' = H.s0 then 1 else 0) := fun s s' => by
      have h := hc s s'
      rw [nrmS_punit, nrmS_punit] at h
      exact h
    refine ⟨∑ s, r s • ⟨_, down_mem σ Γ htriv (c s)⟩, fun s' => ?_⟩
    rw [htG]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc',
      map_sub, apply_ite (unitE k), map_one, map_zero, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases h : s' = H.s0
    · simp [h, hr]
    · simp [h]

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

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation k G k) (Γ : Subgroup G) [Γ.Normal]

variable {S : Type} (I : S → Subgroup G)

/-- Frobenius on the cone's `H²` is the scalar `χ · σ(ψ)(1)` when it is conjugate to `frobH2c`. -/
theorem frobH2K_eq_smul (hσ : IsOpen (σ.ker : Set G)) (ψ : G) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I ψ τ h) (χ : k) (E : H2K σ Γ I hσ ≃ₗ[k] H2c σ Γ)
    (hE : ∀ x, E (frobH2K σ Γ I ψ τ h hσ hI x) = frobH2c σ Γ ψ χ (E x)) (z : H2K σ Γ I hσ) :
    frobH2K σ Γ I ψ τ h hσ hI z = (χ * σ ψ 1) • z :=
  eq_smul_of_conj E hE (frobH2c_eq_smul σ Γ ψ χ) z

variable [Fintype S] [Nonempty S] {σ Γ I} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- Frobenius on the constant-coefficient pairing: `⟨F x, F y⟩ = c · ⟨x, y⟩` when `F = c` on `H²(K)`. -/
theorem constPair_frob (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (c : k)
    (hF : ∀ z, frobH2K σ Γ I ψ τ h H.openL hI z = c • z)
    (x : H1c (Representation.trivial k G k) Γ I) (y : H1 σ Γ) :
    constPair H D (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x) (frobH1 σ Γ ψ y) =
      c * constPair H D x y := by
  show h2kEquiv D H.openL (cupPair H (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x)
      (frobH1 σ Γ ψ y)) = c * h2kEquiv D H.openL (cupPair H x y)
  rw [cupPair_frob H ψ τ h hI x y, hF, map_smul, smul_eq_mul]

/-- `constPair_frob` with the scalar read off from an intertwiner `E : H²(K) ≃ H²_c` (S4-PD). -/
theorem constPair_frob_of_equiv (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (ψ : G) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ τ h) (χ : k)
    (E : H2K σ Γ I H.openL ≃ₗ[k] H2c σ Γ)
    (hE : ∀ x, E (frobH2K σ Γ I ψ τ h H.openL hI x) = frobH2c σ Γ ψ χ (E x))
    (x : H1c (Representation.trivial k G k) Γ I) (y : H1 σ Γ) :
    constPair H D (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x) (frobH1 σ Γ ψ y) =
      (χ * σ ψ 1) * constPair H D x y :=
  constPair_frob H D ψ τ h hI _ (frobH2K_eq_smul σ Γ I H.openL ψ τ h hI χ E hE) x y

end

end CupDuality
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

section Gys

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {ι : Type} [Fintype ι]

variable {ρ : Representation k G ((ι → k) × (ι → k))} {d : ι → Γ → k}

theorem cx1_inf (hρ : IsOpen (ρ.ker : Set G)) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (p : Z1 ρ Γ × (S → (ι → k) × (ι → k))) (s : S)
    (g : ↥(Γ ⊓ I s)) :
    (cx1 ρ Γ I hρ p s : ↥(Γ ⊓ I s) → (ι → k) × (ι → k)) g =
      (p.1 : Γ → (ι → k) × (ι → k)) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ := by
  rw [cx1_apply, rho_inf hρΓ hpar s g, sub_self, sub_zero]

variable [DecidableEq S] [Nonempty S]

/-- **Gysin count**: if every `d_i` is in the right kernel of `constPair`, `#H²(K; V) ≥ #(ι → k)²`. -/
theorem card_sq_le_h2K (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (DD : ConstData σ Γ I t) (hρ : IsOpen (ρ.ker : Set G)) (hρΓ : IsUniFam ρ d)
    (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0) (hd : ∀ i, d i ∈ Z1 σ Γ)
    (hR : ∀ i (p : Z1c (Representation.trivial k G k) Γ I),
      constPair H DD (H1c.mk (Representation.trivial k G k) Γ I p) (H1.mk σ Γ ⟨d i, hd i⟩) = 0)
    [Finite (H2K ρ Γ I hρ)] :
    Nat.card (ι → k) * Nat.card (ι → k) ≤ Nat.card (H2K ρ Γ I hρ) := by
  classical
  choose e he using fun s => DD.surj s 1
  have hsum : ∀ (r : (ι → k) × (ι → k) →ₗ[k] (ι → k)) (v : (ι → k) × (ι → k)) (s0 : S),
      prR t ρ r (fun s => zmk DD hρΓ hpar s (e s) (if s = s0 then v else 0)) = r v := by
    intro r v s0
    rw [prR_apply, Finset.sum_eq_single s0]
    · rw [zmk_apply, he, one_smul, if_pos rfl]
    · intro s _ hs
      rw [zmk_apply, if_neg hs, smul_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ s0) h
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  refine card_sq_le_quot (LinearMap.range (cx1 ρ Γ I hρ)) (zSnd0 I ρ) (prR t ρ (LinearMap.fst k _ _))
    (prR t ρ (LinearMap.snd k _ _)) (fun a => ⟨_, hsum _ (0, a) s0⟩)
    (fun a => ⟨_, (mem_zSnd0 _).2 fun s g => ?_, hsum _ (a, 0) s0⟩) ?_ ?_ ?_
  · rw [zmk_apply]
    split_ifs <;> simp
  · rintro z ⟨p, rfl⟩
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.snd_apply, cx1_inf hρ hρΓ hpar]
    exact DD.resSum ⟨_, snd_mem_Z1 DD hρΓ p.1 i⟩
  · intro z hz
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.snd_apply]
    exact Finset.sum_eq_zero fun s _ => by rw [(mem_zSnd0 _).1 hz s (t s)]; rfl
  · rintro z ⟨p, rfl⟩ hz
    funext i
    rw [prR_apply, Finset.sum_apply]
    simp only [LinearMap.fst_apply, cx1_inf hρ hρΓ hpar]
    have hun : ∀ (s : S) (g : Γ), (g : G) ∈ I s → ((p.1 : Γ → (ι → k) × (ι → k)) g).2 i = 0 := by
      intro s g hg
      have := (mem_zSnd0 _).1 hz s ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩
      rw [cx1_inf hρ hρΓ hpar] at this
      exact congrFun this i
    have hpc : ((fun g => ((p.1 : Γ → (ι → k) × (ι → k)) g).2 i), (0 : S → k)) ∈
        Z1c (Representation.trivial k G k) Γ I :=
      (mem_Z1c _ Γ I _).2 ⟨snd_mem_Z1_triv hρΓ p.1 i, fun s g hg => (hun s g hg).trans (by simp)⟩
    have hc := constPair_mk H DD ⟨_, hpc⟩ ⟨d i, hd i⟩ _ (prim_fst DD hρΓ hd p.1 i)
    rw [hR i ⟨_, hpc⟩] at hc
    have ht : ∀ s, ((p.1 : Γ → (ι → k) × (ι → k)) (tG t s)).2 i = 0 :=
      fun s => hun s (tG t s) (Subgroup.mem_inf.1 (t s).2).2
    simp only [Pi.zero_apply, zero_mul, zero_sub, ht, Finset.sum_neg_distrib] at hc
    simpa [tG] using hc.symm

end Gys

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

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- `d` is a parabolic cocycle in the right kernel of `constPair`. -/
def InR (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (DD : ConstData σ Γ I t)
    (d : Γ → k) : Prop :=
  ∃ hd : d ∈ Z1 σ Γ, (∀ s (g : Γ), (g : G) ∈ I s → d g = 0) ∧
    ∀ z : H1c (Representation.trivial k G k) Γ I, constPair H DD z (H1.mk σ Γ ⟨d, hd⟩) = 0

/-- **O4G-5a.** Stability of the right kernel under `d ↦ d ∘ conjΓ φ`. -/
theorem inR_conj (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (DD : ConstData σ Γ I t)
    (htriv : ∀ (g : Γ) (x : k), σ g x = x) {φ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I φ⁻¹ τ h)
    {τ2 : S → S} {h2 : S → Γ} (hI2 : BdryCompat Γ I φ τ2 h2) {c : k} (hc : IsUnit c)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial k G k) Γ I φ⁻¹ τ h hI x) (frobH1 σ Γ φ⁻¹ y) =
      c * constPair H DD x y) {d : Γ → k} (hR : InR H DD d) : InR H DD (fun g => d (conjΓ Γ φ g)) := by
  obtain ⟨hd, hpar, hker⟩ := hR
  have hadd := add_of_Z1 htriv hd
  have hd' : (fun g => d (conjΓ Γ φ g)) ∈ Z1 σ Γ :=
    ⟨hd.1.comp_continuous (continuous_conjΓ Γ φ), fun g g' => by
      simp only [conjΓ_mul, hadd, htriv]⟩
  refine ⟨hd', fun s g hg => ?_, fun z => ?_⟩
  · have hm := bdryCompat_mem Γ I hI2 s g hg
    have e : conjΓ Γ φ g = h2 s * ((h2 s)⁻¹ * conjΓ Γ φ g * h2 s) * (h2 s)⁻¹ := by group
    show d (conjΓ Γ φ g) = 0
    rw [e, hadd, hadd, hpar _ _ hm, d_inv hadd]
    ring
  · have key : frobH1 σ Γ φ⁻¹ (H1.mk σ Γ ⟨_, hd'⟩) = σ φ⁻¹ 1 • H1.mk σ Γ ⟨d, hd⟩ := by
      rw [← map_smul]
      refine congrArg (H1.mk σ Γ) (Subtype.ext (funext fun g => ?_))
      show σ φ⁻¹ (d (conjΓ Γ φ (conjΓ Γ φ⁻¹ g))) = σ φ⁻¹ 1 * d g
      rw [conj_conj_inv]
      calc σ φ⁻¹ (d g) = σ φ⁻¹ (d g • (1 : k)) := by rw [smul_eq_mul, mul_one]
        _ = d g • σ φ⁻¹ 1 := map_smul _ _ _
        _ = σ φ⁻¹ 1 * d g := by rw [smul_eq_mul, mul_comm]
    have h1 := hF z (H1.mk σ Γ ⟨_, hd'⟩)
    rw [key, map_smul, hker, smul_zero] at h1
    exact hc.mul_right_eq_zero.1 h1.symm

/-- **O4G-5b.** Iteration: `InR d → InR (d ∘ conjΓ φ^j)`. -/
theorem inR_conj_pow (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (DD : ConstData σ Γ I t) (htriv : ∀ (g : Γ) (x : k), σ g x = x) {φ : G} {τ : S → S} {h : S → Γ}
    (hI : BdryCompat Γ I φ⁻¹ τ h) {τ2 : S → S} {h2 : S → Γ} (hI2 : BdryCompat Γ I φ τ2 h2) {c : k}
    (hc : IsUnit c)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial k G k) Γ I φ⁻¹ τ h hI x) (frobH1 σ Γ φ⁻¹ y) =
      c * constPair H DD x y) (j : ℕ) :
    ∀ {d : Γ → k}, InR H DD d → InR H DD (fun g => d (conjΓ Γ (φ ^ j) g)) := by
  induction j with
  | zero =>
    intro d hR
    have e : (fun g => d (conjΓ Γ (φ ^ 0) g)) = d := funext fun g => congrArg d (Subtype.ext (by simp))
    rw [e]
    exact hR
  | succ j ih =>
    intro d hR
    have e : (fun g => d (conjΓ Γ (φ ^ (j + 1)) g)) =
        fun g => (fun g' => d (conjΓ Γ φ g')) (conjΓ Γ (φ ^ j) g) :=
      funext fun g => congrArg d (Subtype.ext (by simp only [conjΓ_val, pow_succ]; group))
    rw [e]
    exact ih (inR_conj H DD htriv hI hI2 hc hF hR)

end Gen

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

open TameInertia

section Sep

variable {N : ℕ} [NeZero N] {A : Type*} [AddCommGroup A]

/-- `ℤ/N`-valued characters separate the points of an `N`-torsion group. -/
theorem exists_zmod_hom_ne_zero (hN : ∀ a : A, N • a = 0) {a : A} (ha : a ≠ 0) :
    ∃ ψ : A →+ ZMod N, ψ a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  have hex : ∀ b : A, ∃ z : ZMod N, toQCircle N z = c b := fun b =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hN b, map_zero])
  choose ψ hψ using hex
  have hadd : ∀ b b', ψ (b + b') = ψ b + ψ b' := fun b b' =>
    toQCircle_injective N (by rw [map_add, hψ, hψ, hψ, map_add])
  refine ⟨AddMonoidHom.mk' ψ hadd, fun h0 => hc ?_⟩
  have h1 : toQCircle N (ψ a) = c a := hψ a
  rw [← h1, show ψ a = 0 from h0, map_zero]

theorem eq_of_zmod_hom (hN : ∀ a : A, N • a = 0) {a b : A} (h : ∀ ψ : A →+ ZMod N, ψ a = ψ b) : a = b := by
  by_contra hab
  obtain ⟨ψ, hψ⟩ := exists_zmod_hom_ne_zero hN (sub_ne_zero.2 hab)
  exact hψ (by rw [map_sub, h ψ, sub_self])

end Sep

section Span

variable {N : ℕ} [NeZero N] {k : Type*} [CommRing k] (ι : ZMod N →+* k)

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- **Coordinates of `k`-valued parabolic homomorphisms** from a `ℤ/N` dual basis. -/
theorem span_of_zmod {P : Γ → Prop} {r : ℕ} (χ : Fin r → Γ → ZMod N) (e : Fin r → Γ)
    (hspan : ∀ y : Γ → ZMod N, IsParHom P y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {x : Γ → k} (hx : IsParHom P x) (g : Γ) : x g = ∑ i, ι (χ i g) * x (e i) := by
  refine eq_of_zmod_hom (nsmul_eq_zero_of_hom ι) fun ψ => ?_
  rw [hspan _ (hx.comp ψ) g, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [zmod_hom_map_mul, mul_comm]

end Span

section Mat

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

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

variable {ι χ}

variable {σ : Representation k G k}

theorem parHomL_eval (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {x : Γ → k} (hx : IsParHom (InBdry I) x) : parHomL ι χ (fun i => x (e i)) = x := by
  funext g
  rw [parHomL_apply, span_of_zmod ι χ e hspan hx g]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable (ι)

theorem eRlin_surjective (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    Function.Surjective (eRlin ι htriv hχ) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have hx := isParHom_of_mem_Z1par (x := (z : Γ → k)) htriv (Submodule.mem_comap.1 hz)
  refine ⟨fun i => (z : Γ → k) (e i), Subtype.ext ?_⟩
  show H1.mk σ Γ (parZ1 ι htriv hχ _) = H1.mk σ Γ z
  congr 1
  exact Subtype.ext (parHomL_eval hspan hx)

/-- `eR : k^r ≃ H¹_par(Γ, k(1))`. -/
def eR (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    (Fin r → k) ≃ₗ[k] H1par σ Γ I :=
  LinearEquiv.ofBijective (eRlin ι htriv hχ) ⟨eRlin_injective ι htriv hχ hδ, eRlin_surjective ι htriv hχ hspan⟩

theorem eR_coe (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) (l : Fin r → k) :
    (eR ι htriv hχ hδ hspan l : H1 σ Γ) = H1.mk σ Γ (parZ1 ι htriv hχ l) := rfl

theorem eLlin_surjective (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    Function.Surjective (eLlin ι hχ) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨p, rfl⟩ :=
    (Submodule.mkQ_surjective _ : Function.Surjective (H1c.mk (Representation.trivial k G k) Γ I)) y
  have hx := isParHom_of_mem_Z1c p.2
  refine ⟨fun i => (p : (Γ → k) × (S → k)).1 (e i), ?_⟩
  have hp : p = parZ1c ι hχ (fun i => (p : (Γ → k) × (S → k)).1 (e i)) +
      ⟨((0 : Γ → k), (p : (Γ → k) × (S → k)).2), zero_mem_Z1c Γ I _⟩ := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (p : (Γ → k) × (S → k)).1 = parHomL ι χ (fun i => (p : (Γ → k) × (S → k)).1 (e i)) + 0
      rw [add_zero, parHomL_eval hspan hx]
    · show (p : (Γ → k) × (S → k)).2 = 0 + (p : (Γ → k) × (S → k)).2
      rw [zero_add]
  have h0 : (LinearMap.range (bdryMap (k := k) Γ I)).mkQ (bdryMap (k := k) Γ I (p : (Γ → k) × (S → k)).2) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ _)
  rw [bdryMap_apply, H1c.mk] at h0
  conv_rhs => rw [hp, map_add, map_add, h0, add_zero]
  rfl

/-- `eL : k^r ≃ H¹_c(Γ, k) / im(k^S)`. -/
def eL (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    (Fin r → k) ≃ₗ[k] H1c (Representation.trivial k G k) Γ I ⧸ LinearMap.range (bdryMap (k := k) Γ I) :=
  LinearEquiv.ofBijective (eLlin ι hχ) ⟨eLlin_injective ι hχ hδ, eLlin_surjective ι hχ hspan⟩

theorem eL_apply (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) (l : Fin r → k) :
    eL ι hχ hδ hspan l = Submodule.Quotient.mk (H1c.mk (Representation.trivial k G k) Γ I (parZ1c ι hχ l)) := rfl

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

variable [Nonempty S]

/-- **The parabolic block in coordinates** is the matrix pairing of `ι(M)`. -/
theorem pair_eLR {σ : Representation k G k}
    (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {U : Fin r → Fin r → Γ → ZMod N} (hU : IsPrimFam χ U) (l μ : Fin r → k) :
    pairQuotSub (constPair H D) _ _ (constPair_h0 H D) (eL ι hχ hδ hspan l) (eR ι D.triv hχ hδ hspan μ) =
      Matrix.toLinearMap₂' k ((lamMat t U).map ι) l μ := by
  rw [eL_apply, pairQuotSub_apply, eR_coe,
    constPair_mk H D (parZ1c ι hχ l) (parZ1 ι D.triv hχ μ) (primL ι U l μ) (isPrim_primL ι D.triv hU l μ),
    parZ1c_snd]
  simp only [Pi.zero_apply, zero_mul, zero_sub, Finset.sum_neg_distrib]
  rw [Matrix.toLinearMap₂'_apply]
  have hterm : ∀ i j, l i • μ j • (lamMat t U).map ι i j = -∑ s, l i * (μ j * ι (U i j (tG t s))) := by
    intro i j
    simp only [smul_eq_mul, Matrix.map_apply, lamMat, Matrix.of_apply, map_neg, map_sum, mul_neg,
      Finset.mul_sum]
  simp only [hterm, Finset.sum_neg_distrib]
  congr 1
  simp only [primL]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)

/-- **O5d.** If the `ℤ/N`-valued parabolic homomorphisms have a dual basis `χ_i`, `e_j`, then perfectness of the
parabolic block of the constant pairing over `ℤ/N` implies it over every coefficient ring `Λ ← ℤ/N`. -/
theorem parabolic_of_zmod {Λ : Type} [CommRing Λ] (ιΛ : ZMod N →+* Λ)
    {σ0 : Representation (ZMod N) G (ZMod N)} {σΛ : Representation Λ G Λ}
    (H0 : CupHyp (Representation.trivial (ZMod N) G (ZMod N)) σ0 σ0 (LinearMap.mul (ZMod N) (ZMod N)) Γ)
    (D0 : ConstData σ0 Γ I t)
    (HΛ : CupHyp (Representation.trivial Λ G Λ) σΛ σΛ (LinearMap.mul Λ Λ) Γ) (DΛ : ConstData σΛ Γ I t)
    (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    (h0 : (pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)).IsPerfPair) :
    (pairQuotSub (constPair HΛ DΛ) _ _ (constPair_h0 HΛ DΛ)).IsPerfPair := by
  obtain ⟨U, hU⟩ : ∃ U : Fin r → Fin r → Γ → ZMod N, IsPrimFam χ U := by
    choose U hU using fun i j => exists_prim H0
      (mem_Z1_of_isParHom (σ := Representation.trivial (ZMod N) G (ZMod N)) (fun _ _ => rfl) (hχ i))
      (mem_Z1_of_isParHom D0.triv (hχ j))
    refine ⟨U, fun i j => ⟨(hU i j).1, fun g h => ?_⟩⟩
    have := (hU i j).2 g h
    simpa only [cupCochain, LinearMap.mul_apply', D0.triv] using this
  have hid : (lamMat t U).map (RingHom.id (ZMod N)) = lamMat t U := Matrix.ext fun _ _ => rfl
  have hM : (Matrix.toLinearMap₂' (ZMod N) (lamMat t U)).IsPerfPair := by
    have := h0
    refine LinearMap.IsPerfPair.congr (p := pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0))
      (eM := eL (RingHom.id _) hχ hδ hspan) (eN := eR (RingHom.id _) D0.triv hχ hδ hspan) (q := _) ?_
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have := pair_eLR (RingHom.id (ZMod N)) H0 D0 hχ hδ hspan hU ((eL (RingHom.id _) hχ hδ hspan).symm x)
      ((eR (RingHom.id _) D0.triv hχ hδ hspan).symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hid] at this
    exact this.symm
  have := isPerfPair_map ιΛ hM
  refine LinearMap.IsPerfPair.congr (p := Matrix.toLinearMap₂' Λ ((lamMat t U).map ιΛ))
    (eM := (eL ιΛ hχ hδ hspan).symm) (eN := (eR ιΛ DΛ.triv hχ hδ hspan).symm) (q := _) ?_
  refine LinearMap.ext fun l => LinearMap.ext fun μ => ?_
  exact pair_eLR ιΛ HΛ DΛ hχ hδ hspan hU l μ

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

variable (P : AddSubgroup (Γ → ZMod N)) (Ψ : (Fin r → ZMod N) ≃+ P)

theorem exists_dual (hP : ∀ y ∈ P, ∀ a b : Γ, y (a * b) = y a + y b) (j : Fin r) :
    ∃ g : Γ, ∀ i, chiOf P Ψ i g = if i = j then 1 else 0 := by
  classical
  have hmul : ∀ i (a b : Γ), chiOf P Ψ i (a * b) = chiOf P Ψ i a + chiOf P Ψ i b :=
    fun i => hP _ (chiOf_mem P Ψ i)
  have hone : ∀ i, chiOf P Ψ i 1 = 0 := fun i => by
    have h := hmul i 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ i (a : Γ), chiOf P Ψ i a⁻¹ = -chiOf P Ψ i a := fun i a => by
    have h := hmul i a⁻¹ a
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let R : AddSubgroup (Fin r → ZMod N) :=
    { carrier := Set.range fun g : Γ => fun i => chiOf P Ψ i g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, funext fun i => hmul i a b⟩
      zero_mem' := ⟨1, funext fun i => hone i⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a⁻¹, funext fun i => hinv i a⟩ }
  by_contra hne
  simp only [not_exists] at hne
  have hmem : (fun i => if i = j then (1 : ZMod N) else 0) ∉ R := by
    rintro ⟨g, hg⟩
    exact hne g fun i => congrFun hg i
  have hN : ∀ a : (Fin r → ZMod N) ⧸ R, N • a = 0 := by
    intro a
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hv : N • v = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
    rw [← QuotientAddGroup.mk_nsmul, hv, QuotientAddGroup.mk_zero]
  have hne0 : (QuotientAddGroup.mk (fun i => if i = j then (1 : ZMod N) else 0) :
      (Fin r → ZMod N) ⧸ R) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hmem
  obtain ⟨ψ, hψ⟩ := exists_zmod_hom_ne_zero hN hne0
  let ψ' : (Fin r → ZMod N) →+ ZMod N := ψ.comp (QuotientAddGroup.mk' R)
  let c : Fin r → ZMod N := fun i => ψ' (stdV i)
  have hc : Ψ c = 0 := by
    apply Subtype.ext
    funext g
    have h0 : ψ' (fun i => chiOf P Ψ i g) = 0 := by
      show ψ (QuotientAddGroup.mk (fun i => chiOf P Ψ i g)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (show (fun i => chiOf P Ψ i g) ∈ R from ⟨g, rfl⟩), map_zero]
    have h1 := addHom_apply_sum ψ' (fun i => chiOf P Ψ i g)
    rw [h0] at h1
    rw [AddSubgroup.coe_zero, Pi.zero_apply, psi_apply, h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc0 : c = 0 := Ψ.injective (hc.trans (map_zero Ψ).symm)
  apply hψ
  show ψ' (fun i => if i = j then (1 : ZMod N) else 0) = 0
  rw [addHom_apply_sum ψ']
  exact Finset.sum_eq_zero fun i _ => by
    rw [show ψ' (stdV i) = 0 from congrFun hc0 i, smul_zero]

/-- **Dual basis.** `χ_i = Ψ(δ_i)` has dual elements `e_j ∈ Γ` and spans `P` in coordinates `y(e_i)`. -/
theorem exists_dualBasis (hP : ∀ y ∈ P, ∀ a b : Γ, y (a * b) = y a + y b) :
    ∃ e : Fin r → Γ, (∀ i j, chiOf P Ψ i (e j) = if i = j then 1 else 0) ∧
      ∀ y ∈ P, ∀ g, y g = ∑ i, y (e i) * chiOf P Ψ i g := by
  choose e he using exists_dual P Ψ hP
  exact ⟨e, fun i j => he j i, fun y hy g => span_of_dual P Ψ e (fun i j => he j i) hy g⟩

end Basis

section Perf

variable {N : ℕ} [NeZero N] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {r : ℕ} {χ : Fin r → Γ → ZMod N} {e : Fin r → Γ}

/-- **O9 over `ℤ/N`.** With a dual basis of the parabolic homomorphisms, a zero right kernel of `constPair`
(`InR d → d = 0`) makes the parabolic block perfect. -/
theorem parabolic_of_rightKer {σ0 : Representation (ZMod N) G (ZMod N)}
    (H0 : CupHyp (Representation.trivial (ZMod N) G (ZMod N)) σ0 σ0 (LinearMap.mul (ZMod N) (ZMod N)) Γ)
    (D0 : ConstData σ0 Γ I t) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    (hR : ∀ d : Γ → ZMod N, InR H0 D0 d → d = 0) :
    (pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)).IsPerfPair := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Fin r → Fin r → Γ → ZMod N, IsPrimFam χ U := by
    choose U hU using fun i j => exists_prim H0
      (mem_Z1_of_isParHom (σ := Representation.trivial (ZMod N) G (ZMod N)) (fun _ _ => rfl) (hχ i))
      (mem_Z1_of_isParHom D0.triv (hχ j))
    refine ⟨U, fun i j => ⟨(hU i j).1, fun g h => ?_⟩⟩
    have := (hU i j).2 g h
    simpa only [cupCochain, LinearMap.mul_apply', D0.triv] using this
  have hid : (lamMat t U).map (RingHom.id (ZMod N)) = lamMat t U := Matrix.ext fun _ _ => rfl
  have hlin : ∀ μ, (lamMat t U) *ᵥ μ = 0 → μ = 0 := by
    intro μ hμ
    have hpair : ∀ l, pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)
        (eL (RingHom.id _) hχ hδ hspan l) (eR (RingHom.id _) D0.triv hχ hδ hspan μ) = 0 := by
      intro l
      rw [pair_eLR (RingHom.id _) H0 D0 hχ hδ hspan hU l μ, hid, toLinearMap₂'_eq_dot,
        ← dotProduct_mulVec, hμ, dotProduct_zero]
    have hd : InR H0 D0 (parHomL (RingHom.id (ZMod N)) χ μ) := by
      refine ⟨(parZ1 (RingHom.id _) D0.triv hχ μ).2, fun s g hg => (parHomL_isParHom hχ μ).2.2 g ⟨s, hg⟩,
        fun z => ?_⟩
      obtain ⟨l, hl⟩ := (eL (RingHom.id _) hχ hδ hspan).surjective (Submodule.Quotient.mk z)
      have h := hpair l
      rw [hl, pairQuotSub_apply, eR_coe] at h
      exact h
    have h0 := hR _ hd
    funext j
    have h1 := congrFun h0 (e j)
    rw [parHomL_e hδ] at h1
    exact h1
  have hinj : Function.Injective (lamMat t U).mulVec := fun a b hab =>
    sub_eq_zero.1 (hlin _ (by rw [mulVec_sub, hab, sub_self]))
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.1 (Finite.injective_iff_surjective.1 hinj)
  have hBA : (↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod N)) * lamMat t U = 1 := by
    rw [← hu]
    exact u.inv_mul
  have hAB : lamMat t U * (↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod N)) = 1 := by
    rw [← hu]
    exact u.mul_inv
  have hM := isPerfPair_toLinearMap₂' hBA hAB
  refine LinearMap.IsPerfPair.congr (p := Matrix.toLinearMap₂' (ZMod N) (lamMat t U))
    (eM := (eL (RingHom.id _) hχ hδ hspan).symm) (eN := (eR (RingHom.id _) D0.triv hχ hδ hspan).symm)
    (q := _) ?_
  refine LinearMap.ext fun l => LinearMap.ext fun μ => ?_
  have := pair_eLR (RingHom.id (ZMod N)) H0 D0 hχ hδ hspan hU l μ
  rw [hid] at this
  exact this

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

variable {σ : Representation (ZMod N) G (ZMod N)}

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq in
theorem not_dvd_card {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) : ¬ l ∣ Fintype.card Fq := by
  rw [hq]
  intro h
  have hlp : l = p :=
    (Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 ((Fact.out : l.Prime).dvd_of_dvd_pow h)
  exact hl (by rw [hlp]; exact CharP.cast_eq_zero F p)

end S3

end

end CupDuality
end RamanujanPetersson


end


