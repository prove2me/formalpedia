-- Prove2me | Definitions.Def_RPLib_F2_049
-- name    : RPLib_F2_049
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T19:23:53.703732+00:00
-- url     : https://prove2.me/theorems/82458aa2-d9a4-4a25-8abb-96bdfbd3f1e9
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 049 of 70
-- statement:
--   File 049 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--   * `S4.Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
--   * `S4.Def_RP_JacFrob_MorR`: S4-JacFrob, part MorR: the ring map `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`
--   * `S4.Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
--   * `S4.Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
--   * `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_047

/-!
# Ramanujan-Petersson curve library (flat edition), file 049 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
* `S4.Def_RP_JacFrob_JJ`: S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field
* `S4.Def_RP_JacFrob_MorR`: S4-JacFrob, part MorR: the ring map `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`
* `S4.Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
* `S4.Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
* `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Curve7 =====
section

/-!
# Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)

* `kapM cK : J ⟶ J`, `e ↦ c_K e⁻¹`; `mu1 P0 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`; `mu2 P0 c2`, `(e, q) ↦ AJ(q)² e c_2`;
* `Bad P0 c2 := mu1⁻¹ W ∩ mu2⁻¹ (J \ jX0 (X0))`, closed in `J × X1`;
* **`Ogood P0 cK c2 := Wᶜ ∩ kapM⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`**, open (`isOpen_Ogood`: `pr_J` is closed, `X1` proper);
* **`isGoodFor_of_mem`**: every `K`-point of `Ogood` is good;
* `not_mem_image_Bad`, `mem_Ogood_of`: the converse criterion (all `K`-points `(e, q)` off `Bad`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve7

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

instance universallyClosed_fstJ : UniversallyClosed (fst (Jac K F) (X1O K F)).left := by
  show UniversallyClosed (pullback.fst (Jac K F).hom (toSpecK K (algebraMap K[X] F X) 1))
  infer_instance

end Curve7

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_JacFrob_JJ =====
section

/-!
# S4-JacFrob, part JJ: instances on `J` and `J ⊗ J` over an algebraically closed field

* `isIntegral_JacL : IsIntegral (Jac K F).left`;
* `isIntegral_JacJac : IsIntegral (Jac K F ⊗ Jac K F).left` (S4-IntersectA `isIntegral_pullback`);
* `isReduced_JacJac`, `lft_JacJac`, `smooth_JacJac`: what `extJ` (with `V = J`) and `eq_of_kpt_eq`
  (on `J ⊗ J`) ask for.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory RamanujanPetersson.JacComplete

universe u

section JJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isReduced_JacJac : IsReduced (Jac K F ⊗ Jac K F).left := inferInstance

instance lft_JacJac : LocallyOfFiniteType (Jac K F ⊗ Jac K F).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance smooth_JacJac : Smooth (Jac K F ⊗ Jac K F).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end JJ

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_MorR =====
section

/-!
# S4-JacFrob, part MorR: the ring map `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`

Generic (JacComplete context): for a `K`-algebra map `φ : S_g → S_g`, `vA φ = φ u0` in `S_g[1/u0]`,
`BRing φ = S_g[1/u0][1/φ u0]`, `gB φ : S_g → BRing φ`, `rho φ` (`rho_algebraMap`), and `vA_ne` (`φ u0 ≠ 0 → vA φ ≠ 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Mor

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- `φ u0` in `S_g[1/u0]`. -/
noncomputable abbrev vA : LawRing K F := algebraMap _ (LawRing K F) (φ (lawPre K F).u0)

/-- The ring `S_g[1/u0][1/φ u0]`. -/
abbrev BRing : Type u := Localization.Away (vA φ)

/-- `S_g → S_g[1/u0][1/φ u0]`, `s ↦ φ s`. -/
noncomputable def gB : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] BRing φ :=
  (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)).comp ((IsScalarTower.toAlgHom K _ (LawRing K F)).comp φ)

theorem gB_apply (s : SymRing K (Places.Rfin K F) (genusFK K F)) :
    gB φ s = algebraMap (LawRing K F) (BRing φ) (algebraMap _ (LawRing K F) (φ s)) := rfl

theorem isUnit_gB : IsUnit (gB φ (lawPre K F).u0) := IsLocalization.Away.algebraMap_isUnit (vA φ)

/-- `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`, `s / u0^n ↦ φ s / (φ u0)^n`. -/
noncomputable def rho : LawRing K F →ₐ[K] BRing φ :=
  IsLocalization.Away.liftAlgHom (A := K) (S := LawRing K F) (lawPre K F).u0 (isUnit_gB φ)

theorem rho_algebraMap (s : SymRing K (Places.Rfin K F) (genusFK K F)) :
    rho φ (algebraMap _ (LawRing K F) s) = gB φ s := by
  rw [rho, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

theorem vA_ne (hφ : φ (lawPre K F).u0 ≠ 0) : vA φ ≠ 0 := by
  intro h
  obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (M := Submonoid.powers (lawPre K F).u0) (S := LawRing K F) _).1 h
  exact hφ ((mul_eq_zero.1 hm).resolve_left (pow_ne_zero n (lawPre_u0_ne K F)))

end Mor

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Mor =====
section

/-!
# S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`): a `K`-algebra map `φ : S_g → S_g` with
`φ u0 ≠ 0` gives `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`, hence the partial map `jX0(D(φ u0)) ⇢ J`
(`Spec (rho φ)` followed by `jX0`), and Weil extension (`extJ`) turns it into `mor φ hφ : J ⟶ J` over `K`:
`eJ φ : Spec S_g[1/u0][1/φ u0] ⟶ J`; `eJ_mor`, `eq_mor` are in `Def_RP_JacFrob_MorE`.
The special case `piJ0 hk := mor (PhiS hk g)` is in `Def_RP_JacFrob_PiJ0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Mor

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- `D(φ u0) ⊆ X0`, as `Spec S_g[1/u0][1/φ u0] ⟶ X0`. -/
noncomputable def eB : Spec (.of (BRing φ)) ⟶ X0 K F :=
  Spec.map (CommRingCat.ofHom (algebraMap (LawRing K F) (BRing φ)))

instance isOpenImmersion_eB : IsOpenImmersion (eB φ) := by
  unfold eB; infer_instance

/-- `D(φ u0) ⊆ X0 ⊆ J`. -/
noncomputable def eJ : Spec (.of (BRing φ)) ⟶ (Jac K F).left := eB φ ≫ jX0 K F

instance isOpenImmersion_eJ : IsOpenImmersion (eJ φ) := by
  unfold eJ; infer_instance

theorem dense_eJ (hφ : φ (lawPre K F).u0 ≠ 0) : Dense ((eJ φ).opensRange : Set (Jac K F).left) := by
  have : IsDomain (BRing φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (vA_ne φ hφ))
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (BRing φ)) := inferInstance
  exact (eJ φ).opensRange.isOpen.dense ⟨(eJ φ).base p, Scheme.Hom.mem_opensRange.2 ⟨p, rfl⟩⟩

/-- **The partial map `J ⇢ J`** on `jX0(D(φ u0))`: `Spec (rho φ)` followed by `jX0`. -/
noncomputable def pmap (hφ : φ (lawPre K F).u0 ≠ 0) : (Jac K F).left.PartialMap (Jac K F).left where
  domain := (eJ φ).opensRange
  dense_domain := dense_eJ φ hφ
  hom := (eJ φ).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F

theorem spec_rho_over :
    Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ (X0 K F ↘ Spec (.of K)) =
      eB φ ≫ (X0 K F ↘ Spec (.of K)) := by
  rw [eB, specOverSpec_over, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  exact ((rho φ).commutes c).trans (IsScalarTower.algebraMap_apply K (LawRing K F) (BRing φ) c)

theorem pmap_over (hφ : φ (lawPre K F).u0 ≠ 0) :
    (pmap φ hφ).hom ≫ (Jac K F).hom = (pmap φ hφ).domain.ι ≫ (Jac K F).hom := by
  show ((eJ φ).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F) ≫ (Jac K F).hom =
    (eJ φ).opensRange.ι ≫ (Jac K F).hom
  rw [← cancel_epi (eJ φ).isoOpensRange.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc]
  rw [jX0_over, eJ, Category.assoc, jX0_over, spec_rho_over]

end Mor

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_PiJ0 =====
section

/-!
# S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`

* `PhiS_u0_ne`: `Φ_S u0 ≠ 0` (`symMap_injective` + `PhiR_injective`);
* `piJ0 hk : J ⟶ J` over `k-bar` (`J = Jac k-bar F-bar`), the morphism induced by `Φ = (·)^q ∘ σ⁻¹` on `S_g`;
* `eJ_piJ0`: on `D(Φ_S u0) ⊆ X0` it is `Spec (rho Φ_S)` followed by `jX0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

section PiJ0

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
theorem PhiS_u0_ne :
    PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)) (lawPre (kbar Fq Ω) (Fbar Fq F Ω)).u0 ≠ 0 :=
  (map_ne_zero_iff _ (symMap_injective _ (PhiR_injective Fq F Ω hk))).2 (lawPre_u0_ne _ _)

end PiJ0

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val =====
section

/-!
# S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`):
* `kptEquiv_of_jX0`, `jacPicEquiv_of_jX0`: a `K`-point `a` of `J` with closed point `jX0 x` (`x` closed in `X0`) has value
  `lamB x` in `H` and class `psiJ x` in `Pic⁰`;
* `eJ_kpt`, `mor_kpt`: `mor φ hφ` sends `jX0 (kpt (z ∘ ι))` to `jX0 (kpt (z ∘ rho φ))` for `z : S_g[1/u0][1/φ u0] →ₐ[K] K`;
* `jacPicEquiv_mor`: the class of `a ≫ mor φ hφ` is `psiJ (kpt (z ∘ rho φ))`;
* `zOf`, `zOf_comp`: every `y` with `y (φ u0) ≠ 0` factors through `S_g[1/u0][1/φ u0]`;
* `comp_rho_S`: on `S_g`, `z ∘ rho φ` is `(z ∘ ι) ∘ φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Val

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem kptEquiv_of_jX0 (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (x : X0 K F) (hx : IsClosed ({x} : Set (X0 K F)))
    (ha : a.left (IsLocalRing.closedPoint K) = jX0 K F x) :
    kptEquiv K F a = ⟨(lawChunk K F).lamB x hx, (lawChunk K F).lamB_mem_H x hx⟩ := by
  apply Subtype.ext
  rw [kptEquiv_apply]
  show (lawChunk K F).PtT (a.left (IsLocalRing.closedPoint K)) = _
  rw [ha, jX0, (lawChunk K F).PtT_ι 1 x hx, OneMemClass.coe_one, one_mul]
  exact (lawChunk K F).lamT_eq x hx

theorem left_comp_closedPoint (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ψ : Jac K F ⟶ Jac K F) :
    (a ≫ ψ).left (IsLocalRing.closedPoint K) = ψ.left (a.left (IsLocalRing.closedPoint K)) := by
  rw [Over.comp_left]
  rfl

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

theorem eJ_kpt (z : BRing φ →ₐ[K] K) :
    eJ φ (kpt z) = jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)))) := by
  rw [eJ, Scheme.Hom.comp_apply]
  exact congrArg (fun p => jX0 K F p) (SpecMap_kpt (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)) z)

end Val

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val2 =====
section

/-!
# S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`

Generic:
* `ptOf_comp_xMap`, `symPt_comp_symMap`, `ptSet_comp_symMap`: the support of `y ∘ symMap f` is `(supp y) ∘ f`;
* `thetaK`, `psiJ_kpt`: `psiJ (kpt y) = [Z(y|S_g)] - [Θ]`; `cls_of_kpt`, `cls_mor`, `cls_mor_hom`: classes of `a` and `a ≫ mor φ hφ`.

For `J = J_{F-bar}` over `k-bar`:
* `PhiR_eq_pow`: `Φ b = (σ⁻¹ b)^q` on `Rfin`; `ptP_comp_PhiR`: the place of `χ ∘ Φ` is `σ_*` of the place of `χ`;
* `comp_PhiR_injective`, `Zdiv_image_PhiR`, `Zdiv_ptSet_PhiS`: `Z(y ∘ Φ_S) = σ_* Z(y)`;
* `cTheta = σ_*[Θ] - [Θ] ∈ Pic⁰`; **`jacPicEquiv_piJ0`**: `[a ≫ π_J⁰] = σ_*[a] + cTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory IsDedekindDomain
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR
open RamanujanPetersson.PicDescent

universe u

section SymPt

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

end SymPt

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The class `[Θ]` of the base divisor of the law chunk. -/
noncomputable abbrev thetaK : PicK K F :=
  clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1)

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Hom =====
section

/-!
# S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects

Generic (JacComplete context): `ptW` (a `K`-point of `J` inside `jX0(D(φ u0))` comes from a `K`-point of
`S_g[1/u0][1/φ u0]`), `UJ W` (the dense open `fst⁻¹W ∩ snd⁻¹W ∩ μ⁻¹W` of `J × J`), and `isMonHom_of_cls`:
a map `ψ : J ⟶ J` acting on the classes of the `K`-points over a dense open `W` through an additive map `s`
is a homomorphism of group objects. For `J = J_{F-bar}`: **`isMonHom_piJ`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- `fst⁻¹W ∩ snd⁻¹W ∩ μ⁻¹W ⊆ J × J`. -/
noncomputable def UJ (W : (Jac K F).left.Opens) : (Jac K F ⊗ Jac K F).left.Opens :=
  (fst (Jac K F) (Jac K F)).left ⁻¹ᵁ W ⊓ (snd (Jac K F) (Jac K F)).left ⁻¹ᵁ W ⊓ (μ[Jac K F]).left ⁻¹ᵁ W

variable (ψ : Jac K F ⟶ Jac K F) (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end


