-- Prove2me | Definitions.Def_RPLib_S4_CDPack67
-- name    : RPLib_S4_CDPack67
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:13:14.01057+00:00
-- url     : https://prove2.me/theorems/9fea3b23-2f89-4df0-9de2-3ecd0bd1e420
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 67 of 71
-- statement:
--   Part 67 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacFrob_MorR`: S4-JacFrob, part MorR: the ring map `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`
--   * `Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack54b

/-!
# Curve-duality library package, part 67 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacFrob_MorR`: S4-JacFrob, part MorR: the ring map `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`
* `Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
-/

set_option autoImplicit false

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

/-- **The morphism `J ⟶ J` over `K` induced by `φ`** (Weil extension of `pmap`). -/
noncomputable def mor (hφ : φ (lawPre K F).u0 ≠ 0) : Jac K F ⟶ Jac K F :=
  extJ (pmap φ hφ) (pmap_over φ hφ)

end Mor

end RamanujanPetersson.JacFrob

end


