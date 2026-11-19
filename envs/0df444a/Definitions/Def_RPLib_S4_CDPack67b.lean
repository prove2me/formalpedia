-- Prove2me | Definitions.Def_RPLib_S4_CDPack67b
-- name    : RPLib_S4_CDPack67b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:16:45.85304+00:00
-- url     : https://prove2.me/theorems/bb063aa8-7ca7-4350-8166-5b9866fa2c69
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 67b of 71
-- statement:
--   Part 67b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacFrob_MorE`: S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness
--   * `Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack67
import Definitions.Def_RPLib_S4_CDPack24

/-!
# Curve-duality library package, part 67b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacFrob_MorE`: S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness
* `Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacFrob_MorE =====
section

/-!
# S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness

* `eJ_mor : eJ φ ≫ (mor φ hφ).left = Spec.map (rho φ) ≫ jX0`;
* `eq_mor`: `mor φ hφ` is the only map `J ⟶ J` over `K` with this property.
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

theorem eJ_mor (hφ : φ (lawPre K F).u0 ≠ 0) :
    eJ φ ≫ (mor φ hφ).left = Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F := by
  have h : (eJ φ).opensRange.ι ≫ (mor φ hφ).left =
      (eJ φ).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F :=
    ι_extJ (pmap φ hφ) (pmap_over φ hφ)
  rw [← (eJ φ).isoOpensRange_hom_ι, Category.assoc, h, Iso.hom_inv_id_assoc]

/-- `mor φ hφ` is the only map `J ⟶ J` over `K` restricting to `Spec (rho φ)` on `D(φ u0)`. -/
theorem eq_mor (hφ : φ (lawPre K F).u0 ≠ 0) (ψ : Jac K F ⟶ Jac K F)
    (h : eJ φ ≫ ψ.left = Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F) : ψ = mor φ hφ :=
  eq_extJ (pmap φ hφ) (pmap_over φ hφ) ψ (by
    show (eJ φ).opensRange.ι ≫ ψ.left =
      (eJ φ).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F
    rw [← (eJ φ).isoOpensRange_inv_comp, Category.assoc, h])

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

set_option synthInstance.maxHeartbeats 100000 in
/-- **`π_J⁰`**: the morphism of `J = J_{F-bar}` over `k-bar` induced by `Φ = (·)^q ∘ σ⁻¹` on `S_g`. -/
noncomputable def piJ0 : Jac (kbar Fq Ω) (Fbar Fq F Ω) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω) :=
  mor (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) (PhiS_u0_ne Fq F Ω hk)

set_option synthInstance.maxHeartbeats 100000 in
theorem eJ_piJ0 :
    eJ (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) ≫ (piJ0 Fq F Ω hk).left =
      Spec.map (CommRingCat.ofHom (rho (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)))).toRingHom) ≫
        jX0 (kbar Fq Ω) (Fbar Fq F Ω) :=
  eJ_mor _ _

end PiJ0

end RamanujanPetersson.JacFrob

end


