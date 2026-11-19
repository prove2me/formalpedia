-- Prove2me | Definitions.Def_RPLib_S4_CDPack36b
-- name    : RPLib_S4_CDPack36b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T12:08:42.653701+00:00
-- url     : https://prove2.me/theorems/ff93000a-3d59-48c2-b994-8858a0526670
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 36b of 71
-- statement:
--   Part 36b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
--   * `Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack36
import Definitions.Def_RPLib_S4_CDPack33d

/-!
# Curve-duality library package, part 36b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
* `Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_CommJ =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)

`H_comm_lawChunk`: the chunk group `H` of Weil's law is commutative (the law is commutative at points,
`lawData_rel_comm`, so `λ_a = ρ_a`); **`isCommMonObj_Jac`**: the Jacobian `Jac K F` is a commutative group scheme.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem preComm_lawPre : PreComm (lawPre K F) := fun x x' e1 e2 => lawData_rel_comm (lawData K F) x x' e1 e2

theorem chunkComm_lawChunk : ChunkComm (lawChunk K F) :=
  chunkComm_toStrict (lawPre K F).toAff (affComm_toAff (lawPre K F) (preComm_lawPre K F))

/-- The chunk group of Weil's law is commutative. -/
theorem H_comm_lawChunk (σ τ : (lawChunk K F).H) : σ * τ = τ * σ :=
  H_comm_of_chunkComm (lawChunk K F) (chunkComm_lawChunk K F) σ τ

/-- **L22: the Jacobian is commutative.** -/
instance isCommMonObj_Jac : IsCommMonObj (Jac K F) := isCommMonObj_Jac_of_comm K F (H_comm_lawChunk K F)

end Jac

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_PicLaw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)

* `psiJ K F : X0 → PicK`, additive (`chunkAdd_lawChunk`) and rigid (`chunkRigid_lawChunk`); `card_lawPt`, `deg_psiJ`;
* **`jacPic0 K F : H →* Multiplicative (Pic0K K F)`**, `jacPic0_injective`, `jacPic0_lamB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The class function** `ψ : X0 → Pic`, `ψ(D) = [D] - [Θ]` at closed points. -/
noncomputable def psiJ : X0 K F → PicK K F := psiS (psiA (lawPre K F) (psiL (lawData K F)))

theorem chunkAdd_lawChunk : ChunkAdd (lawChunk K F) (psiJ K F) :=
  chunkAdd_toStrict (lawPre K F).toAff (affAdd_toAff (lawPre K F) fun x => lawData_add (lawData K F) x)

theorem chunkRigid_lawChunk : ChunkRigid (lawChunk K F) (psiJ K F) :=
  chunkRigid_of_m (lawChunk K F) (rigid_toStrict (lawPre K F).toAff
    (affRigid_toAff (lawPre K F) fun x y e => lawData_rigid (lawData K F) x y e))

/-- Every closed point of `X0` is a reduced divisor of degree `g`. -/
theorem card_lawPt (yR : LawRing K F →ₐ[K] K) :
    (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))).card = genusFK K F := by
  obtain ⟨x, hx⟩ := (lawPre K F).toAff.fibL yR
  have e1 : pL (x.comp (extK (lawPre K F).u0 ((lawPre K F).t1 * (lawPre K F).t2) (lawPre K F).μ)) =
      yR.comp (awayι (K := K) (lawPre K F).u0) :=
    (extK_pL (lawPre K F).u0 ((lawPre K F).t1 * (lawPre K F).t2) (lawPre K F).μ x).trans
      (congrArg (fun z => z.comp (awayι (K := K) (lawPre K F).u0)) hx)
  have e2 : yR.comp (awayι (K := K) (lawPre K F).u0) =
      ((lawData K F).mB ((x.comp (extK (lawPre K F).u0 ((lawPre K F).t1 * (lawPre K F).t2)
        (lawPre K F).μ)).comp (nestK (K := K) (lawData K F).mU))).comp (iL K F) :=
    e1.symm.trans ((lawData K F).mB_L _).symm
  rw [e2]
  exact card_mBase_L (T := T0 K F) (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1
    (iL K F) (iR K F) _

theorem deg_psiJ (p : X0 K F) (hp : IsClosed ({p} : Set (X0 K F))) :
    degPicK K F (psiJ K F p) = (genusFK K F : ℤ) -
      (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1).deg := by
  obtain ⟨yR, rfl⟩ := exists_kpt (K := K) p hp
  rw [psiJ, psiS_kpt, psiA, psiL, map_sub, degPicK_clsK, degPicK_clsK, deg_Zdiv, card_lawPt]

theorem Phi_mem_Pic0K (σ : (lawChunk K F).H) : Phi (psiJ K F) σ.1 ∈ Pic0K K F := by
  obtain ⟨x, y, hx, hy, h⟩ := exists_takes σ.1
  rw [Phi_spec (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) σ.1 σ.2 hx hy h, mem_Pic0K, map_sub,
    deg_psiJ K F y hy, deg_psiJ K F x hx, sub_self]

/-- **The class map** `H → Pic⁰`, `σ ↦ [σ(D) - D]` (L20). -/
noncomputable def jacPic0 : (lawChunk K F).H →* Multiplicative (Pic0K K F) :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (⟨Phi (psiJ K F) σ.1, Phi_mem_Pic0K K F σ⟩ : Pic0K K F))
    fun σ τ => by
      rw [← ofAdd_add]
      exact congrArg Multiplicative.ofAdd (Subtype.ext
        (Phi_mul (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) σ.1 τ.1 σ.2 τ.2))

theorem jacPic0_apply (σ : (lawChunk K F).H) :
    ((Multiplicative.toAdd (jacPic0 K F σ) : Pic0K K F) : PicK K F) = Phi (psiJ K F) σ.1 := rfl

theorem jacPic0_injective : Function.Injective (jacPic0 K F) := by
  intro σ τ h
  apply PhiHom_injective (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) (chunkRigid_lawChunk K F)
  rw [PhiHom_apply, PhiHom_apply]
  exact congrArg Multiplicative.ofAdd ((jacPic0_apply K F σ).symm.trans
    ((congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) h).trans (jacPic0_apply K F τ)))

/-- `ψ(a)` lies in `Pic⁰` and is the class of `λ_a`. -/
theorem jacPic0_lamB (a : X0 K F) (ha : IsClosed ({a} : Set (X0 K F))) :
    ((Multiplicative.toAdd (jacPic0 K F ⟨(lawChunk K F).lamB a ha, (lawChunk K F).lamB_mem_H a ha⟩) :
      Pic0K K F) : PicK K F) = psiJ K F a := by
  rw [jacPic0_apply, Phi_lamB (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) a ha]

end Jac

end RamanujanPetersson.JacComplete

end


