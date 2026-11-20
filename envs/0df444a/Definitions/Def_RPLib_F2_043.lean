-- Prove2me | Definitions.Def_RPLib_F2_043
-- name    : RPLib_F2_043
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T17:43:36.533187+00:00
-- url     : https://prove2.me/theorems/45d22d5d-6c15-4fc9-b8fd-dff2577b11ee
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 043 of 70
-- statement:
--   File 043 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstB`: S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`
--   * `S4.Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
--   * `S4.Def_RP_JacComplete_Def`: The Jacobian (unit S4-JacComplete), part `Def`
--   * `S4.Def_RP_JacComplete_Comm`: The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)
--   * `S4.Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
--   * `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
--   * `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
--   * `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
--   * `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
--   * `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
--   * `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_040

/-!
# Ramanujan-Petersson curve library (flat edition), file 043 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstB`: S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`
* `S4.Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
* `S4.Def_RP_JacComplete_Def`: The Jacobian (unit S4-JacComplete), part `Def`
* `S4.Def_RP_JacComplete_Comm`: The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)
* `S4.Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
* `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
* `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
* `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
* `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
* `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
* `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstB =====
section

/-!
# S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`

* `LawData.toPre L hw : PreChunk K S_g`; `hw` is one point of `D(ωm)` where `(a, m(a,b)) ∈ D(ωr)` and
  `(m(a,b), b) ∈ D(ωl)`.
* `LawData.chunk L hw : StrictChunk (sR K S_g[1/u0])`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

/-- The `PreChunk` of a `LawData`, given one witness point. -/
noncomputable def toPre
    (hw : ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0) :
    PreChunk K (SymRing K (Places.Rfin K F) (genusFK K F)) where
  ω := L.ωm
  μ := L.μm
  ωr := L.ωr
  ρ := L.ρr
  ωl := L.ωl
  la := L.lal
  r_m := L.rel_r_m
  m_r x' x := L.rel_m_r x x'
  l_m := L.rel_l_m
  m_l x' x := L.rel_m_l x x'
  assoc := L.rel_assoc
  wit := hw

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw =====
section

/-!
# Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella

Milne III.7.1-7.2 (lemmas L15-L16 of `S4_COREB_ROUTE.md`). `S = S_g = SymRing K (Rfin K F) g` is the coordinate
ring of (an affine open of) `Sym^g X`.
* L15: `exists_lawData_wit` (files `Gen*`) produces law data `lawData K F`: the rule `(D, D') ↦ E` with
  `D + D' - g P0 ~ E` as a rational map `m` (`μm` on `D(ωm) ⊆ Sym^g × Sym^g`), and `r` (`ρr`) for the inverse,
  each well defined and unique on a dense open (files `Nu`, `Uniq`, `Step`, `Law`).
* L16: `lawPre K F : PreChunk K S` packages `m`, `r`, `l` with associativity and the inverse relations
  (`InstL*`, `InstR`, `InstA`, `Assoc`); `lawChunk K F` is the resulting strict group chunk on the dense open
  `D(u0) = Spec S[1/u0]` (`Shrink*`, `Sch`), stated in the form `StrictChunk (X ↘ Spec k)` used by S4-JacChunkB.
* The instances S4-JacChunkB needs on `X = Spec S[1/u0]`: reduced, irreducible, separated, locally of finite type,
  geometrically reduced; `dense_basicOpen_u0`: `D(u0)` is dense in `Spec S`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk

universe u

section Umb

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Weil's birational group law** on `S_g` (L15-L16): `m`, `r`, `l`, associativity, inverse relations. -/
noncomputable def lawPre : PreChunk K (SymRing K (Places.Rfin K F) (genusFK K F)) :=
  (lawData K F).toPre (lawData_hasWit K F).out

theorem lawPre_u0_ne : (lawPre K F).u0 ≠ 0 := (lawPre K F).u0_ne

/-- The coordinate ring `S_g[1/u0]` of the dense open carrying the group chunk. -/
abbrev LawRing : Type u := Localization.Away (lawPre K F).u0

instance isDomain_lawRing : IsDomain (LawRing K F) := (lawPre K F).isDomain_u0

instance finiteType_lawRing : Algebra.FiniteType K (LawRing K F) :=
  Algebra.FiniteType.trans (S := SymRing K (Places.Rfin K F) (genusFK K F)) inferInstance inferInstance

/-- **The group chunk of Weil's law** on `X = Spec S_g[1/u0]` (L16), in the form used by S4-JacChunkB. -/
noncomputable def lawChunk : StrictChunk (k := K) (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  (lawPre K F).toStrict'

instance isReduced_lawX : IsReduced (Spec (.of (LawRing K F))) := inferInstance

instance irreducibleSpace_lawX : IrreducibleSpace (Spec (.of (LawRing K F))) := inferInstance

instance isSeparated_lawX : (Spec (.of (LawRing K F))).IsSeparated := inferInstance

instance isSeparated_lawX_hom : IsSeparated (Spec (.of (LawRing K F)) ↘ Spec (.of K)) := inferInstance

instance locallyOfFiniteType_lawX : LocallyOfFiniteType (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  inferInstance

instance geometricallyReduced_lawX : GeometricallyReduced (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  geometricallyReduced_sR (K := K) (R := LawRing K F)

end Umb

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacComplete_Def =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Def`

Weil's group chunk theorem (S4-JacChunkA/B) applied to Weil's birational group law (S4-JacLaw):
* `X0 K F = Spec S_g[1/u0]`, the dense open of `Sym^g X` carrying the chunk `lawChunk K F`;
* `Jac K F : Over (Spec K)`, a group object (`grpObj_Jac`), smooth, separated, reduced, irreducible, lft;
* `jX0 : X0 ⟶ J`, the open immersion with dense range, compatible with the law (`jX0_mu`);
* `kptEquiv : J(K) ≃* H`, the `K`-points of `J` with the group law of `GrpObj` are the group `H` of
  birational maps generated by the left translations of the chunk.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Def

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The dense open `X0 = Spec S_g[1/u0]` of `Sym^g X` carrying Weil's group chunk. -/
noncomputable abbrev X0 : Scheme.{u} := Spec (.of (LawRing K F))

/-- **The Jacobian** of `F/K`: the group scheme of Weil's group chunk theorem for Weil's law. -/
noncomputable abbrev Jac : Over (Spec (.of K)) := (lawChunk K F).GO

noncomputable instance grpObj_Jac : GrpObj (Jac K F) := (lawChunk K F).grpObj

instance smooth_Jac : Smooth (Jac K F).hom := (lawChunk K F).smooth_sG

instance isSeparated_Jac : IsSeparated (Jac K F).hom := (lawChunk K F).isSeparated_sG

instance isReduced_Jac : IsReduced (Jac K F).left := inferInstanceAs (IsReduced (G (lawChunk K F).H))

instance irreducibleSpace_Jac : IrreducibleSpace (Jac K F).left :=
  inferInstanceAs (IrreducibleSpace (G (lawChunk K F).H))

instance locallyOfFiniteType_Jac : LocallyOfFiniteType (Jac K F).hom :=
  inferInstanceAs (LocallyOfFiniteType (G (lawChunk K F).H ↘ Spec (.of K)))

/-- The chart `X0 ⟶ J`. -/
noncomputable def jX0 : X0 K F ⟶ (Jac K F).left := JacChunk.ι (lawChunk K F).H 1

instance isOpenImmersion_jX0 : IsOpenImmersion (jX0 K F) :=
  inferInstanceAs (IsOpenImmersion (JacChunk.ι (lawChunk K F).H 1))

lemma jX0_over : jX0 K F ≫ (Jac K F).hom = X0 K F ↘ Spec (.of K) := JacChunk.ι_sG _ 1

/-- The `K`-points of `J` (with the group structure of `GrpObj`) are the group `H` of the chunk. -/
noncomputable def kptEquiv : (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≃* (lawChunk K F).H where
  toFun a := ⟨(lawChunk K F).kval a, (lawChunk K F).kval_mem a⟩
  invFun h := (lawChunk K F).kptH h
  left_inv a := (lawChunk K F).kpt_ext _ _ ((lawChunk K F).kval_kptH _)
  right_inv h := Subtype.ext ((lawChunk K F).kval_kptH h)
  map_mul' a b := Subtype.ext (by
    have e := (lawChunk K F).kval_mul (lift a b)
    rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd] at e
    exact e)

lemma kptEquiv_apply (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ((kptEquiv K F a : (lawChunk K F).H) : Bir K (X0 K F)) = (lawChunk K F).kval a := rfl

lemma kptEquiv_symm_apply (h : (lawChunk K F).H) : (kptEquiv K F).symm h = (lawChunk K F).kptH h := rfl

end Def

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Comm =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Comm` (L22, abstract half)

`isCommMonObj_of_comm`: for any strict group chunk `C` on a geometrically reduced, integral, separated, lft `k`-scheme
(`k` algebraically closed), if the group `H` of the chunk is commutative then the group scheme `G C.H` is commutative.
`isCommMonObj_Jac_of_comm`: the same for `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Abstract

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

variable (C : StrictChunk (X ↘ Spec (.of k)))

end Abstract

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- L22 reduced to the commutativity of the chunk group: `Jac K F` is commutative if `H` is. -/
theorem isCommMonObj_Jac_of_comm (hc : ∀ a b : (lawChunk K F).H, a * b = b * a) : IsCommMonObj (Jac K F) :=
  isCommMonObj_of_comm (lawChunk K F) hc

end Jac

end RamanujanPetersson.JacComplete


end

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

end Jac

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)

* `phi1 : Sym¹ B → B` (identity on points), `ptSet_phi1`, `liftTuple_phi1`;
* `rangeJ K F`: the image of `jacPic0` in `Pic`; `psiJ_mem_rangeJ`; `psiJ_of_pt` (points `y` of `S_g` with `y u0 ≠ 0`);
* **`jacPic0_surjective`**: for `g ≥ 1` the points `Q + c` (`c` = all but one point of a fixed point of `X0`) give
  `[Q] - [q0] ∈ rangeJ` for all `Q` off the zeros of `f = padMap phi1 c u0`, and `pic0_le_of_gen` finishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section One

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] [IsReduced B]
  [Algebra.FiniteType k B]

end One

section Surj

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical in
theorem psiJ_of_pt (y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K) (hy : y (lawPre K F).u0 ≠ 0) :
    ∃ a : X0 K F, IsClosed ({a} : Set (X0 K F)) ∧ (ptSet y).card = genusFK K F ∧
      psiJ K F a = clsK K F (Zdiv (ptSet y)) -
        clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1) := by
  have hu : IsUnit (y (lawPre K F).u0) := isUnit_iff_ne_zero.2 hy
  obtain ⟨yR, e⟩ : ∃ yR : LawRing K F →ₐ[K] K, yR.comp (awayι (K := K) (lawPre K F).u0) = y :=
    ⟨IsLocalization.Away.liftAlgHom (lawPre K F).u0 hu, by
      refine AlgHom.ext fun t => ?_
      rw [AlgHom.comp_apply, awayι_apply, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
      rfl⟩
  refine ⟨kpt yR, isClosed_kpt yR, ?_, ?_⟩
  · rw [← e]; exact card_lawPt K F yR
  · rw [psiJ, psiS_kpt, psiA, e, psiL]

end Surj

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJPiece =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`

In `F' = SynF K F c0` (coordinate `x' = 1/(x - c0)`), the `ν`-piece `pieceMap D c : Sym^g(B') → B'[1/f]` of
`AJLoc` is localized at `N(x')` (`ConvR`), converted to `F`-coordinates by `convSym` (`convS`), and localized at
the image of `u0` (`LocR`). This gives **`lawMapP : LawRing K F → LocR`**, i.e. `Spec LocR → X0`, on the open
`Spec LocR ⊆ Spec B'` (`pieceIn`), with the class formula **`psiJ_lawMapP`**: `ψ(piece(Q)) = κ - [Θ] - [Q]`.
`exists_pieceIn`: a point `Q` of `B'` lies on the piece when `f`, `N(x')` and `u0` do not vanish there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AwayPt

variable {K : Type u} [Field K] [IsAlgClosed K]

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- `u0` on the piece. -/
noncomputable def convU : ConvR c0 D c := convS c0 D c (lawPre K F).u0

end AJPiece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Ext =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)

Weil's extension theorem (S4-JacDivisors, Milne I.3.2) applied to the proper group `J` (L19, `isProper_Jac`):
* `domain_eq_top_Jac`: a rational map over `K` from a smooth `V` (with `V`, `V ×_K V` integral) to `J` is defined
  everywhere;
* `extJ f hf : V ⟶ J`, `ι_extJ` (it restricts to `f` on the domain of `f`), `eq_extJ` (unique);
* `UO V U`, `ιU V U` (a dense open `U ⊆ V` over `K`) and `eq_of_kpt_eq`: maps `V ⟶ J` from a reduced `V` locally of
  finite type are determined by their values at the `K`-points of a dense open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacLaw

universe u

section Ext

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
instance isSeparated_Jac_left : (Jac K F).left.IsSeparated :=
  ⟨by rw [← terminal.comp_from (Jac K F).hom]; infer_instance⟩

variable {V : Over (Spec (.of K))} [IsReduced V.left]

/-- The morphism `V ⟶ J` of a partial map whose rational map is defined everywhere. -/
noncomputable def extL (f : V.left.PartialMap (Jac K F).left) (h : f.toRationalMap.domain = ⊤) :
    V.left ⟶ (Jac K F).left :=
  V.left.topIso.inv ≫ V.left.homOfLE (show (⊤ : V.left.Opens) ≤ f.toRationalMap.toPartialMap.domain from h.ge) ≫
    f.toRationalMap.toPartialMap.hom

end Ext

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Sep =====
section

/-!
# Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)

* **`eq_one_of_stab`**: a `K`-point `c` of `J` with `W(K) · c ⊆ W` is `1` (Riemann's theorem `mem_W_iff` and the
  divisor form `mem_PrincK_of_stab`);
* `hsep_W`: translates of `W` separate `K`-points: for `b ≠ b'` some `a` has `b a ∈ W`, `b' a ∉ W`;
* `support_effI_Theta`: the support of the ideal sheaf `effI Θ` is `W`; `support_effI_Theta_ne_top`;
* **`hsep_Theta`**: the `hsep` hypothesis of `inum_pos` for `D = Θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors
open RamanujanPetersson.IntersectC

universe u

section Sep

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

instance isIntegral_Jac_left : IsIntegral (Jac K F).left := isIntegral_of_irreducibleSpace_of_isReduced _

end Sep

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_Cone_TwS3 =====
section

/-!
# S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data

* `twist_jt` (chart-generic): the local twist `χ (φ σ φ⁻¹) = q • χ σ` on `J = I(Q) ∩ ker π` for `φ • Q = Q`.
* `twist_loc_S3`: the same in the S3 chart for a Frobenius lift `φ` (`q = |𝔽_q|`), level data discharged.
* `tw_core`: for the normalised generators `τ` of `exists_norm_tau_fin`, `g⁻¹` a Frobenius lift with
  `P u = g⁻¹ • P s`: `χ (g⁻¹ τ_s g) = q • χ τ_u` (local twist if `u = s`, global normalisation otherwise).
* **`exists_resDat_tw`**: `exists_resDat` together with this twist clause.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Gen

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

end Gen

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

include hq he hP hI in
set_option maxHeartbeats 1600000 in
/-- **Twist of the normalised generators**: if `g⁻¹` is a Frobenius lift with `P u = g⁻¹ • P s`, then
`χ (g⁻¹ τ_s g) = q • χ τ_u` for every locally constant homomorphism `χ : J_u → M` (`N M = 0`). -/
theorem tw_core [Finite Gf] {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N) (hζNc : IsConst (p ^ e) ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • P s)
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    [Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)] {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hT : ∀ t, TauProp (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) N (τ t))
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (s u : S) (g : Pi1 (Places.Rfin Fq F) F)
    (hgF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹) (hu : P u = g⁻¹ • P s)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0)
    (χ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (hc : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) * g ∈
      Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) :
    χ ⟨_, hc⟩ = Fintype.card Fq • χ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
  by_cases hus : u = s
  · subst hus
    exact tw_same hq he π P hP I τ hNF g hgF hu hMo χ hχc hχ hc
  classical
  have hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN := by
    rw [hq]
    exact Kummer.zeta_fixed hζNc
  have hgF' : IsFrobLift (Places.Rfin Fq F) F (p ^ e) g⁻¹ := by
    rw [← hq]
    exact hgF
  have hx : g⁻¹ ζN = epow ζN ((p ^ e : ℕ) : ZMod N) := Kummer.frobLift_zeta hζN hζNc hgF'
  have hτ' : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ ∈ Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
    rw [inv_inv]
    exact hc
  have h1 := normAll_conj_tw hq he hζN hM hMU (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s))
    (ile_S3 hq he P hP I hI s (tau_base_I π _ I P τ hI s)) ((hπM _).1 (tau_base_ker π _ I P τ s)) hx hτ'
    (normAll_base π P I τ hζN hn s)
  rw [← hu] at h1
  have h2 := normAll_base π P I τ hζN hn u
  have hJΓu := jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP
    (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)
  obtain ⟨χ', hχ'c, hχ', hχ't⟩ := yconj_exist hq he π P hP I hI τ hNF hPic hζN hζNg hM hMU hπM hcov hdis hk₀ hn
    (Pi.single (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) 1 -
      Pi.single (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) 1)
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self])
  have hne : cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u ≠
      cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s := fun h => hus (congrArg Sigma.fst h)
  have hχu : χ' ⟨τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hJΓu (τ _).2⟩ = 1 := by
    rw [← yconj_chi hq he π P hP I hI τ hζN hζNg hM hMU hπM hk₀ hn χ' hχ'c hχ'
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hχ't]
    simp [Pi.single_apply, hne]
  have h3 := chi_eq_of_normTw hq he hζN hM hMU _ (fun σ hσ => hζNg σ (Subgroup.mem_inf.1 hσ).1)
    (memΓH_S3 hMU hπM) (hP u) _ hJΓu _ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))
    hk₀ hk₀ h1 h2 χ' hχ'c hχ'
  rw [hχu, mul_one] at h3
  obtain ⟨θ, -, -, hθ1, -, hgen⟩ := hT (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)
  have h4 : ∀ σ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)),
      χ' ⟨σ, hJΓu σ.2⟩ = χ' ⟨τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u), hJΓu (τ _).2⟩ * θ σ :=
    hgen (fun σ => χ' ⟨σ, hJΓu σ.2⟩) (hχ'c.comp_continuous (continuous_subtype_val.subtype_mk _))
      (fun a b => hχ' ⟨a, hJΓu a.2⟩ ⟨b, hJΓu b.2⟩)
  have h5 := h4 ⟨_, hτ'⟩
  rw [hχu, one_mul] at h5
  have hθc : θ ⟨_, hτ'⟩ = ((p ^ e : ℕ) : ZMod N) := h5.symm.trans h3
  have e1 : (⟨_, hτ'⟩ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) = ⟨_, hc⟩ := by
    apply Subtype.ext
    show g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ = g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) : Pi1 (Places.Rfin Fq F) F) * g
    rw [inv_inv]
  rw [← e1, eq_val_nsmul_of_gen hMo hθ1 (fun χ0 hc0 h0 => ⟨_, hgen χ0 hc0 h0⟩) χ hχc hχ ⟨_, hτ'⟩, hθc,
    ZMod.val_natCast, nsmul_mod_eq hMo, ← hq]

end Tau

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Arithmetic residue data with the Frobenius twist**: `exists_resDat` together with
`χ (g⁻¹ σ_s g) = q • χ σ_u` whenever `g⁻¹` is a Frobenius lift with `P u = g⁻¹ • P s`. -/
theorem exists_resDat_tw {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
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
    ∃ D : PerfectCx.ResDat π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I N
      (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I),
      ∀ (s u : S) (g : Pi1 (Places.Rfin Fq F) F), IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹ →
        P u = g⁻¹ • P s → ∀ (Mo : Type) [AddCommGroup Mo], (∀ m : Mo, N • m = 0) →
        ∀ χ : D.J u → Mo, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) →
        ∀ hc : g⁻¹ * D.σ s * g ∈ D.J u,
          χ ⟨_, hc⟩ = Fintype.card Fq • χ ⟨D.σ u, (D.hJ u _).2 ⟨D.hσ u, D.hσπ u⟩⟩ := by
  obtain ⟨ζN, hζN, hζNc⟩ := Kummer.exists_zeta (Places.Rfin Fq F) F p he N hNF
  have hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN := by
    rw [hq]
    exact Kummer.zeta_fixed hζNc
  obtain ⟨k₀, hk₀, τ, hT, hn, hs⟩ := exists_norm_tau_fin hq he hNF hζN hζNg hM hMU π hπM
    (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P) (cosQA_bdry π _ I P hP)
    (cosQA_cover π _ I P hπM hcov hI) (cosQA_disj_S3 hq he hMU π hπM P hP hdis I hI)
    (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP)
  refine ⟨{
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
    s0 := Classical.arbitrary S }, fun s u g hgF hu Mo _ hMo χ hχc hχ hc => ?_⟩
  exact tw_core hq he π P hP I hI τ hNF hPic hζN hζNc hM hMU hπM hcov hdis hk₀ hT hn s u g hgF hu hMo χ hχc hχ hc

end S3

end

end Residue
end RamanujanPetersson


end


