-- Prove2me | Definitions.Def_RPLib_F2_030
-- name    : RPLib_F2_030
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:54:35.20779+00:00
-- url     : https://prove2.me/theorems/c02b1c53-afe5-48a6-b44b-33ccfecde7d5
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 030 of 70
-- statement:
--   File 030 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
--   * `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
--   * `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
--   * `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_028
import Definitions.Def_RPLib_F2_076

/-!
# Ramanujan-Petersson curve library (flat edition), file 030 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstL2`: S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`
* `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
* `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
* `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstL2 =====
section

/-!
# S4-JacLaw, file O10e (part L, law_l_m, law_m_l): the point relations of `Law`/`Assoc` on `T0[1/u3][1/u2]`

`law_r_m law_m_r law_l_m law_m_l law_assoc`: `r_mOut`, `m_rOut`, `l_mOut`, `m_lOut`, `assoc_mOut` at `T := T0 K F`,
`iL`, `iR`, for abstract points `y` (instantiating them at `x ∘ nestK` directly is slow).
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

section Law

/-! The point relations of `Law`/`Assoc` for abstract points `y` of the nested localizations (instantiating them
at `x ∘ nestK` directly is slow; through these lemmas it is a plain application). -/

variable (y y₁ y₂ y₃ y₄ : Localization.Away L.mU →ₐ[K] K) (yr : Localization.Away L.rU →ₐ[K] K)
  (yl : Localization.Away L.lU →ₐ[K] K)

set_option maxHeartbeats 400000 in
theorem law_m_l (ha : (L.mB y).comp (iL K F) = yl.comp L.lOutL)
    (hb : (L.mB y).comp (iR K F) = (L.lB yl).comp (iR K F)) : y.comp L.mOutL = (L.lB yl).comp (iL K F) :=
  m_lOut (T := T0 K F) (T' := T0 K F) (D3 := L.Dl3) (D3' := L.Dm3) (D2 := L.Dl2) (D2' := L.Dm2) (c0 := L.c0)
    (c1 := L.c1) (ψb := iR K F) (ψc := iL K F) (φa := iL K F) (φb := iR K F) L.hl3.symm L.hl2.symm yl y ha hb

end Law

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_InstA =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`

`b_LL b_LR b_RR b_Lmu b_Rmu` (base identities through the nest) and `rel_assoc`.
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

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

variable {x xr xl} in
theorem b_LL {x' : Localization.Away L.ωm →ₐ[K] K} (h : pL x = pL x') :
    (L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F) = (L.mB (x'.comp (nestK (K := K) L.mU))).comp (iL K F) :=
  (L.mB_L x).trans (h.trans (L.mB_L x').symm)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacComplete_AJLoc =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point

* `exists_secE`: through a closed point `φ0` and any finite `E` avoiding the roots of some `b ≠ 0` (in `x`),
  a section `s` with exact poles, only simple zeros, and zero set `Z ⊇ E ∪ {φ0}` of any size.
* `exists_nuE`: `ν`-data `D` with `ν(Z \ E) = E` (`exists_role`), `Z \ E = {φ0} ∪ c`.
* `pieceF D c` (`good` at `Q + c`), `PieceR D c = B[1/pieceF]`, **`pieceMap D c : Sym^g B → B[1/pieceF]`**
  (points `Q ↦ ν(Q + c)`, `ptSet_pieceMap`); `clsK_nuF`: `[ν(A)] = [Hn] - [A]`.
* **`exists_piece`**: the package for a closed point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJLoc

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {r : ℕ} (D : NuData K F (1 + r)) (c : Fin r → (Rfin K F →ₐ[K] K))

/-- **Value of the piece**: `[ν(Q + c)] = [Hn] - [Q] - [c]`. -/
theorem clsK_pieceMap (x : PieceR D c →ₐ[K] K) :
    clsK K F (Zdiv (ptSet (x.comp (pieceMap D c)))) = clsK K F D.Hn -
      clsK K F (Finsupp.single (Sum.inl (ptP (x.comp (pieceι D c)))) 1) - clsK K F (Zdiv (Finset.univ.image c)) := by
  have hy := good_padPt D c x
  have hcard := NuData.card_ptSet hy
  rw [ptSet_padPt1] at hcard
  have hQc : x.comp (pieceι D c) ∉ Finset.univ.image c := by
    intro hmem
    rw [Finset.insert_eq_of_mem hmem] at hcard
    have := Finset.card_image_le (s := Finset.univ) (f := c)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [ptSet_pieceMap, clsK_nuF hy, ptSet_padPt1, Zdiv_insert hQc, clsK_add]
  abel

end AJLoc

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

/-- `N(x')` on the piece. -/
noncomputable def pieceN : PieceR D c := pieceMap D c (normS K (xS K F c0))

end AJPiece

end RamanujanPetersson.JacComplete


end


