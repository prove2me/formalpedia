-- Prove2me | Definitions.Def_RPLib_S4_CDPack41t
-- name    : RPLib_S4_CDPack41t
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T13:41:49.633492+00:00
-- url     : https://prove2.me/theorems/f2731882-07c6-4bc7-83a9-43be3b1ca10c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41t of 71
-- statement:
--   Part 41t of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJPieceA3`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA3: `kapP`, `clsK_single_syn`, `pieceN_ne_zero`, `exists_pieceIn`]
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41

/-!
# Curve-duality library package, part 41t of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJPieceA3`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA3: `kapP`, `clsK_single_syn`, `pieceN_ne_zero`, `exists_pieceIn`]
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJPieceA3 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0` [pack-only part AJPieceA3: `kapP`, `clsK_single_syn`, `pieceN_ne_zero`, `exists_pieceIn`]

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

/-- The constant of the piece: `[Hn] - [c]` moved to `F`. -/
noncomputable def kapP : PicK K F :=
  (picMap (synEquiv K F c0)).symm
    (clsK K (SynF K F c0) D.Hn - clsK K (SynF K F c0) (Zdiv (Finset.univ.image c)))

omit [IsAlgClosed K] in
theorem clsK_single_syn (P' : Place K (SynF K F c0)) :
    (picMap (synEquiv K F c0)).symm (clsK K (SynF K F c0) (Finsupp.single P' 1)) =
      clsK K F (Finsupp.single ((synPlace c0).symm P') 1) := by
  rw [AddEquiv.symm_apply_eq, picMap_clsK, divMap_single]
  show clsK K (SynF K F c0) (Finsupp.single P' 1) =
    clsK K (SynF K F c0) (Finsupp.single (synPlace c0 ((synPlace c0).symm P')) 1)
  rw [Equiv.apply_symm_apply]

/-- `N(x')` does not vanish where `ν(Q + c)` avoids `x = ∞`. -/
theorem pieceN_ne_zero (z : PieceR D c →ₐ[K] K)
    (h : ∀ e ∈ ptSet (z.comp (pieceMap D c)), e (xS K F c0) ≠ 0) : z (pieceN c0 D c) ≠ 0 := by
  have e := symPt_normS (liftTuple (z.comp (pieceMap D c))) (xS K F c0)
  rw [symPt_liftTuple, AlgHom.comp_apply] at e
  rw [pieceN, e]
  exact Finset.prod_ne_zero_iff.2 fun l _ => h _ ((mem_ptSet _ _).2 ⟨l, rfl⟩)

/-- **A point of `B'` lies on the piece** when `f`, `N(x')` and `u0` do not vanish there. -/
theorem exists_pieceIn (Q : Rfin K (SynF K F c0) →ₐ[K] K) (hf : Q (pieceF D c) ≠ 0)
    (hN : ∀ z : PieceR D c →ₐ[K] K, z.comp (pieceι D c) = Q →
      ∀ e ∈ ptSet (z.comp (pieceMap D c)), e (xS K F c0) ≠ 0)
    (hu : ∀ y : ConvR c0 D c →ₐ[K] K, (y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) = Q →
      y (convU c0 D c) ≠ 0) :
    ∃ x : LocR c0 D c →ₐ[K] K, x.comp (pieceIn c0 D c) = Q := by
  obtain ⟨z, hz⟩ : ∃ z : PieceR D c →ₐ[K] K, z.comp (pieceι D c) = Q := exists_away_pt Q (pieceF D c) hf
  obtain ⟨y, hy⟩ := exists_away_pt z (pieceN c0 D c) (pieceN_ne_zero c0 D c z (hN z hz))
  have hyQ : (y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) = Q := by rw [hy, hz]
  obtain ⟨x, hx⟩ := exists_away_pt y (convU c0 D c) (hu y hyQ)
  refine ⟨x, ?_⟩
  have e : x.comp (pieceIn c0 D c) =
      ((x.comp (awayι (K := K) (convU c0 D c))).comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) := rfl
  rw [e, hx, hyQ]

end AJPiece

end RamanujanPetersson.JacComplete

end


