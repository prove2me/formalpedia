-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
-- name    : MIPRE_Foundations_LowDegree_SelfDualize
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:13.100359+00:00
-- url     : https://prove2.me/theorems/80adbc15-14af-42db-89d1-e4c32b7052dc
-- title:
--   Definitions of SelfDualize: Self-dualization in characteristic two The step that turns a normal basis into a *self-dual* normal basis (blueprint…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.SelfDualize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Self-dualization in characteristic two. The step that turns a normal basis into a *self-dual* normal basis (blueprint `lem:self-dual-basis`, ledger nodes `1.1.6.1.7` and `1.1.6.1.8`). Written in the group algebra, where the whole step is two short lemmas. If `α` is a normal element of `K / F` with Galois group `G`, the Gram matrix of its orbit is circulant, i.e. it is the element `c ∈ F[G]` with `c g = tr(α · g α)`; it is a unit, and it is fixed by the involution `τ` induced by `g ↦ g⁻¹`. Replacing `α` by `a • α` replaces `c` by `a · τ a · c`, so a self-dual normal basis is exactly a solution…
--
--   **Definitions** (1): `MIPRE.LowDegree.binarySquareRoot` (Square root in a binary group algebra: the coefficient at `g` is read from `g + g`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeff_binarySquareRoot`, `two_eq_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.SelfDualize` (`MIPRE/Foundations/LowDegree/SelfDualize.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/SelfDualize.lean; blueprint lem:group-algebra-selfdualization

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Self-dualization in characteristic two

The step that turns a normal basis into a *self-dual* normal basis (blueprint
`lem:self-dual-basis`, ledger nodes `1.1.6.1.7` and `1.1.6.1.8`).

Written in the group algebra, where the whole step is two short lemmas. If `α` is a normal
element of `K / F` with Galois group `G`, the Gram matrix of its orbit is circulant, i.e. it is
the element `c ∈ F[G]` with `c g = tr(α · g α)`; it is a unit, and it is fixed by the involution
`τ` induced by `g ↦ g⁻¹`. Replacing `α` by `a • α` replaces `c` by `a · τ a · c`, so a self-dual
normal basis is exactly a solution `a` of `a · τ a = c⁻¹`.

* `exists_mul_involute_eq` — that equation is solvable in any commutative ring on which
  squaring is bijective: take the square root of the right-hand side, which is unique and
  therefore fixed by `τ` because the right-hand side is.
* `sq_bijective` — and squaring *is* bijective on `F[G]` when `F` is a finite field of
  characteristic two and `G` is a finite abelian group of odd order, because squaring is then
  the composite of the Frobenius of `F` on coefficients with the doubling bijection of `G` on
  indices.

Between them they replace the circulant Gram manipulation the campaign's two nodes carry.
Nothing here is about fields yet: `MIPRE/Foundations/LowDegree/SelfDual.lean` has the
definitions `IsSelfDualBasis` and `IsNormalBasis`, and assembling these lemmas into a basis is
the remaining work of issue #105.
-/

namespace MIPRE.LowDegree

open Finset

/-! ## The equation `a · τ a = u` -/

/-! ## Squaring on a group algebra of odd order in characteristic two -/

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]

omit [Fintype G] [Fintype F] [DecidableEq G] in
theorem two_eq_zero (hF : CharP F 2) : (2 : AddMonoidAlgebra F G) = 0 := by
  have : ((2 : ℕ) : F) = 0 := by
    have := hF
    exact CharP.cast_eq_zero F 2
  rw [show (2 : AddMonoidAlgebra F G) = AddMonoidAlgebra.single 0 (2 : F) from rfl,
    show (2 : F) = ((2 : ℕ) : F) from by norm_num, this, AddMonoidAlgebra.single_zero]

/-! ## An explicit square root over the binary field -/

/-- Square root in a binary group algebra: the coefficient at `g` is read from `g + g`.
For an odd-order group this is a permutation of the coefficient vector. In particular,
this step needs neither factorization nor exponentiation in the group of units. -/
noncomputable def binarySquareRoot (z : AddMonoidAlgebra (ZMod 2) G) : AddMonoidAlgebra (ZMod 2) G :=
  .ofCoeff (Finsupp.onFinset univ (fun g => z.coeff (g + g)) (fun g _ => mem_univ g))

omit [DecidableEq G] in
@[simp] theorem coeff_binarySquareRoot (z : AddMonoidAlgebra (ZMod 2) G) (g : G) :
    (binarySquareRoot z).coeff g = z.coeff (g + g) := by
  simp [binarySquareRoot]

end MIPRE.LowDegree


