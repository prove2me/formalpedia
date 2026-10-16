-- Prove2me | Definitions.Def_MIPRE_Foundations_GameDouble
-- name    : MIPRE_Foundations_GameDouble
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:27:40.03339+00:00
-- url     : https://prove2.me/theorems/b81adac4-4ee6-493a-bcec-03d926bf8b36
-- title:
--   The doubled question set: a synchronous game from any two-player game
-- statement:
--   This bundle holds the module that turns an arbitrary game on a common question set into a synchronous game without changing its value. Let $G$ be a game (`Game X X A A`) with question distribution $\mu$ on $X \times X$ and decision predicate $D$. The doubled game `Game.doubled G` is a `SynchronousGame` on the questions $\mathrm{Bool} \times X$ and the answers $A$: Alice's questions carry the tag `false`, Bob's the tag `true`, and every other pair of tagged questions, the diagonal included, carries no weight and is rejected. Writing $\mathbf{1}[\cdot]$ for the indicator of the tag condition,
--
--   $$\mu_{\mathrm{dbl}}\big((s, x), (t, y)\big) = \mathbf{1}[s = \mathrm{false} \wedge t = \mathrm{true}] \cdot \mu(x, y), \qquad D_{\mathrm{dbl}}\big((s,x),(t,y),a,b\big) = \mathbf{1}[s = \mathrm{false} \wedge t = \mathrm{true}] \wedge D(x,y,a,b),$$
--
--   so the decision is `false` off the tag block. The synchronicity field holds for every $G$, since equal questions have equal tags and so fail the tag test. The two other definitions transport tensor-product strategies across the doubling: `TensorProductStrategy.undouble` reads a strategy for the doubled game on the original one by keeping Alice's measurements at $(\mathrm{false}, \cdot)$ and Bob's at $(\mathrm{true}, \cdot)$ (a relabelling along $x \mapsto (\mathrm{false}, x)$, $y \mapsto (\mathrm{true}, y)$ with the identity on answers), and `TensorProductStrategy.double` reads a strategy for $G$ on the doubled game by having both players ignore the tag (a relabelling along the projections). The two embedded lemmas, `doubled_μ` and `doubled_D`, restate the two fields above as rewriting equations. The doubling is how the game of a verifier is read as a synchronous game with no hypothesis on its decider (`MIPRE.Verifier.doubledGame`), on which the definition of perfect PCC strategies of a verifier rests.
--
--   **Formalization Note** `Game.doubled` is a `def` producing a `SynchronousGame (Bool × X) A` with fields `μ p q := if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0`, the nonnegativity and normalization proofs, `D p q a b := if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false`, and `synchronous`. `undouble` and `double` are instances of `TensorProductStrategy.relabel` between `G` and `G.doubled.toGame` with `Equiv.refl A` on both answer sets; the value-preservation and PCC statements (`quantumValue_doubled`, `value_double`, `isPCC_double`) are theorem items outside this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameDouble.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameDouble.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-!
# The doubled question set

A game description denotes a *synchronous* game by construction: `GameData.game` rejects
unequal answers at equal questions whatever its acceptance table holds, while a verifier's
game does no such thing. So a description can match `𝒱_n` only where `𝒱_n` happens to be
synchronous (`MIPRE.Verifier.isSynchronousAt_of_game_matches`), and membership in the class
`B` of the halting reduction does not ask for synchronicity — which is exactly the seam
blueprint `lem:halting-semidecider` records, the semidecider needing the tabulation's value
to equal `val*` at every bounded string.

`Game.doubled` closes it, and does so without weakening anything. The doubled game plays on
`Bool × X`: Alice is asked a question tagged `false`, Bob one tagged `true`, and every other
pair — the diagonal included — carries no weight and is rejected outright. Two consequences,
and both are what make this cheap:

* it is a `SynchronousGame` for *any* game, its `synchronous` field holding for free, since
  `p = q` forces equal tags and so fails the tag test. The description's veto is no longer a
  constraint on the verifier; it is implied by the distribution.
* because the decision predicate also rejects off the tag block, a description matching the
  doubled game matches it *totally*, on every question pair including the diagonal. So
  `quantumValue_eq_of_equiv` and `SyncStrategy.isPCC_relabel` apply unchanged, and no
  support-restricted version of either is needed.

The value is untouched in both senses that the halting reduction uses:

* `quantumValue_doubled`, by a two-sided `iSup` argument on `TensorProductStrategy.double`
  and `undouble` — a strategy for the doubled game restricts to Alice's `(false, ·)` and
  Bob's `(true, ·)` measurements, and one for the original ignores the tag;
* `SyncStrategy.double` with `value_double` and `isPCC_double`, which is the direction
  completeness needs. The doubling adds no commutation obligation: `IsPCC` is quantified
  over the support of `μ`, and the doubled support maps into the original one.

`Game.sum_doubled` is the one computation, strategy-agnostic so that it serves both values.
-/

namespace MIPRE

open Matrix Kronecker
open scoped ComplexOrder

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

namespace Game

/-- **The doubled game.** Alice's questions carry the tag `false` and Bob's the tag `true`;
every other pair carries no weight and is rejected. Synchronous for free. -/
def doubled (G : Game X X A A) : SynchronousGame (Bool × X) A where
  μ p q := if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0
  μ_nonneg p q := by split_ifs; exacts [G.μ_nonneg _ _, le_rfl]
  μ_sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [G.μ_sum_one]
  D p q a b := if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false
  synchronous p a b _ := by
    rcases p with ⟨t, x⟩
    cases t <;> simp

@[simp] theorem doubled_μ (G : Game X X A A) (p q : Bool × X) :
    G.doubled.μ p q = if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0 := rfl

@[simp] theorem doubled_D (G : Game X X A A) (p q : Bool × X) (a b : A) :
    G.doubled.D p q a b = if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false := rfl

end Game

/-! ## Tensor-product strategies through the doubling -/

namespace TensorProductStrategy

/-- A strategy for the doubled game, read on the original: Alice keeps her measurements at
`(false, ·)`, Bob his at `(true, ·)`. -/
def undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    TensorProductStrategy G :=
  S.relabel G (fun x => (false, x)) (fun y => (true, y)) (Equiv.refl A) (Equiv.refl A)

/-- A strategy for the original game, read on the doubled one: both players ignore the tag. -/
def double {G : Game X X A A} (S : TensorProductStrategy G) :
    TensorProductStrategy G.doubled.toGame :=
  S.relabel G.doubled.toGame (fun p => p.2) (fun q => q.2) (Equiv.refl A) (Equiv.refl A)

end TensorProductStrategy

/-! ## Synchronous strategies through the doubling -/

namespace SyncStrategy

variable {G : SynchronousGame X A}

end SyncStrategy

end MIPRE


