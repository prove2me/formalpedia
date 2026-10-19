-- Prove2me | Definitions.Def_MIPRE_Foundations_Dilation
-- name    : MIPRE_Foundations_Dilation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:37:17.157+00:00
-- url     : https://prove2.me/theorems/98263b98-8ed6-4e8a-8d1e-af2ce3433c2e
-- title:
--   The ancilla register of Naimark dilation against a fixed state
-- statement:
--   Let $d$ be a finite index type, the register $\mathbb C^d$, and $\mathcal A$ a finite outcome type. Blueprint `lem:naimark-dilation` states that a family of POVMs $\{E^x_a\}_{a \in \mathcal A}$ on $\mathbb C^d$, indexed by questions $x$, is the compression of a family of projective measurements $\{P^x_a\}$ on $\mathbb C^d \otimes \mathbb C^{\mathcal A}$ by one question-independent isometry $V : |v\rangle \mapsto |v\rangle \otimes |a_0\rangle$, with $V^\dagger P^x_a V = E^x_a$ for all $x, a$. This bundle holds the two matrices on the enlarged register $d \times \mathcal A$ in which the module `MIPRE.Foundations.Dilation` states that lemma.
--
--   `MIPRE.ancillaProj d a : Matrix (d × A) (d × A) ℂ`, for `a : A`, is the ancilla projection $\Pi_a = \mathbf 1_d \otimes |a\rangle\langle a|$. `MIPRE.ancillaEmbed d a₀ : Matrix (d × A) d ℂ`, for `a₀ : A`, is the isometry padding a vector with the fixed ancilla state $|a_0\rangle$. Entrywise, with $[\cdot]$ the indicator,
--
--   $$(\Pi_a)_{(j,b),(j',b')} = [(j,b) = (j',b')]\,[b = a], \qquad (V_{a_0})_{(j,b),\,j'} = [(j,b) = (j', a_0)].$$
--
--   The bundle embeds no lemmas. The module's theorems (that $\Pi_a$ is a self-adjoint idempotent with $\sum_a \Pi_a = \mathbf 1$ and $V_{a_0}^\dagger V_{a_0} = \mathbf 1$, the dilation of one POVM to an isometry, the unitary extension `exists_unitary_extending`, the dilation of a question-indexed family `exists_projective_dilation`, and three Born-rule transport lemmas) are not part of this bundle.
--
--   The module was extracted from `MIPRE/Background/Repetition/Entangled.lean`, where the dilation was written for blueprint `lem:povm-value-eq` (the entangled bridge); it reaches none of the vendored trees and lives in `MIPRE/Foundations/` so that `lem:ms-direct-anticomm`, which dilates the Magic Square's six constraint POVMs against one shared ancilla, can use it.
--
--   **Formalization Note** Both objects are concrete complex matrices indexed by the product type `d × A`, the outcome type `A` itself serving as the ancilla register; no abstract Hilbert space or tensor product appears. `ancillaProj d a` is `Matrix.diagonal fun p => if p.2 = a then 1 else 0`, diagonal by construction; `ancillaEmbed d a₀` is `Matrix.of fun p j => if p = (j, a₀) then 1 else 0`. In both, `d` is explicit and `A` implicit, and the definitions need only `[DecidableEq d] [DecidableEq A]`; `[Fintype d] [Fintype A]` enter only in the module's theorems. The bundle imports no other definition bundle, only Mathlib.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Dilation.lean; blueprint lem:naimark-dilation

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Naimark dilation against a fixed state

A POVM is the compression of a projective measurement on a larger space. What the applications
need is more than that: a whole *question-indexed family* of POVMs must be the compression of a
family of projective measurements by **one** question-independent isometry, because the state
the expectations are taken against is shared and must not depend on the question.
`exists_projective_dilation` is that statement, and the unitary extension
(`exists_unitary_extending`) is the step that buys it.

This file was extracted from `MIPRE/Background/Repetition/Entangled.lean`, where it was written
for the dilation direction of `lem:povm-value-eq`. It is generic mathematics --- matrices, an
ancilla register, and the completion of an orthonormal family to a basis --- and it reaches
none of the vendored trees, but `Entangled.lean` imports the 71k-line vendored
`Repetition/TenProofs/QuantumParallelRepetition`, and `MIPRE/LCS/` may not import
`MIPRE/Background/` at all. The second consumer is blueprint `lem:ms-direct-anticomm`, whose
proof dilates each of the Magic Square's six constraint POVMs against one shared ancilla, so
the code has to live outside `MIPRE/Background/` to be usable at all.

The Born-rule transport lemmas at the end travel with it: they are how a dilated projective
measurement is compressed back, and they say nothing about repetition either.
-/

namespace MIPRE

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

/-! ## Naimark dilation of a question-indexed family

The second input to the dilation direction. A POVM dilates to an isometry into one extra
register (`exists_isometry_of_povm`); extending that isometry to a unitary turns it into a
*projective* measurement on the larger space whose expectations against a **fixed** state are
the POVM's. The extension is what makes the construction work for a whole question-indexed
family at once: the isometry depends on the question, the state must not. -/

/-- The ancilla projection `1 ⊗ |a⟩⟨a|` on `d × A`: the identity on the first factor and the
rank-one projection onto `a` on the second. It is a diagonal matrix, and saying so is what
makes the dilation computations below elementary. -/
def ancillaProj (d : Type*) [DecidableEq d] {A : Type*} [DecidableEq A] (a : A) :
    Matrix (d × A) (d × A) ℂ :=
  Matrix.diagonal fun p => if p.2 = a then 1 else 0

/-- The isometry `d → d × A` that pads a vector with the fixed ancilla state `|a₀⟩`. -/
def ancillaEmbed (d : Type*) [DecidableEq d] {A : Type*} [DecidableEq A] (a₀ : A) :
    Matrix (d × A) d ℂ :=
  Matrix.of fun p j => if p = (j, a₀) then 1 else 0

/-! ## Transport of Born-rule expectations

Three ways a quadratic form `⟨v| M |v⟩` moves: along a bijective reindexing of the space,
along an arbitrary linear map (which is how a dilation is compressed back), and the
special case `M = 1` that transports unit vectors. -/

end MIPRE


