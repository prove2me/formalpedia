-- Prove2me | Definitions.Def_MIPRE_Foundations_Pasting
-- name    : MIPRE_Foundations_Pasting
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:55.847528+00:00
-- url     : https://prove2.me/theorems/a642ce01-e196-4402-a8c7-21ae77801e02
-- title:
--   Definitions of Pasting: Pasting two measurements into one The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   **Definitions** (3): `MIPRE.collisionTerm` (**The collision term**: the pairs of `G`-outcomes that the outcome map cannot tell apart.); `MIPRE.fibSum` (The fibre sum of a family of operators along an outcome map --- its coarse-graining.); `MIPRE.pasteJ` (**The pasted POVM**: the paper's `J_{[eval = (a_1, a_2)]}`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Pasting` (`MIPRE/Foundations/Pasting.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean; blueprint lem:pasting-updated

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le

/-!
# Pasting two measurements into one

The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's
`lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds
two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with
`A`'s two marginals. The conclusion is that `A` agrees with the **sandwich**
`J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes.

Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are
proved first.

* **A sub-measurement close to a projective measurement carries almost all the mass**
  (`qform_sum_ge_of_close`, NW19's Fact 4.31). Two Cauchy--Schwarz steps against the same
  deviation, and the loss is `2 sqrt(delta)`.
* **Multiplying by the projector of the same outcome costs nothing** (`sum_snorm_sq_cool`, the
  paper's `lem:cool-closeness-fact` in its partition form). The cross terms vanish by mutual
  orthogonality and each diagonal term loses only `A_a <= Id`. The partition form is what matters:
  the consumers apply it to the `q` fibres of an outcome map at once, and the single-subset form
  would cost a factor `q` there.

The sandwich is where a **collision probability** enters. `G_2^{g_2} G_1 G_2^{g_2}` summed over a
fibre of `g_2 |-> g_2(y)` is a *pinching* of `G_1` by that fibre, not a conjugation by the fibre's
projector, and the difference is the cross terms `g_2 \ne g_2'` with `g_2(y) = g_2'(y)`. Those are
rare exactly when the outcome map separates the family, which for line polynomials is
Schwartz--Zippel.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker

set_option linter.unusedSectionVars false

/-! ## Two small facts about the quadratic form -/

section QF

variable {N : Type*} [Fintype N] [DecidableEq N]

end QF

section Mass

variable {N : Type*} [Fintype N] [DecidableEq N] {C : Type*} [Fintype C] [DecidableEq C]

/-! ## A sub-measurement close to a projective measurement -/

end Mass

/-! ## The coarse-graining of a family, and the product question distribution -/

section Setup

/-- The fibre sum of a family of operators along an outcome map --- its coarse-graining. -/
def fibSum {α β N : Type*} [Fintype α] [DecidableEq β] (G : α → Matrix N N ℂ) (e : α → β)
    (b : β) : Matrix N N ℂ :=
  ∑ g ∈ univ.filter fun g => e g = b, G g

variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Setup

/-! ## Regrouping along the fibres of an outcome map -/

section Fibre

/-! ### Weighted sums -/

section Weighted

variable {ι : Type*} [Fintype ι]

end Weighted

end Fibre

/-! ## Two ways for a family of squared state norms to sum to at most one -/

section Mass2

variable {N : Type*} [Fintype N] [DecidableEq N]

end Mass2

section Nonneg

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

end Nonneg

/-! ## Coarse-graining a pair of projective families, on the two parties -/

section Coarse2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Coarse2

/-! ## The fine-grained commutator against the coarse-grained one -/

section Fine

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y G2 R1 R2 : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype G2] [DecidableEq G2] [Fintype R1] [DecidableEq R1]
  [Fintype R2] [DecidableEq R2]

end Fine

/-! ## The sandwich family of the pasting lemma -/

section Sand2

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

/-- **The pasted POVM**: the paper's `J_{[eval = (a_1, a_2)]}`. `R` is already the coarse-graining
of the paper's `G_1` along its own outcome map --- only `R`'s projectivity is used, so it enters
as a single projective family, and the inner coarse-graining is the consumer's business. -/
def pasteJ (R : R1 → Matrix dB dB ℂ) (G : K → Matrix dB dB ℂ) (e : K → R2)
    (p : R1 × R2) : Matrix dB dB ℂ :=
  ∑ g ∈ univ.filter fun g => e g = p.2, G g * R p.1 * G g

variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}

/-! ## Alice's operator against Bob's projection -/

/-! ## The ordered product carries almost all the mass -/

/-! ## The pasted POVM -/

/-! ## The coarse-grained commutator, and the collision term -/

/-- **The collision term**: the pairs of `G`-outcomes that the outcome map cannot tell apart. It
is exactly what the coarse-grained cloud has beyond the fine-grained one, and the only place where
the separating property of the outcome map is needed. -/
def collisionTerm (ψ : dA × dB → ℂ) (R : R1 → Matrix dB dB ℂ) (G : K → Matrix dB dB ℂ)
    (Ga : K → Matrix dA dA ℂ) (e : K → R2) : ℝ :=
  ∑ a : R1, ∑ g : K, ∑ g' ∈ univ.filter fun g' => g' ≠ g ∧ e g' = e g,
    bornProb ψ (Ga g') (R a * G g * R a)

/-! ## The two halves of the pasting lemma, at one question -/

end Sand2

/-! ## The marginal of a joint measurement against the other party's product

The step `lem:qld-pairs-of-lines` needs before the pasting lemma applies: a *joint* measurement
consistent with the ordered product of the other party's two families is consistent, after summing
out one outcome, with that party's single family. Two facts do it: `sum_snorm_sq_cool`, to replace
the marginal by the same marginal with the other party's projection attached, and then the
orthogonality of that projection's fibres, which is what makes the sum over the summed-out outcome
free rather than a factor `|R2|`. -/

section Marginal

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]

end Marginal

/-! ## Transport to a twice-extended state

The consumer's two inputs live on different spaces: the joint measurement on each party's space
enlarged by one register (the Naimark dilation of `lem:qld-combined-points`), the line measurements
on the unenlarged ones. An operator with an inert ancilla has the same cross-party deviation on the
extended state as the operator itself. -/

section Transport

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

end Transport

/-! ## The pasting lemma

The averaged statement. `A` is Alice's joint projective measurement, `R` Bob's first family --- in
the application already the coarse-graining of his answer measurement along its own outcome map ---
and `G` his second, with `Ga` Alice's copy of it. The four hypotheses are the two marginal
consistencies, the cross-party self-consistency of `G` at the *fine* level, and the collision term.

Two hypotheses of the paper's statement are absent, and both are absences rather than gaps.
`G_1` is assumed projective (in the paper it may be a POVM for `i = 1`), which makes the two
diagonal sums of the commutator expansion exactly one and removes the need for NW19's Fact 4.31.
And the cross-party self-consistency of `G` is a hypothesis here rather than derived from the
backwards consistency and Alice's self-consistency, because the consumer has it directly, at the
fine level and with no collision cost. -/

section Average

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]

end Average

/-! ## The collision term under a product question distribution -/

section Collision

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

end Collision

end MIPRE

end


