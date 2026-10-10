-- Prove2me | Definitions.Def_ChapterA1h
-- name    : ChapterA1h
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T06:53:25.88654+00:00
-- url     : https://prove2.me/theorems/902aa1f1-96d2-432b-bee2-76f0b67ba883
-- title:
--   Chapter A1h
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA1h.lean`): generated def bundle for ChapterA1h. See BookProof/ChapterA1h.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA1h.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA1d
import Definitions.Def_Complexification
import Mathlib


/-!
# Chapter A, §A.1 — the real-system trichotomy (work-package N1 residue)

This file discharges the remaining N1 residue of `FORMALIZATION_ROADMAP.md`
(§A.1, **Prop 11**, the type assignment of an irreducible **real** system).

The complex side of Prop 11 is `realification_classification` in
`BookProof/ChapterA1g.lean`.  Here we treat the **real** side, classifying a real
system `(M, W)` by the structure of its endomorphism division algebra — the
standard **real / complex / quaternionic** trichotomy of Frobenius — phrased via
the **R-imaginary** operators of Def 8.2:

* **R-real type** — no R-imaginary operator commutes with `M` (endomorphism
  algebra `ℝ`);
* **R-complex type** — a commuting R-imaginary exists, but no *quaternionic*
  (anticommuting) pair does (endomorphism algebra `ℂ`);
* **R-pseudoreal type** — a quaternionic pair of commuting R-imaginaries exists
  (endomorphism algebra `ℍ`).

We prove the trichotomy is **exhaustive** (`rType_exhaustive`) and **mutually
exclusive**, and connect it to the Def-10 complexification framework: a commuting
R-imaginary makes the complexification `(M, Cx W)` **reducible**
(`cxSystem_reducible_of_commuting_rImaginary`).  Hence an **R-real** system —
one whose complexification is irreducible (`IsRReal`) — is of R-real type
(`IsRReal.not_hasCommutingRImaginary`).

The reducibility argument is the concrete eigenspace splitting behind Def 10:
the complexified R-imaginary `Jc := cxMap J` is `ℂ`-linear with `(Jc)² = -1`, so
its `+i` eigenspace `ker (Jc - i)` is a proper, non-trivial subsystem of
`(M, Cx W)` (its `-i` eigenspace being the complementary conjugate summand
`V ⊕ V̄`).

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace BookProof.ChapterA

open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-! ## R-imaginary structures and the R-type predicates -/

/-- A real system **has a commuting R-imaginary** iff some R-imaginary operator
(Def 8.2: an isometry `J` with `J² = -1`) commutes with every `m ∈ M`. -/
def HasCommutingRImaginary (M : System ℝ W) : Prop :=
  ∃ J : W ≃ₗᵢ[ℝ] W, IsRImaginary M J

/-- A real system **has a quaternionic pair** iff it admits two commuting
R-imaginary operators `J, K` that **anticommute** (`J K = - K J`).  Together with
`J K` this realizes the quaternion units `i, j, k` in the endomorphism algebra. -/
def HasQuaternionicRImaginary (M : System ℝ W) : Prop :=
  ∃ J K : W ≃ₗᵢ[ℝ] W, IsRImaginary M J ∧ IsRImaginary M K ∧
    (∀ x, J (K x) = - K (J x))



/-- **R-real type.** A real system with no commuting R-imaginary operator
(endomorphism algebra `ℝ`). -/
def IsRRealType (M : System ℝ W) : Prop :=
  ¬ HasCommutingRImaginary M

/-- **R-complex type.** A commuting R-imaginary exists, but no quaternionic pair
(endomorphism algebra `ℂ`). -/
def IsRComplexType (M : System ℝ W) : Prop :=
  HasCommutingRImaginary M ∧ ¬ HasQuaternionicRImaginary M

/-- **R-pseudoreal type.** A quaternionic pair of commuting R-imaginaries exists
(endomorphism algebra `ℍ`). -/
def IsRPseudorealType (M : System ℝ W) : Prop :=
  HasQuaternionicRImaginary M









/-! ## The complexified R-imaginary and its eigenspace splitting -/

/-- The **complexification of an R-imaginary** operator, as a `ℂ`-linear bounded
operator on `Cx W`. -/
noncomputable def rImagCx (J : W ≃ₗᵢ[ℝ] W) : Cx W →L[ℂ] Cx W :=
  Cx.cxMap (J.toContinuousLinearEquiv.toContinuousLinearMap)

omit [CompleteSpace W] in
@[simp] lemma rImagCx_apply (J : W ≃ₗᵢ[ℝ] W) (x : Cx W) :
    rImagCx J x = ⟨J x.re, J x.im⟩ := rfl

















end BookProof.ChapterA


