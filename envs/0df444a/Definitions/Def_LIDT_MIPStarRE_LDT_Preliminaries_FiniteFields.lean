-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_FiniteFields
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_FiniteFields
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:57.681495+00:00
-- url     : https://prove2.me/theorems/156aa6c8-aae6-4c74-9d6b-10df8ca5e3f9
-- title:
--   LIDT definitions: LDT / Preliminaries / FiniteFields
-- statement:
--   This bundle defines additive characters and Fourier phases for the finite field and its vector space. The trace to the prime field supplies the scalar phase, while the field dot product supplies the vector phase used in hypercube and polynomial orthogonality calculations.
--
--   Principal definitions:
--   - `ffTrace`: the field trace from the finite field to its prime subfield.
--   - `ffChar`: the complex additive character $x\mapsto\omega^{\operatorname{tr}(x)}$.
--   - `ffChar_apply`: the explicit evaluation formula for the scalar character.
--   - `ffDotProduct`: the coordinatewise dot product on $\mathbb{F}_q^m$.
--   - `ffVecChar`: the vector character $u\mapsto\omega^{\operatorname{tr}(\langle u,v\rangle)}$.
--   - `ffVecChar_apply`: the explicit formula for evaluating the vector character.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/FiniteFields.lean#L39-L166

-- Generated from MIPStarRE/LDT/Preliminaries/FiniteFields.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace LIDT

/-!
# Finite fields and Fourier orthogonality

This file formalizes the finite-field trace and the two Fourier orthogonality facts
from `references/ldt-paper/preliminaries.tex` (lines 15–83).

## Main results

* `fourier_fact_scalar` (`prop:fourier-fact-scalar`):
  `𝔼_{x ∈ 𝔽_q} ω^{tr[x·a]} = 1 if a = 0, 0 otherwise`
* `fourier_fact_vector` (`prop:fourier-fact-vector`):
  Vector version over `𝔽_q^m`.

## References

* `references/ldt-paper/preliminaries.tex`, lines 15–83
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

section Trace

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]

/-- Paper label `def:finite-field-trace`.

The finite-field trace `F → F_p`, implemented as Mathlib's algebraic trace
`Algebra.trace (ZMod p) F`. -/
noncomputable abbrev ffTrace : F → ZMod p :=
  Algebra.trace (ZMod p) F



section Honest

variable (params : Parameters) (spec : PrimePowerFieldSpec params)





end Honest
end Trace

section Fourier

-- The Fourier section uses `[Fintype F]` (rather than `[Finite F]` as in the Trace section)
-- because `AddChar.expect_eq_ite` requires a `Fintype` instance. Downstream users with
-- only `[Finite F]` can obtain `Fintype` via `Fintype.ofFinite`.
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

/-- The canonical complex additive character `x ↦ ω^{tr[x]}` on `F`. -/
noncomputable abbrev ffChar : AddChar F ℂ :=
  (ZMod.stdAddChar (N := p)).compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom

omit [Fintype F] [DecidableEq F] in
@[simp] theorem ffChar_apply (x : F) :
    ffChar (p := p) (F := F) x =
      ZMod.stdAddChar (N := p) (ffTrace (p := p) (F := F) x) :=
  rfl







section Vector

variable {m : ℕ}

-- We define `ffDotProduct` directly rather than reusing `Matrix.dotProduct` to avoid
-- pulling in the full `Mathlib.Data.Matrix.Basic` import. The definitions are identical.
/-- The standard dot product on `F^m`. -/
def ffDotProduct (u v : Fin m → F) : F :=
  ∑ i, u i * v i

/-- The additive character `u ↦ ω^{tr[⟨u, v⟩]}` on `F^m`. -/
noncomputable def ffVecChar (v : Fin m → F) : AddChar (Fin m → F) ℂ :=
  (ffChar (p := p) (F := F)).compAddMonoidHom
    { toFun := fun u => ffDotProduct u v
      map_zero' := by simp [ffDotProduct]
      map_add' := by
        intro u w
        simp [ffDotProduct, add_mul, Finset.sum_add_distrib] }

omit [Fintype F] [DecidableEq F] in
@[simp] theorem ffVecChar_apply (u v : Fin m → F) :
    ffVecChar (p := p) (F := F) v u =
      ffChar (p := p) (F := F) (ffDotProduct u v) :=
  rfl





end Vector
end Fourier

end MIPStarRE.LDT.Preliminaries

end

end LIDT


