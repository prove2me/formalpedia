-- Prove2me | Definitions.Def_D1Bound5_FinitePResidualIdentity_Definitions
-- name    : D1Bound5_FinitePResidualIdentity_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:31.604774+00:00
-- url     : https://prove2.me/theorems/aee44c18-a2f9-402f-ba79-15ef57f3d0a6
-- title:
--   Finite PResidual Identity
-- statement:
--   The exact first nonzero inverse-power coefficient of R and T. The named objects in this bundle include `finitePPairCoeff`, `finitePPairResidual`, `finitePPairTail`, `finitePLeadingR`, `finitePLeadingT`, `finitePResidual`, `finitePLeadingV`, `finitePLeading` and 1 further declarations.
-- source:
--   D1Bound5/FinitePResidualIdentity.lean, lines 64-67, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 69-72, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 74-77, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 79-81, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 83-84, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 125-128, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 130-134, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 136-138, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052; D1Bound5/FinitePResidualIdentity.lean, lines 140-143, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three





def finitePPairCoeff {R : Type*} [CommRing R]
    (u v : R) (kind side : Fin 2) : Fin 3 → R :=
  ![![finitePRLeftCoeff u v, finitePRRightCoeff u v],
    ![finitePTLeftCoeff u v, finitePTRightCoeff u v]] kind side

noncomputable def finitePPairResidual (u v c : ℂ) (kind : Fin 2) : ℂ :=
  ![finitePRConstant u v c,finitePTConstant u v c] kind +
    u*finitePairQuadratic (finitePPairCoeff u v kind 0) c*((1+1/(u*c))^(1/2 : ℂ)) +
    v*finitePairQuadratic (finitePPairCoeff u v kind 1) c*((1+1/(v*c))^(1/2 : ℂ))

noncomputable def finitePPairTail (u v c : ℂ) (kind : Fin 2) : ℂ :=
  ∑ side : Fin 2, ∑ l : Fin 3,
    ![u,v] side*finitePPairCoeff u v kind side l*c^(l : ℕ)*
      finiteQHalfRemainder (6+(l : ℕ)) (1/(![u,v] side*c))

/-- The exact first nonzero inverse-power coefficient of R and T. -/
noncomputable def finitePLeadingR (u v : ℂ) : ℂ :=
  5/(128*u^2)-5/(128*v^2)+5*u/(256*v^3)-5*v/(256*u^3)

noncomputable def finitePLeadingT (u v : ℂ) : ℂ :=
  -75/(128*u)+5*v/(16*u^2)-15*v^2/(256*u^3)-35*u/(256*v^2)+15/(32*v)









noncomputable def finitePResidual (a b s c : ℂ) (i : Fin 4) : ℂ :=
  finitePDividedMatrix a b s c i 0+
    ∑ j : Fin 3, ![a,b,s] j*finitePDividedMatrix a b s c i j.succ*
      ((1+1/(![a,b,s] j*c))^(1/2 : ℂ))

/-- The V leading coefficient is combined before taking absolute values;
its two 15/(32s) terms cancel exactly. -/
noncomputable def finitePLeadingV (a b s : ℂ) : ℂ :=
  -75/(128*a)+5*s/(16*a^2)-15*s^2/(256*a^3)-35*a/(256*s^2)+
    75/(128*b)-5*s/(16*b^2)+15*s^2/(256*b^3)+35*b/(256*s^2)

noncomputable def finitePLeading (a b s : ℂ) : Fin 4 → ℂ :=
  ![finitePLeadingR a b, finitePLeadingR a b+finitePLeadingR b s-finitePLeadingR a s,
    finitePLeadingT a b, finitePLeadingV a b s]

noncomputable def finitePTail (a b s c : ℂ) : Fin 4 → ℂ :=
  ![finitePPairTail a b c 0,
    finitePPairTail a b c 0+finitePPairTail b s c 0-finitePPairTail a s c 0,
    finitePPairTail a b c 1, finitePPairTail a s c 1-finitePPairTail b s c 1]





end D1Bound5
end


