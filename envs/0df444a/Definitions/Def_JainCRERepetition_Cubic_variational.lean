-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_variational
-- name    : JainCRERepetition_Cubic_variational
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:40.246817+00:00
-- url     : https://prove2.me/theorems/a37a3667-e994-41d4-9a58-8c62b8bf967d
-- title:
--   Fact 2.27 — Hermitian exponentials and variational functionals
-- statement:
--   Hermitian functional calculus uses the published spectral decomposition, with natural operator logarithms and complex scalar multiples in the exponent. The two variational functionals are extended-real suprema over all positive definite test matrices $W$:
--
--   $$\sup_{W>0}\{\operatorname{Tr}\alpha\ln W-\ln\operatorname{Tr}e^{\ln\zeta+\ln W}\},\qquad\sup_{W>0}\{\operatorname{Tr}\alpha\ln W-\ln\operatorname{Tr}\zeta W\}.$$
--
--   They are the natural-log quantum and measured relative entropies in Fact 2.27. No positive definiteness is imposed on the singular normalized comparison in the measured-divergence extension. These definitions supply the exact four-matrix estimate and real probability integral used by constructive marginal replacement.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 21, Fact 2.27; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_quantum

open scoped ComplexOrder MatrixOrder BigOperators
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic

def hermitianExp {I : Type} [Fintype I] [DecidableEq I] (H : Op I) (z : ℂ) : Op I :=
  WildeQIT.Recover.spectralFun (fun x => Complex.exp (z * (x : ℂ))) H

def naturalLogOp {I : Type} [Fintype I] [DecidableEq I] (H : Op I) : Op I :=
  WildeQIT.Recover.spectralFun (fun x => (Real.log x : ℂ)) H

def variationalD {I : Type} [Fintype I] [DecidableEq I] (α ζ : Op I) : EReal :=
  sSup {v : EReal | ∃ W : Op I, W.PosDef ∧ v =
    ((α * naturalLogOp W).trace.re -
      Real.log ((hermitianExp (naturalLogOp ζ + naturalLogOp W) 1).trace.re) : ℝ)}

def variationalMeasuredD {I : Type} [Fintype I] [DecidableEq I] (α ζ : Op I) : EReal :=
  sSup {v : EReal | ∃ W : Op I, W.PosDef ∧ v =
    ((α * naturalLogOp W).trace.re - Real.log ((ζ * W).trace.re) : ℝ)}

end JainCRERepetition.Cubic


