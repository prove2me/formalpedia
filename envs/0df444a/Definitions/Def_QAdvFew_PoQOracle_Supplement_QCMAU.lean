-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_QCMAU
-- name    : QAdvFew_PoQOracle_Supplement_QCMAU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:14:39.10021+00:00
-- url     : https://prove2.me/theorems/4c7073a2-583c-4626-bb6d-5a4c38f4e652
-- title:
--   $\mathsf{QCMA}^{U,C}$ for a unitary oracle
-- statement:
--   A language $L$ is in $\mathsf{QCMA}^{U,C}$ if there are a QPT oracle verifier $\mathrm{Ver}$ and a polynomial witness length $p$ such that for every $x$:
--
--   1. if $x\in L$, some classical $w\in\{0,1\}^{p(|x|)}$ has $\Pr[\mathrm{Ver}^{U,C}(x,w)\to1]\ge\frac23$;
--   2. if $x\notin L$, every $w\in\{0,1\}^{p(|x|)}$ has $\Pr[\mathrm{Ver}^{U,C}(x,w)\to1]\le\frac13$.
--
--   The promise version requires these conditions only on yes- and no-instances (Definition 3.7 and the promise convention on p. 13).
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.7 and the promise-problem convention, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UQFamily

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- The class `QCMA^{U,C}` of languages (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Definition 3.7, p. 13 (PDF p. 15): "`L ∈ QCMA^U` if
there are a QPT oracle verifier `Ver^U` and a polynomial `p` such that … if `x ∈ L`, there is a
classical witness `w ∈ {0,1}^{p(|x|)}` such that `Pr[Ver^U(x, w) → 1] ≥ 2/3`; if `x ∉ L`, then
for every `w ∈ {0,1}^{p(|x|)}`, `Pr[Ver^U(x, w) → 1] ≤ 1/3`").

**Formalization Note** The verifier is a uniform, polynomially bounded `UQVer`; its witness length
`wit n` is computed by the uniform generator and bounded by a polynomial. -/
def QCMAU {ar : ℕ → ℕ → ℕ} (U : UOracle ar) (C : Oracle) : Set (Set Str) :=
  {L | ∃ V : UQVer ar, V.Uniform ∧ V.PolyBounded ∧ ∀ x : Str,
    (x ∈ L → ∃ w, (2 : ℝ) / 3 ≤ V.accept U C x w) ∧
    (x ∉ L → ∀ w, V.accept U C x w ≤ (1 : ℝ) / 3)}

/-- The promise version of `QCMA^{U,C}` (p. 13, PDF p. 15). -/
def PromiseQCMAU {ar : ℕ → ℕ → ℕ} (U : UOracle ar) (C : Oracle) : Set PromiseProblem :=
  {Pp | ∃ V : UQVer ar, V.Uniform ∧ V.PolyBounded ∧ ∀ x : Str,
    (x ∈ Pp.yes → ∃ w, (2 : ℝ) / 3 ≤ V.accept U C x w) ∧
    (x ∈ Pp.no → ∀ w, V.accept U C x w ≤ (1 : ℝ) / 3)}

end QAdvFew.PoQOracle.Supplement


