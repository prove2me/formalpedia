-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula
-- name    : ProcurementPoA_DeterministicCap_CapFormula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:14.460772+00:00
-- url     : https://prove2.me/theorems/c02e67bd-9bfd-4a4c-8ae6-052c1a42d455
-- title:
--   Sharp loss, optimal deterministic cap and comparison function
-- statement:
--   Write $e=\exp(1)$ and $\varepsilon=\exp(-2)=e^{-2}$. The source's cap and the exact comparison value are computed from the real parameter $R$:
--
--   $$T^\star(R)=\frac{\sqrt{(e^2-1)^2+4e^2R}-(e^2-1)}2,\qquad A(R)=\frac{1-\varepsilon+\sqrt{(1-\varepsilon)^2+4\varepsilon R}}2.$$
--
--   For Lemma 5.2 define
--
--   $$g_{R,T}(c)=\begin{cases}c+\varepsilon(T-c),&c<T,\\R,&c\ge T.\end{cases}$$
--
--   These are algebraic functions only. In particular $A(R)$ is not a definition of price of anarchy: its equality to the independently defined worst-case equilibrium ratio is part of the goal. The strict branch $c<T$ matches the lemma, while the actual auction accepts a bid equal to $T$.
--
--   **Formalization Note** The code uses $\exp(2)$ for $e^2$. The displayed real functions are total, but their theorem uses specify $R\ge1$ and the lemma specifies $T\ge1$.
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, normalization, printed p. 8 (PDF p. 10); Lemma 5.2 and Theorem 5.3, printed p. 9 (PDF p. 11); Appendix A.1.2, printed p. 17 (PDF p. 19)

import Mathlib

namespace ProcurementPoA.DeterministicCap

open scoped Classical

/-- The exact sharp value-auction loss, e^{-2}. -/
noncomputable def epsilon : ℝ := Real.exp (-2)

/-- The cap prescribed in Theorem 5.3, computed only from R. -/
noncomputable def capStar (R : ℝ) : ℝ :=
  (Real.sqrt ((Real.exp 2 - 1) ^ 2 + 4 * Real.exp 2 * R) - (Real.exp 2 - 1)) / 2

/-- The exact optimal ratio computed in Appendix A.1.2, not the definition of PoA. -/
noncomputable def capBound (R : ℝ) : ℝ :=
  (1 - epsilon + Real.sqrt ((1 - epsilon) ^ 2 + 4 * epsilon * R)) / 2

/-- Lemma 5.2's comparison function; the branch is strictly c < T. -/
noncomputable def gCap (R T c : ℝ) : ℝ :=
  if c < T then c + epsilon * (T - c) else R

end ProcurementPoA.DeterministicCap


