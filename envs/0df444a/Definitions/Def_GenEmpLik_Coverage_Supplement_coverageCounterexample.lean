-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_coverageCounterexample
-- name    : GenEmpLik_Coverage_Supplement_coverageCounterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:18:05.779787+00:00
-- url     : https://prove2.me/theorems/765c52ba-8595-4d23-9bc7-3dfa187140ac
-- title:
--   Three-atom functional exposing the missing hypothesis in Theorem 10
-- statement:
--   Let $P_0$ be uniform on $\{-1,0,1\}$ and let $H=\{z\mapsto z,z\mapsto z^2\}$. Represent a probability law by its moment pair $(a,b)=(E_Pz,E_Pz^2)$ and define
--   $$T(a,b)=\begin{cases}(b-2/3)^2,&a=0,\\a,&a\ne0.\end{cases}$$
--   The population point is $(0,2/3)$. The derivative there is $dT(u,v)=u$, its centered influence is $z$, and the divergence generator is $f(t)=(t-1)^2$. The zero fibre of $T$ fixes both moments and therefore fixes the entire three-atom probability law. This model supplies a counterexample to Theorem 10 as printed; it is not asserted to be a construction from the paper.
--
--   **Formalization Note** The atoms are coded by `Fin 3` with $z=j-1$, and the two class members by `Fin 2`. The bounded functional space is the same general uniform-norm space used above.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 23, Theorem 10; proof p. 37; finite-support continuity for Topt p. 12; counterexample model (not a source construction)

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_functionalDomain

open MeasureTheory
open Classical

namespace GenEmpLik.Coverage.Supplement

/-- Three-point population for the failure of Theorem 10 as printed, p. 23.
Fin 3 is coded by z=j-1, with equal probabilities on {-1,0,1}. -/
noncomputable def counterexampleLaw : Measure (Fin 3) :=
  (PMF.uniformOfFintype (Fin 3)).toMeasure

/-- The two-moment class H={z,z²}. It is bounded and finite, hence Donsker. -/
def counterexampleClass (i : Fin 2) (j : Fin 3) : ℝ :=
  if i = 0 then (j : ℝ) - 1 else ((j : ℝ) - 1) ^ 2

/-- A functional differentiable at (mean,second moment)=(0,2/3), but discontinuous
on the zero-mean line away from that point. Its zero fibre fixes both moments. -/
noncomputable def counterexampleFunctional (v : ProcessSpace (Fin 2)) : ℝ :=
  if v 0 = 0 then (v 1 - 2 / 3) ^ 2 else v 0

/-- The derivative is the continuous first-coordinate functional on all M. -/
def counterexampleDerivative (v : ProcessSpace (Fin 2)) : ℝ := v 0

/-- Quadratic divergence normalized by f''(1)=2. -/
def counterexampleGenerator (t : ℝ) : EReal := ((t - 1) ^ 2 : ℝ)

end GenEmpLik.Coverage.Supplement


