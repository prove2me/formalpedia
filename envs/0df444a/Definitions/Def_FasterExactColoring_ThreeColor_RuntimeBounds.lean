-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds
-- name    : FasterExactColoring_ThreeColor_RuntimeBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:09:40.321674+00:00
-- url     : https://prove2.me/theorems/058a7283-b027-4bd6-ad3f-194349bb6924
-- title:
--   Exact exponential factors for the three residual algorithms
-- statement:
--   For computed structural counts $a=(p,q,r,s,t,d,c,m)$, set $B_I=3^p2^q$ and $B_R=3^m2^{r-2m}$. The three factors are
--   $$F_{\rm CSP}=B_I\Lambda^{s+t}(3\Lambda^{-4})^{(d+t)/10+19c/660},$$
--   $$F_{\rm path}(\kappa)=B_IB_R\kappa^{c/6+\varepsilon n},\qquad
--   F_{\rm joint}=B_I3^m3^{(d+t+2r-4m)/6+\varepsilon n}.$$
--   All subtractions in real exponents occur after conversion of the counts to real numbers. Hence no negative intermediate quantity is silently truncated.
--
--   The deterministic and randomized residual-solver predicates quantify over all valid graph/forest/root/matching data. Each uses an actual finite program execution, a uniform polynomial envelope, and the indicated factor. The predicates are specifications to be proved by existentially producing programs; they supply neither correctness nor a time bound as a structure field or as a hypothesis of the goal.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Eqs. (3)–(5) and Lemmas 4.7–4.9, pp. 7–9 (PDF pp. 9–11)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Execution
import Definitions.Def_FasterExactColoring_ThreeColor_CSP
import Definitions.Def_FasterExactColoring_ThreeColor_BushyForest

namespace FasterExactColoring.ThreeColor

noncomputable def internalFactor (a : Counts) : ℝ := (3:ℝ)^a.p * (2:ℝ)^a.q
noncomputable def leafFactor (a : Counts) : ℝ :=
  (3:ℝ)^a.m * (2:ℝ)^((a.r:ℝ)-2*a.m)
noncomputable def cspFactor (a : Counts) : ℝ :=
  internalFactor a * cspBase^(a.s+a.t) *
    (3*cspBase^(-4:ℤ))^(((a.d:ℝ)+a.t)/10 + (19/660:ℝ)*a.c)
noncomputable def pathFactor (a : Counts) (n : ℕ) (ε : ℝ) (κ : ℝ) : ℝ :=
  internalFactor a * leafFactor a * κ^((a.c:ℝ)/6+ε*n)
noncomputable def jointFactor (a : Counts) (n : ℕ) (ε : ℝ) : ℝ :=
  internalFactor a * (3:ℝ)^a.m *
    (3:ℝ)^(((a.d:ℝ)+a.t+2*a.r-4*a.m)/6+ε*n)

/-- One deterministic program, with constants before all graphs and decompositions. -/
def solvesPreprocessed (A : Program) (C : ℝ) (d : ℕ)
    (factor : Counts → ℕ → ℝ) : Prop :=
  deterministic A ∧ ∀ (n : ℕ) (G : GraphInput n) (F : ForestData n)
    (roots : Finset (Fin n)) (M : Matching n),
    preprocessed G F roots M →
    let x := preprocessingCode G F roots M
    runWithin A x (polynomial C d x * factor (counts G F roots M) n)
      (answers (colorable G 3))

noncomputable def randomSolvesPreprocessed (A : Program) (C : ℝ) (d : ℕ)
    (factor : Counts → ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (G : GraphInput n) (F : ForestData n)
    (roots : Finset (Fin n)) (M : Matching n),
    preprocessed G F roots M →
    let x := preprocessingCode G F roots M
    monteCarlo A x (polynomial C d x * factor (counts G F roots M) n)
      (colorable G 3)

end FasterExactColoring.ThreeColor


