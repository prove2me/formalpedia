-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds
-- name    : FasterExactColoring_ThreeColor_Supplement_TerminalBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:58.73604+00:00
-- url     : https://prove2.me/theorems/9ee288fc-b6ae-424c-b08b-c697ad5894d2
-- title:
--   Operational terminal solvers and the exact exponential factors
-- statement:
--   The two modes are deterministic decision and one-sided Monte Carlo decision. Both use the published finite program and charged execution model. A graph solver handles every graph; a terminal solver handles every valid terminal instance with its supplied valid maximal star packings. The same execution supplies the Boolean output and its charged cost. Polynomial coefficients and exponents are fixed before all inputs.
--
--   The terminal factors are
--   $$3^{n_{K_3}}4^{n_{K_4}}\tau^{|S|+2n_{K_3}+3n_{K_4}},\quad
--    3^{s_{\star1}/4}\prod_{i=0}^3g_{3,i}^{a_i}\prod_{i=0}^4g_{4,i}^{b_i}\Lambda^{s'}e^{h(a_0)},\quad
--    24^{s_{\star1}/4}18^{n_{K_3}}24^{n_{K_4}}.$$
--   Here $\Lambda$ is the published exact root of $x^5-2x-2$, and
--   $$g_{m,0}=3m/2,\qquad g_{m,1}=\Lambda^{m-1}(3+\Lambda^3),\qquad
--    g_{m,i}=\frac6{(4-i)!}(4-i+i\Lambda^3)\quad(2\le i\le m).$$
--   For the path algorithm,
--   $$Q_0=1,\quad Q_i=\frac{6\,8^i}{(4-i)!}(4-i+27i/8),\quad
--    Q=24^{s_{\star1}/4}\prod_{i=0}^3Q_i^{a_i}\prod_{i=0}^4Q_i^{b_i},$$
--   $$Q\,3^{(10/3)b_0+2(a_0+b_1)+(a_1+b_2)+(a_2+b_3)/2+\epsilon n}.$$
--   These are numerical functions of computed data, with no assumed solver correctness. The subexponential term is represented explicitly by the triangle-cover envelope, not absorbed into a polynomial.
--
--   **Formalization Note** Only $m\in\{3,4\}$, $0\le i\le m$ are used. Formula defaults outside those indices have no theorem meaning. Monte Carlo execution rejects every no-instance, succeeds with probability at least $1/2$ on yes-instances, and has the stated worst-case bound on every coin tape. Terminal polynomial overhead is measured in the charged encoded input size, polynomially bounded in $n$ on valid packings.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemmas 5.2, 5.4–5.6, Eq. (7), pp. 11–14 (PDF pp. 13–16)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Execution
import Definitions.Def_FasterExactColoring_ThreeColor_CSP
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_StarPackings
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TriangleLists

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

inductive Mode where
  | det
  | rand

/-- Correctness and work refer to one execution, with the published coin-tape semantics. -/
noncomputable def decides (mode : Mode) (A : Program) (x : List ℕ) (B : ℝ)
    (P : Prop) : Prop :=
  match mode with
  | .det => deterministic A ∧ runWithin A x B (answers P)
  | .rand => monteCarlo A x B P

noncomputable def graphSolver (mode : Mode) (k : ℕ) (A : Program) (C : ℝ) (d : ℕ)
    (base : ℝ) : Prop :=
  ∀ (n : ℕ) (G : GraphInput n),
    decides mode A (graphCode G) (C * (n+1 : ℕ)^d * base^n) (colorable G k)

noncomputable def terminalSolver (mode : Mode) (A : Program) (C : ℝ) (d : ℕ)
    (factor : {n : ℕ} → Restricted n → StarPackings n → ℝ) : Prop :=
  ∀ (n : ℕ) (P : Restricted n) (K : StarPackings n),
    P.valid → P.terminal → K.valid P →
    let x := terminalCode P K
    decides mode A x (polynomial C d x * factor P K) P.colorable

noncomputable def threeColorFactor {n : ℕ} (P : Restricted n) (τ : ℝ) : ℝ :=
  (3 : ℝ)^(P.nClique 3) * (4 : ℝ)^(P.nClique 4) *
    τ^(P.S.card + 2*P.nClique 3 + 3*P.nClique 4)

/-- Lemma 5.4: in particular g(3,0)=9/2 and g(4,0)=6. -/
noncomputable def g (m i : ℕ) : ℝ :=
  if i = 0 then 3*(m : ℝ)/2
  else if i = 1 then cspBase^(m-1) * (3+cspBase^3)
  else 6/(Nat.factorial (4-i) : ℝ) * (4-(i : ℝ)+(i : ℝ)*cspBase^3)

noncomputable def cspTerminalFactor {n : ℕ} (P : Restricted n) (K : StarPackings n) : ℝ :=
  (3 : ℝ)^((K.firstVertices.card : ℝ)/4) *
    (∏ i : Fin 4, (g 3 i.val)^(cliqueCount P K 3 i.val)) *
    (∏ i : Fin 5, (g 4 i.val)^(cliqueCount P K 4 i.val)) *
    cspBase^((K.remainingS P).card) * Real.exp (coverEnvelope (cliqueCount P K 3 0))

noncomputable def treeTerminalFactor {n : ℕ} (P : Restricted n) (K : StarPackings n) : ℝ :=
  (24 : ℝ)^((K.firstVertices.card : ℝ)/4) *
    (18 : ℝ)^(P.nClique 3) * (24 : ℝ)^(P.nClique 4)

noncomputable def Qentry (i : ℕ) : ℝ :=
  if i = 0 then 1 else
    6*(8 : ℝ)^i/(Nat.factorial (4-i) : ℝ) * (4-(i : ℝ)+27*(i : ℝ)/8)

noncomputable def Qfactor {n : ℕ} (P : Restricted n) (K : StarPackings n) : ℝ :=
  (24 : ℝ)^((K.firstVertices.card : ℝ)/4) *
    (∏ i : Fin 4, (Qentry i.val)^(cliqueCount P K 3 i.val)) *
    (∏ i : Fin 5, (Qentry i.val)^(cliqueCount P K 4 i.val))

noncomputable def pathTerminalFactor {n : ℕ} (P : Restricted n) (K : StarPackings n)
    (ε : ℝ) : ℝ :=
  Qfactor P K * (3 : ℝ)^(
    (10/3 : ℝ)*cliqueCount P K 4 0 +
    2*((cliqueCount P K 3 0 : ℝ)+cliqueCount P K 4 1) +
    ((cliqueCount P K 3 1 : ℝ)+cliqueCount P K 4 2) +
    (1/2 : ℝ)*((cliqueCount P K 3 2 : ℝ)+cliqueCount P K 4 3) + ε*n)

end FasterExactColoring.ThreeColor.Supplement


