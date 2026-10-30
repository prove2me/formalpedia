-- Prove2me | Definitions.Def_KhachiyanRounding_BCD_Specification
-- name    : KhachiyanRounding_BCD_Specification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:44:25.583914+00:00
-- url     : https://prove2.me/theorems/c8a235ba-287b-4862-b975-27209bf8f47b
-- title:
--   Endpoint assertions, centered rounding and analytic budgets
-- statement:
--   The endpoint assertion says that the computed weights belong to $S_F$, their moment is positive definite, the cached inverse and scores equal the mathematical inverse and leverage scores, and the requested relaxed optimality inequalities hold. It is an output property, never an execution precondition.
--
--   For center $b$, shape $Q$ and factor $t$, the rounding assertion means
--   $$H_{b,1/t}(E(b,Q))\subseteq\operatorname{conv}(\mathcal A)\subseteq E(b,Q),\qquad H_{b,s}(x)=b+s(x-b).$$
--   Here $E(b,Q)$ is the published inverse-shape ellipsoid. Covariance is $D-bb^\mathsf T$, with $b=\sum_jp_ja_j$ and $D=\sum_jp_ja_ja_j^\mathsf T$. The analytic expressions are
--   $$B(n,m,\varepsilon)=mn^2(\varepsilon^{-1}+\ln n+\ln\ln m),$$
--   $$B_{\mathrm{lift}}(n,m,\varepsilon)=2m(n+1)^2\left(\frac{n+1}{n\varepsilon}+\ln(n+1)+\ln\ln(2m)\right).$$
--   They are used only in theorem conclusions; the execution counter is independent of them. Theorems provide positivity and the domains on which the logarithms and inverse have the intended meanings.
-- source:
--   Leonid G. Khachiyan (1996), Rounding of Polytopes in the Real Number Model of Computation, Mathematics of Operations Research 21(2), 307–320, https://doi.org/10.1287/moor.21.2.307, (1.2)–(1.3), printed p.307 / PDF p.2; (2.5), (2.7), (2.10), printed pp.309–310 / PDF pp.4–5; (3.2)–(3.7), printed pp.315–316 / PDF pp.10–11.

import Definitions.Def_KhachiyanRounding_BCD_Program

namespace KhachiyanRounding.BCD

open scoped Pointwise

/-- Mathematical output assertion, never an input or execution constructor.
The inverse here is the mathematical inverse, not a computation primitive. -/
def EndpointCorrect {ι : Type} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (s : Registers ι d) (δ : ℝ) : Prop :=
  s.weights ∈ KhachiyanRound.BCD.SF v ∧
  (KhachiyanRound.BCD.momentMatrix v s.weights).PosDef ∧
  s.inverse = (KhachiyanRound.BCD.momentMatrix v s.weights)⁻¹ ∧
  s.scores = (fun j => KhachiyanRound.BCD.w v s.weights j) ∧
  KhachiyanRound.BCD.IsRelaxedOpt v s.weights δ

/-- The source's two inclusions, with contraction about the returned center. -/
def Rounds {ι : Type} {n : ℕ} (a : ι → Fin n → ℝ)
    (b : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  (AffineMap.homothety b t⁻¹) '' LinearOptimization.ellipsoid b Q ⊆
      convexHull ℝ (Set.range a) ∧
  convexHull ℝ (Set.range a) ⊆ LinearOptimization.ellipsoid b Q

/-- Mathematical covariance; the program computes this by scalar loops. -/
noncomputable def covariance {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  KhachiyanRound.BCD.momentMatrix a p -
    Matrix.vecMulVec (∑ j, p j • a j) (∑ j, p j • a j)

/-- Source operation-order expression, used for analysis only. -/
noncomputable def printedBudget (n m : ℕ) (ε : ℝ) : ℝ :=
  (m : ℝ) * (n : ℝ) ^ 2 * (1 / ε + Real.log n + Real.log (Real.log m))

/-- Positive global version of N(ε′) in lifted parameters (3.2)–(3.3).
No executable cost is defined using this expression. -/
noncomputable def liftedBudget (n m : ℕ) (ε : ℝ) : ℝ :=
  (2 * m : ℕ) * (n + 1 : ℕ) ^ (2 : ℕ) *
    (((n + 1 : ℕ) : ℝ) / ((n : ℝ) * ε) +
      Real.log (n + 1 : ℕ) + Real.log (Real.log (2 * m : ℕ)))

end KhachiyanRounding.BCD


