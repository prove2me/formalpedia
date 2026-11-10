-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_Potential
-- name    : EzeunalaJiangKS_Signing_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:01:43.375639+00:00
-- url     : https://prove2.me/theorems/d10e59e9-691a-4557-b9e0-b6d08aec75a9
-- title:
--   Coupled inverse optimization and its chosen minimizer
-- statement:
--   Over real $t$ and positive definite complex Hermitian $X,Y$, take the infimum of
--   $$t+\varepsilon\operatorname{Tr}(X+Y)$$
--   subject to $X^{-1}+S(x)+\eta_x(Y)\preceq tI$ and $Y^{-1}-S(x)+\eta_x(X)\preceq tI$. This defines $R(x)$ independently of any optimizer; $\Psi(x)=R(x)+\lambda\Phi(x)$. A minimizer is a feasible triple whose objective is no larger than that of every feasible triple. The chosen optimizer is such a triple if one exists and the zero triple otherwise.
--
--   The infimum is a real infimum, so empty or unbounded-below objective sets have Mathlib's junk value zero. On valid analytic data the source's feasible scalar matrices and spectral lower bound exclude both cases; existence and uniqueness remain theorem conclusions. The constraints are inequalities in this definition. Matrix inversion on singular off-domain arguments returns the standard total inverse; valid feasible matrices are positive definite.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §3.1, (5)–(6), printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Weights

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

abbrev Primal (d : ℕ) := ℝ × CMat d × CMat d

def feasible {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (z : Primal d) : Prop :=
  z.2.1.PosDef ∧ z.2.2.PosDef ∧
    loewner (z.2.1⁻¹ + shift A x₀ x + eta A x z.2.2) (z.1 • (1 : CMat d)) ∧
    loewner (z.2.2⁻¹ - shift A x₀ x + eta A x z.2.1) (z.1 • (1 : CMat d))

def objective {N d : ℕ} (A : Fin N → CMat d) (z : Primal d) : ℝ :=
  z.1 + epsilon A * tr (z.2.1 + z.2.2)

/-- Real infimum with explicit junk value 0 if the feasible objectives are empty or unbounded below.
Lemma 3.1 asserts nonemptiness and a lower bound on every valid instance. -/
def matrixPotential {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) : ℝ :=
  sInf {r : ℝ | ∃ z : Primal d, feasible A x₀ x z ∧ objective A z = r}

def isOptimizer {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) (z : Primal d) : Prop :=
  feasible A x₀ x z ∧ ∀ w : Primal d, feasible A x₀ x w → objective A z ≤ objective A w

/-- Choice is a specification, not an oracle available to the bit machine. -/
def optimizer {N d : ℕ} (A : Fin N → CMat d) (x₀ x : State N) : Primal d :=
  if h : ∃ z, isOptimizer A x₀ x z then Classical.choose h else (0, 0, 0)

def potential {N d : ℕ} (A : Fin N → CMat d) (x₀ : State N) (l : ℝ) (x : State N) : ℝ :=
  matrixPotential A x₀ x + l * fractionality x

end EzeunalaJiangKS.Signing


