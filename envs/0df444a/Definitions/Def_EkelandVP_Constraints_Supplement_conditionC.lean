-- Prove2me | Definitions.Def_EkelandVP_Constraints_Supplement_conditionC
-- name    : EkelandVP_Constraints_Supplement_conditionC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:23:04.119584+00:00
-- url     : https://prove2.me/theorems/f6df1175-01aa-4f41-82ce-b0f2e6e41bb5
-- title:
--   The literal subset/closure Palais–Smale condition (C)
-- statement:
--   Let $M$ be a topological space, $F:M\to\mathbb R$ a function, and $\sigma:M\to\mathbb R$ its differential norm in a geometric application. The paper's **condition (C)** says that for every subset $S\subseteq M$,
--   $$
--   \bigl(\exists B\in\mathbb R\;\forall x\in S,\ |F(x)|\le B\bigr)
--   \ \land\
--   \neg\bigl(\exists\delta>0\;\forall x\in S,\ \delta\le\sigma(x)\bigr)
--   \quad\Longrightarrow\quad
--   \exists p\in\overline S,\ \sigma(p)=0.
--   $$
--   Zero differential norm means a critical point. The formula deliberately retains the subset and closure quantifiers; it does not assert sequential compactness or a cluster point of every minimizing sequence. The empty set does not meet the second antecedent.
--
--   The file also defines $a_n=1/(n+1)$ for the disclosed disconnected counterexample to the printed existence theorem. This sequence is a counterexample construction, not a function introduced by the paper.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 340, condition (C), with the counterexample to the titled theorem (PDF 17); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
set_option autoImplicit false

namespace EkelandVP.Constraints.Supplement

/-- The literal subset/closure condition (C), p.340. `slope` is the norm of dF
(equivalently, of grad F in the strong Riemannian metric); zero slope means critical.
This general topological definition is independent of a particular manifold presentation. -/
def ConditionC {M : Type*} [TopologicalSpace M] (F slope : M → ℝ) : Prop :=
  ∀ S : Set M, (∃ B : ℝ, ∀ x ∈ S, |F x| ≤ B) →
    (¬ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ ≤ slope x) →
      ∃ p ∈ closure S, slope p = 0

/-- Component values in the zero-dimensional counterexample to the printed existence theorem. -/
noncomputable def componentValue (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

end EkelandVP.Constraints.Supplement


