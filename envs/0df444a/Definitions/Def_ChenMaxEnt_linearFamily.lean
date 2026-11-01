-- Prove2me | Definitions.Def_ChenMaxEnt_linearFamily
-- name    : ChenMaxEnt_linearFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:14.499163+00:00
-- url     : https://prove2.me/theorems/1f7239da-b92e-4511-a869-0b17f8ad11bf
-- title:
--   The linear family $L(\alpha)$ of states with data $\alpha$
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be observables on $\mathcal H = \mathbb C^n$ and $\alpha \in \mathbb R^r$. The **linear family** of $\alpha$ is the set of all states that return the measurement results $\alpha$:
--
--   $$
--   L(\alpha) = \bigl\{\rho \in \mathcal D \;\big|\; \operatorname{tr}(\rho F_i) = \alpha_i,\ i = 1, \dots, r\bigr\},
--   $$
--
--   the preimage of $\alpha$ under the data map. It is nonempty exactly when $\alpha \in D_F$, and it is the feasible set of the maximum entropy problem.
--
--   **Formalization Note** States are `QAlgorithms.IsDensityMatrix`; the constraints are written as `expectations F ρ = α` (real parts of the traces).
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §2.1, p.4 (definition of L(α))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ChenMaxEnt_expectations

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, §2.1, p.4: "Given any measurement result α ∈ DF, we are
interested in the set of all states in D that can give α as the measurement results. We denote
such a set as L(α) = {ρ | tr(ρFi) = αi, i = 1, . . . , r}. It is the preimage of α under the
mapping in Eq. (1)." `linearFamily F α` is this linear family `L(α)`: the density matrices whose
data are `α`.

**Formalization Note.** States are `QAlgorithms.IsDensityMatrix` (positive semidefinite, trace
one); `tr(ρ F_i)` is taken through `expectations` (its real part). The set is defined for every
`α : ι → ℝ` and is empty exactly when `α ∉ D_F`. -/
def linearFamily {n ι : Type*} [Fintype n] (F : ι → Matrix n n ℂ) (α : ι → ℝ) :
    Set (Matrix n n ℂ) :=
  {ρ | QAlgorithms.IsDensityMatrix ρ ∧ expectations F ρ = α}

end ChenMaxEnt


