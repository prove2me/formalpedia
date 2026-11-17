-- Prove2me | Definitions.Def_GevreyGibbsSep_Supplement_wsFinalState
-- name    : GevreyGibbsSep_Supplement_wsFinalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:59:47.300494+00:00
-- url     : https://prove2.me/theorems/328f8f5c-4d4b-45f7-b5e9-76049092c194
-- title:
--   Final state $U_T O^{\pm}\cdots U_1 O^{\pm} U_0\,\mathrm{load}|\phi\rangle$ of a warm-started algorithm
-- statement:
--   For a warm-started first-order quantum algorithm $A$ with $T$ oracle calls, a potential $E:\mathbb R^d\to\mathbb R$ and a warm-start state $\phi\in\mathbb C^{(2N+1)^d}$, the final state is
--   $$
--   \psi_T \;=\; U_T\,O_T\,U_{T-1}\cdots U_1\,O_1\,U_0\,\mathrm{load}(\phi),
--   $$
--   where $O_i$ is the gradient oracle $O_{\nabla E}:|x\rangle|b\rangle|w\rangle\mapsto|x\rangle|b+\nabla E(x)\rangle|w\rangle$ or its inverse, as $A$ prescribes for the $i$-th call.
--
--   It is the state measured at the end of the run of Theorem A.3.
--
--   **Formalization Note** Same oracle interleaving as the published `finalState`, started from $\mathrm{load}(\phi)$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, p.31; Eq. (7), p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_QH
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gradOracle
import Definitions.Def_GevreyGibbsSep_Supplement_WarmStartQAlg

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- The state `U_T O^{±} U_{T−1} ⋯ U_1 O^{±} U_0 (load |ϕ⟩)` of a warm-started first-order
quantum algorithm run on the warm-start state `ϕ` with the gradient oracle of `E`
(arXiv:2608.24527 (sha256 d4fd40eb…), Theorem A.3, p.31; oracle Eq. (7), p.6).

**Formalization Note** The same oracle interleaving as the published `GevreyGibbsSep.finalState`,
started from `load ϕ` instead of a fixed start vector. -/
noncomputable def wsFinalState {d : ℕ} {W : Type} {N T : ℕ} (A : WarmStartQAlg d W N T)
    (E : (Fin d → ℝ) → ℝ) (ϕ : EuclideanSpace ℂ (Grid d N)) : QH d W :=
  (List.finRange T).foldl
    (fun ψ i => A.U i.succ (if A.useInv i then (gradOracle E).symm ψ else gradOracle E ψ))
    (A.U 0 (A.load ϕ))

end Supplement

end GevreyGibbsSep


