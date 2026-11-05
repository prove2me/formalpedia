-- Prove2me | Definitions.Def_WolfAreaLaw_mutualInfo
-- name    : WolfAreaLaw_mutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:19.928987+00:00
-- url     : https://prove2.me/theorems/a9eca5b0-201a-49da-9b51-e3ed98cc095e
-- title:
--   Quantum mutual information $I(A:B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$
-- statement:
--   Let $\rho_{AB}$ be an operator on a bipartite space $\mathcal H_A\otimes\mathcal H_B$ of finite dimension, with marginals (partial traces) $\rho_A=\operatorname{tr}_B\rho_{AB}$ and $\rho_B=\operatorname{tr}_A\rho_{AB}$. The **mutual information** between $A$ and $B$ is
--
--   $$
--   I(A:B) = S(\rho_A) + S(\rho_B) - S(\rho_{AB}),
--   $$
--
--   where $S$ is the von Neumann entropy $S(\rho)=-\operatorname{tr}[\rho\log\rho]$. This is Eq. (1) of the paper with the Shannon entropy replaced by the von Neumann entropy, as the paper prescribes for quantum systems. It measures the total amount of correlation between $A$ and $B$.
--
--   **Formalization Note** The composite system is indexed by the product type $A\times B$. The marginal $\rho_A$ is `QAlgorithms.traceRight ρ` (it traces out the second factor $B$) and $\rho_B$ is `QAlgorithms.traceLeft ρ` (it traces out the first factor $A$). Entropies use the natural logarithm (`WolfAreaLaw.entropy`).
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, Eq. (1), p.1, with the replacement of p.2 ("In the quantum case the ρ's become density operators (and their partial traces) and H has to be replaced by the von Neumann entropy")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_WolfAreaLaw_entropy

namespace WolfAreaLaw

/-- **Quantum mutual information** `I(A : B) = S(ρA) + S(ρB) − S(ρAB)` of a bipartite operator
`ρ = ρAB` on `H_A ⊗ H_B`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, Eq. (1), p.1 ("I(A : B) = H(ρA) + H(ρB) −
H(ρAB)"), with the replacement of p.2: "In the quantum case the ρ's become density operators (and
their partial traces) and H has to be replaced by the von Neumann entropy S(ρ) = −tr[ρ log ρ]."

**Formalization Note** The composite system is indexed by `A × B`. The marginal
`ρA = Tr_B ρAB` is `QAlgorithms.traceRight ρ` (traces out the second factor `B`), and
`ρB = Tr_A ρAB` is `QAlgorithms.traceLeft ρ` (traces out the first factor `A`). `S` is the
natural-log `WolfAreaLaw.entropy`. -/
noncomputable def mutualInfo {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  entropy (QAlgorithms.traceRight ρ) + entropy (QAlgorithms.traceLeft ρ) - entropy ρ

end WolfAreaLaw


