-- Prove2me | Definitions.Def_WildeQIT_AFW_qCondMutualInfo
-- name    : WildeQIT_AFW_qCondMutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:10.235597+00:00
-- url     : https://prove2.me/theorems/13c376f1-8351-4177-bc78-27ff0e717e28
-- title:
--   Conditional quantum mutual information $I(A;B|C)_\rho$
-- statement:
--   Let $\rho_{ABC}$ be a tripartite state on $\mathcal H_A \otimes \mathcal H_B \otimes \mathcal H_C$. Its **conditional quantum mutual information** is
--
--   $$
--   I(A;B|C)_\rho \equiv H(A|C)_\rho + H(B|C)_\rho - H(AB|C)_\rho ,
--   $$
--
--   with $H(X|C) = H(XC) - H(C)$ the conditional entropy. Expanded, this is
--
--   $$
--   I(A;B|C)_\rho = H(AC)_\rho + H(BC)_\rho - H(ABC)_\rho - H(C)_\rho ,
--   $$
--
--   the entropies of the marginals $\rho_{AC}$, $\rho_{BC}$, $\rho_{ABC}$, $\rho_C$, with the von Neumann entropy $H(\omega) = -\mathrm{Tr}\{\omega\log_2\omega\}$.
--
--   Its non-negativity is strong subadditivity; Theorem 11.10.5 bounds it by how well $\rho_{ABC}$ can be recovered from $\rho_{BC}$ by a channel acting on $C$.
--
--   **Formalization Note** The tripartite space is the index type `A × (B × C)`. $\rho_{BC}$ is `WildeQIT.partialTraceLeft ρ`, $\rho_C$ is `partialTraceLeft` applied twice, $\rho_{AC}$ is `WildeQIT.AFW.traceMiddle ρ`, and $H$ is `QAlgorithms.vnEntropy` (base 2). The definition uses the expanded form, which equals (11.88) by Definition 11.4.1.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §11.7, (11.88), p. 337; Definition 11.4.1, (11.50), p. 329

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_AFW_traceMiddle

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §11.7, (11.88), p. 337:
"We define the conditional quantum mutual information I(A; B|C)_ρ of any tripartite state
ρ_ABC ∈ D(H_A ⊗ H_B ⊗ H_C) … I(A; B|C)_ρ ≡ H(A|C)_ρ + H(B|C)_ρ − H(AB|C)_ρ."

With `H(X|C) = H(XC) − H(C)` (Definition 11.4.1) this is
`H(AC) + H(BC) − H(ABC) − H(C)`, which is the formula used here.

**Formalization Note.** The tripartite system is the index type `A × (B × C)`;
`ρ_BC = Tr_A ρ` is `WildeQIT.partialTraceLeft ρ`, `ρ_C = Tr_B ρ_BC` is
`WildeQIT.partialTraceLeft (WildeQIT.partialTraceLeft ρ)`, `ρ_AC = Tr_B ρ` is `traceMiddle ρ`,
and `H` is `QAlgorithms.vnEntropy` (base 2). Total on matrices; statements assume density
operators. -/
noncomputable def qCondMutualInfo {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (traceMiddle ρ) + QAlgorithms.vnEntropy (WildeQIT.partialTraceLeft ρ) -
    QAlgorithms.vnEntropy ρ -
    QAlgorithms.vnEntropy (WildeQIT.partialTraceLeft (WildeQIT.partialTraceLeft ρ))

end WildeQIT.AFW


