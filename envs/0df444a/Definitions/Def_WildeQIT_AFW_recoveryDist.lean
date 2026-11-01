-- Prove2me | Definitions.Def_WildeQIT_AFW_recoveryDist
-- name    : WildeQIT_AFW_recoveryDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:59.987459+00:00
-- url     : https://prove2.me/theorems/ab444aec-de38-4edf-9b1e-d8d7bacc46d1
-- title:
--   Recovery distance $\Delta = \tfrac12\inf_{\mathcal R}\|\rho_{ABC} - \mathcal R_{C\to AC}(\rho_{BC})\|_1$
-- statement:
--   Let $\rho_{ABC}$ be a tripartite state with marginal $\rho_{BC} = \mathrm{Tr}_A\,\rho_{ABC}$. Its **recovery distance** is
--
--   $$
--   \Delta \equiv \frac12 \inf_{\mathcal R_{C\to AC}} \bigl\|\rho_{ABC} - \mathcal R_{C\to AC}(\rho_{BC})\bigr\|_1 ,
--   $$
--
--   the infimum being over all quantum channels $\mathcal R: \mathcal L(\mathcal H_C)\to\mathcal L(\mathcal H_A\otimes\mathcal H_C)$, and $\|\cdot\|_1$ the trace norm.
--
--   It quantifies how far $\rho_{ABC}$ is from a quantum Markov chain $A - C - B$: $\Delta = 0$ exactly when some channel acting on $C$ alone regenerates $A$.
--
--   **Formalization Note** The infimum is the real `sInf` of the values over all `WildeQIT.QChannel C (A × C)`, divided by 2, with $\|\cdot\|_1$ the published `WildeQIT.traceNorm` and $\mathcal R_{C\to AC}(\rho_{BC})$ the definition `WildeQIT.AFW.recoverBC`. The set of values is bounded below by $0$ and nonempty whenever $\mathcal H_A \neq 0$ (the channel that appends a fixed basis state of $A$ exists), which holds whenever a density operator on $A\otimes B\otimes C$ exists; so `sInf` is the true infimum in every case the theorems use.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.5, (11.283), p. 362

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_AFW_recoverBC

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.5,
(11.283), p. 362: "∆ ≡ ½ inf_{R_{C→AC}} ∥ρ_ABC − R_{C→AC}(ρ_BC)∥₁, where the optimization is with
respect to channels R : L(H_C) → L(H_A ⊗ H_C)."

**Formalization Note.** The tripartite system is `A × (B × C)`, `ρ_BC = Tr_A ρ` is
`WildeQIT.partialTraceLeft ρ`, `R(ρ_BC)` is `recoverBC R ρ_BC`, and `∥·∥₁` is the published
`WildeQIT.traceNorm`. The infimum is the real `sInf` of the set of values over all channels
`R : WildeQIT.QChannel C (A × C)`. This set is bounded below by `0` and is nonempty whenever `A`
is nonempty (a channel exists), which holds for every `A` carrying a density operator, so
`sInf` is the true infimum in every case the theorems use. -/
noncomputable def recoveryDist {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  sInf (Set.range fun R : WildeQIT.QChannel C (A × C) =>
    WildeQIT.traceNorm (ρ - recoverBC R (WildeQIT.partialTraceLeft ρ))) / 2

end WildeQIT.AFW


