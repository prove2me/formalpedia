-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistN
-- name    : MarkovEntanglementExact_Supplement_muATVDistN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:48:15.321669+00:00
-- url     : https://prove2.me/theorems/2ce22e88-e691-5c89-ac81-63d46c7b8aef
-- title:
--   $\mu$-weighted agent-wise total variation distance w.r.t. agent $i$ of $N$
-- statement:
--   For $N$ agents and a distribution $\mu$ on joint pairs, the **$\mu$-weighted agent-wise total variation distance** with respect to agent $i$ is
--   $$\|P-P'\|_{\mu\text{-ATV}_i}=\frac12\sup_{\|x\|_\infty=1}\big\|(P-P')\big((e\otimes)^{i-1}x(\otimes e)^{N-i}\big)\big\|_\mu,$$
--   where $x$ ranges over vectors on agent $i$'s state-action pairs.
--
--   **Formalization Note** The lifted vector takes the value $x(q_i)$ at the joint pair $q$; the supremum is outside the $\mu$-sum.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 8, p.19, in the N-agent form of Theorem 6, pp.21–22

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement Matrix

namespace MarkovEntanglementExact.Supplement

/-- The `μ`-weighted agent-wise total variation distance with respect to agent `i` of an
`N`-agent system (Definition 8 in `N`-agent form):
`‖P − P′‖_{μ−ATV_i} = ½ sup_{‖x‖∞ = 1} ‖(P − P′)((e⊗)^{i−1} x (⊗e)^{N−i})‖_μ`, where the lifted
vector takes the value `x(q_i)` at the joint pair `q`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 8, p.19,
used for `N` agents in Theorem 6, pp.21–22 ("w.r.t the µ^π_{1:N}-weighted agent-wise total
variation distance"); the lift `(e⊗)^{i−1} r_i (⊗e)^{N−i}` is that of §6, p.20.

**Formalization Note.** The supremum is outside the `μ`-sum, as in Definition 8; this is not the
published `muAgentTVDistN`, which is the per-row upper bound of Eq. (7). `‖x‖ = 1` is Mathlib's
sup norm. -/
noncomputable def muATVDistN {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] (i : Fin N) (μ : Joint S → ℝ)
    (P P' : Matrix (Joint S) (Joint S) ℝ) : ℝ :=
  (1 / 2) * ⨆ x : {x : S i → ℝ // ‖x‖ = 1}, muNorm μ ((P - P') *ᵥ fun q => x.1 (q i))

end MarkovEntanglementExact.Supplement


