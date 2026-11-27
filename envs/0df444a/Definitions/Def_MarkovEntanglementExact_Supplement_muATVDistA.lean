-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistA
-- name    : MarkovEntanglementExact_Supplement_muATVDistA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:46:07.450404+00:00
-- url     : https://prove2.me/theorems/3e9210cf-d122-5fb1-b234-616ae6748f53
-- title:
--   $\mu$-weighted agent-wise total variation distance w.r.t. agent $A$
-- statement:
--   Given a probability distribution $\mu$ on joint state-action pairs, the **$\mu$-weighted agent-wise total variation distance** between transition matrices $P$, $P'$ with respect to agent $A$ is (Definition 8)
--   $$\|P-P'\|_{\mu\text{-ATV}_A}=\frac12\sup_{\|x\|_\infty=1}\big\|(P-P')(x\otimes e)\big\|_\mu,$$
--   where $x$ ranges over vectors on agent $A$'s state-action pairs and $\|y\|_\mu=\sum\mu|y|$. It measures how differently $P$ and $P'$ move agent $A$, averaged over the occupancy.
--
--   **Formalization Note** The supremum is outside the $\mu$-sum, as in Definition 8.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 8, p.19

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement Matrix

namespace MarkovEntanglementExact.Supplement

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- The `μ`-weighted agent-wise total variation distance with respect to agent `A`
(Definition 8): `‖P − P′‖_{μ−ATV_A} = ½ sup_{‖x‖∞ = 1} ‖(P − P′)(x_A)‖_μ`, where `x_A` is
the vector `x` on agent `A`'s pairs lifted to joint pairs (`x ⊗ e` for agent `A`,
`e ⊗ x` for agent `B`) and `‖·‖_μ` is the `μ`-norm of Definition 6.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 8, p.19
("The µ-weighted ATV distance w.r.t agent B can be defined similarly"), with Definition 6, p.18.

**Formalization Note.** The supremum is outside the `μ`-sum, as in Definition 8; Eq. (7) is
only an upper bound for the resulting measure. `‖x‖ = 1` is Mathlib's sup norm on functions,
i.e. `‖x‖∞ = 1`. The lifted vector at the joint pair `q` is `x.1 q.1`. -/
noncomputable def muATVDistA (μ : SA × SB → ℝ) (P P' : Matrix (SA × SB) (SA × SB) ℝ) : ℝ :=
  (1 / 2) * ⨆ x : {x : SA → ℝ // ‖x‖ = 1}, muNorm μ ((P - P') *ᵥ fun q => x.1 q.1)

end MarkovEntanglementExact.Supplement


