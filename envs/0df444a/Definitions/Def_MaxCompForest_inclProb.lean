-- Prove2me | Definitions.Def_MaxCompForest_inclProb
-- name    : MaxCompForest_inclProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:41.299338+00:00
-- url     : https://prove2.me/theorems/b397389e-39aa-42b0-ad36-46593bac89d9
-- title:
--   Inclusion probability $P_{T\sim\mathrm{WST}(G)}(F\subseteq T)$
-- statement:
--   Under the law that samples a spanning tree $T$ with probability $c(T)/\tau_c(G)$, the probability that all labels of $F$ lie in $T$:
--   $$
--   P_{T\sim\mathrm{WST}(G)}(F\subseteq T)=\frac{\Phi_G(F)}{\tau_c(G)} .
--   $$
--   Maximum-completion forest selection maximizes this over label sets of size $k$.
--
--   **Formalization Note** Every statement that uses it has $G$ connected, so that the denominator is positive.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1, (3.3) p.15

import Mathlib
import Definitions.Def_MaxCompForest_tau
import Definitions.Def_MaxCompForest_Phi
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- **The inclusion probability** `P_{T∼WST(G)}(F ⊆ T) = Φ_G(F) / τ_c(G)` under the weighted spanning-tree
law.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1, (3.3) p.15.

**Formalization Note.** The quotient by `τ = 0` is junk `0`; every statement has `G` connected, so
`τ > 0`. -/
noncomputable def inclProb (G : WGraph V E) (F : Finset E) : ℝ := Phi G F / tau G

end MaxCompForest


