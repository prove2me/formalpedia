-- Prove2me | Definitions.Def_BernoulliPoA_worstPPoA
-- name    : BernoulliPoA_worstPPoA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:45:58.243986+00:00
-- url     : https://prove2.me/theorems/bc5520b1-bc3e-45da-b5c2-966c3820135a
-- title:
--   Worst-case prophet price of anarchy $\mathsf{PPoA}(\mathcal C,q)$
-- statement:
--   The **worst-case prophet price of anarchy** is the supremum over the whole class:
--   $$
--   \mathsf{PPoA}(\mathcal C,q)=\sup\bigl\{\mathsf{PPoA}(\Gamma^{\mathbf p}):\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)\bigr\}.
--   $$
--
--   **Formalization Note** The supremum runs over all numbers of players and of resources, and its value lies in $[0,\infty]$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, §3.2, p.19, with Definition 2, p.17

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_PPoA
import Definitions.Def_BernoulliPoA_InClassQ
open CongestionPoA.AsymSum
open scoped ENNReal

namespace BernoulliPoA

/-- **Worst-case prophet price of anarchy** `PPoA(C, q)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3.2, p.19 (the analogue for the PPoA of Definition 2, p.17):
the supremum of `PPoA(Γ^p)` over all games in `G(C, q)`.

**Formalization Note** The supremum runs over all numbers `n` of players and `r` of resources, with players `Fin n` and resources
`Fin r`, and is taken in `ℝ≥0∞`. -/
noncomputable def worstPPoA (C : Set (ℕ → ℝ)) (q : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ r : ℕ, ⨆ G : CongestionGame (Fin n) (Fin r), ⨆ p : Fin n → ℝ,
    ⨆ _ : InClassQ C q G p, PPoA G p

end BernoulliPoA


