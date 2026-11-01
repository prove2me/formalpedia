-- Prove2me | Definitions.Def_BernoulliPoA_expCost
-- name    : BernoulliPoA_expCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:14.831827+00:00
-- url     : https://prove2.me/theorems/24fdf89d-98ee-4888-b44e-f2ffccced67f
-- title:
--   Expected player cost $C_i(s)$
-- statement:
--   In a Bernoulli congestion game, the **expected cost** of player $i$ under the profile $s$ is
--   $$
--   C_i(s)=\sum_{e\in s_i}\sum_{\mathcal I\ni i}p(\mathcal I)\,c_e\bigl(n^{\mathcal I}_e(s)\bigr).
--   $$
--   An inactive player incurs no cost, so only the sets $\mathcal I$ containing $i$ occur.
--
--   **Formalization Note** The two sums are written in the other order. The weight $p(\mathcal I)$ already contains the factor $p_i$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (13), p.13

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_weight
import Definitions.Def_BernoulliPoA_restrict
open CongestionPoA.AsymSum

namespace BernoulliPoA

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- **Expected player cost** `C_i(s)`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.2, display (13), p.13:
`C_i(s) = ∑_{e ∈ s_i} ∑_{I ∋ i} p(I) c_e(n^I_e(s))`.

**Formalization Note** The two sums of (13) are written in the other order. An absent player has no cost: only `I ∋ i`
occur, and `weight p I` already contains the factor `p_i`. -/
noncomputable def expCost (G : CongestionGame ι E) (p : ι → ℝ) (s : ι → Finset E) (i : ι) : ℝ :=
  ∑ I ∈ Finset.univ.filter (fun I : Finset ι => i ∈ I), weight p I * cost G (restrict s I) i

end BernoulliPoA


