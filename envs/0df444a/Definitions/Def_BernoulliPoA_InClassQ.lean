-- Prove2me | Definitions.Def_BernoulliPoA_InClassQ
-- name    : BernoulliPoA_InClassQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:28.209754+00:00
-- url     : https://prove2.me/theorems/7f4ff196-1f54-496d-b903-c64187d3080d
-- title:
--   Membership in $\mathcal G(\mathcal C,q)$
-- statement:
--   A Bernoulli congestion game $\Gamma^{\mathbf p}$ belongs to the class $\mathcal G(\mathcal C,q)$ when $c_e\in\mathcal C$ for every resource $e$, every strategy set is nonempty, and $0<p_i\le q$ for every player $i$.
--
--   **Formalization Note** The first two conditions are the published predicate `RobustPoA.Tight.InClass`. Since $q\le 1$ in every theorem, the condition gives $p_i\in(0,1]$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Definition 2, p.17, and abstract, p.1

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_RobustPoA_Tight_Classes
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Membership in `G(C, q)`.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Definition 2, p.17: the Bernoulli congestion games with `c_e ∈ C` for all
resources `e` and `p_i ≤ q` for all players `i`. Each strategy set is nonempty and `p_i > 0` (abstract, p.1: `p_i ∈ (0,1]`).

**Formalization Note** `RobustPoA.Tight.InClass C G` is "every latency lies in `C` and every strategy set is nonempty". With
`q ≤ 1`, which every theorem assumes, `p_i ≤ q` gives `p_i ≤ 1`. -/
def InClassQ (C : Set (ℕ → ℝ)) (q : ℝ) {n r : ℕ} (G : CongestionGame (Fin n) (Fin r))
    (p : Fin n → ℝ) : Prop :=
  RobustPoA.Tight.InClass C G ∧ ∀ i, 0 < p i ∧ p i ≤ q

end BernoulliPoA


