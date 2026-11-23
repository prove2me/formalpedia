-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_ValidBonus
-- name    : CorruptRobustRL_Supervised_Supplement_ValidBonus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:11:22.557156+00:00
-- url     : https://prove2.me/theorems/db4e896b-37ed-402e-8e31-e0a17ffba6f2
-- title:
--   Optimal-value bonus validity, Condition C.3
-- statement:
--   Let $M$ have nominal rewards $r^\star$, transitions $p^\star$ and optimal values $V_h^\star$, and let $m=(\widehat r,\widehat p,b)$ be a model estimate. For every $h\in[H]$, state $x$ and action $a$, require
--   $$\left|\widehat r(x,a)-r^\star(x,a)+(\widehat p(x,a)-p^\star(x,a))^\top V_{h+1}^\star\right|\le b(x,a).$$
--   This is precisely optimal-value validity (C.3). It constrains the error of the estimate against the nominal optimal value, independently of the two VI inequalities.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 44, Condition C.3, (C.3)

import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X] [Fintype A] [Nonempty A]

/-- Condition C.3, specifically the optimal-value error, not a bonus-validity surrogate. -/
def HasValidBonus (M : NominalMDP X A) (H : ℕ) (m : ModelEst X A) : Prop :=
  ∀ h < H, ∀ x a, |m.dev M (Vstar M H (h + 1)) x a| ≤ m.b x a

end CorruptRobustRL.Supervised.Supplement


