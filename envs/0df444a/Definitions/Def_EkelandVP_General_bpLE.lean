-- Prove2me | Definitions.Def_EkelandVP_General_bpLE
-- name    : EkelandVP_General_bpLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:25:54.659657+00:00
-- url     : https://prove2.me/theorems/766233f7-0bce-41e2-a609-b4cbf7d0f443
-- title:
--   The order (1.6) on $V \times \mathbb{R}$: $(v_1,a_1) \prec (v_2,a_2)$ iff $(a_2-a_1)+\alpha\, d(v_1,v_2) \le 0$
-- statement:
--   Let $(V,d)$ be a metric space and fix a real number $\alpha$. On the product $V \times \mathbb{R}$ define the relation $\prec$ by
--
--   $$
--   (v_1,a_1) \prec (v_2,a_2) \quad\Longleftrightarrow\quad (a_2-a_1) + \alpha\, d(v_1,v_2) \le 0 .
--   $$
--
--   Thus $(v_2,a_2)$ is "greater" than $(v_1,a_1)$ when its real coordinate lies below $a_1$ by at least $\alpha$ times the distance travelled in $V$. In Ekeland's paper $\alpha > 0$ is fixed; for the proof of the variational principle one takes $\alpha = \varepsilon/\lambda$. This is the order, due to Bishop and Phelps, on which Lemma 1.2 and Theorem 1.1 are built.
--
--   **Formalization Note** `bpLE α p q` reads $p \prec q$, with $p = (v_1,a_1)$ and $q = (v_2,a_2)$. The definition itself does not require $\alpha > 0$; the theorems that need it assume it. $V \times \mathbb{R}$ carries the product topology.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 325, §1, (1.6)

import Mathlib

namespace EkelandVP.General

/-- The Bishop–Phelps order (1.6) of Ekeland (1974), p. 325, on `V × ℝ`:
`bpLE α (v₁, a₁) (v₂, a₂)` means `(v₁, a₁) ≺ (v₂, a₂)`, i.e. `(a₂ − a₁) + α d(v₁, v₂) ≤ 0`. -/
def bpLE {V : Type*} [MetricSpace V] (α : ℝ) (p q : V × ℝ) : Prop :=
  (q.2 - p.2) + α * dist p.1 q.1 ≤ 0

end EkelandVP.General


