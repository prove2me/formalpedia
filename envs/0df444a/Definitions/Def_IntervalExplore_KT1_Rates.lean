-- Prove2me | Definitions.Def_IntervalExplore_KT1_Rates
-- name    : IntervalExplore_KT1_Rates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:53.45965+00:00
-- url     : https://prove2.me/theorems/8f40f145-4de8-42c7-a4a6-053fe323257d
-- title:
--   Density factor, connectivity-window witness and ordering-distance sum
-- statement:
--   For integers $3\le n\le m$, define the density factor and window witness used in the paper by
--   $$
--   \xi(n,m)=\frac{\ln n}{1+\ln m-\ln n},\qquad
--   \tau_c(n,m)=c\left\lceil\xi(n,m)m+n(\ln n)^2\right\rceil.
--   $$
--   Here $c$ is a positive natural-number constant. The edge-charge scale is $\xi(n,m)m+n(\log_2 n)^2$, retaining the paper's distinction between natural and base-two logarithms.
--
--   For a finite graph and an enumeration $v_1,\ldots,v_n$ of its vertices, the later-distance summand is
--   $$
--   f(i)=\min_{j>i}d_G(v_i,v_j)\qquad (i<n).
--   $$
--   The last index has no later vertex and contributes zero. Lemma 3 only sums the earlier indices and assumes connectivity. These quantities record the exact formulas needed by the graph-ordering bound, the charge estimate and the full exploration theorem.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), ξ, p.4 (PDF p.5); τ, §2, p.5 (PDF p.6); Lemma 3, p.7 (PDF p.8)

import Definitions.Def_IntervalExplore_KT1_Model

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- §1.3, p.4: natural logarithms. Used only with 3 ≤ n ≤ m. -/
noncomputable def xi (n m : ℕ) : ℝ := Real.log n / (1 + Real.log m - Real.log n)

/-- §2, p.5: the paper's witness for the window and deadline, with an absolute c. -/
noncomputable def tau (c n m : ℕ) : ℕ :=
  c * ⌈xi n m * m + n * (Real.log n) ^ 2⌉₊

/-- The base-two expression in Lemma 6 and Theorem 2. -/
noncomputable def chargeScale (n m : ℕ) : ℝ :=
  xi n m * m + n * (Real.logb 2 n) ^ 2

/-- Lemma 3: at the final index there are no later vertices, and its summand is zero.
At every earlier index the set is a finite nonempty set of graph distances. -/
noncomputable def laterDistance {V : Type} (G : SimpleGraph V) {n : ℕ}
    (enumeration : Fin n ≃ V) (i : Fin n) : ℕ :=
  sInf {d : ℕ | ∃ j : Fin n, i < j ∧ G.dist (enumeration i) (enumeration j) = d}

end IntervalExplore.KT1


