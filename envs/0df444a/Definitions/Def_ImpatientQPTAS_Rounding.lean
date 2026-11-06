-- Prove2me | Definitions.Def_ImpatientQPTAS_Rounding
-- name    : ImpatientQPTAS_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:32.237938+00:00
-- url     : https://prove2.me/theorems/956e555b-2e95-48d8-9c0c-1be83b51af60
-- title:
--   §§2.2–2.3, pp.9–10 — the rounded rewards and probabilities, and the first-move values
-- statement:
--   With $\delta=\epsilon^2/16$, let $U(x)$ round $x>0$ up to the nearest power of $1+\delta$, and $D(x)$ round it down. For an average customer the **rounded probabilities** are
--   $$
--   p^\uparrow=U(p),\quad p^\downarrow=\frac{U(p)}{1+\delta}\quad\text{when } p\le \epsilon/4,\qquad
--   p^\uparrow=1-D(1-p),\quad p^\downarrow=1-(1+\delta)D(1-p)\quad\text{otherwise.}
--   $$
--   The **rounded reward** $\tilde r_i$ is $0$ when $r_i\le(\epsilon/n)\,r_{\max}$, and otherwise $r_i$ rounded down to the grid $r_{\max}(1+\epsilon)^{-j}$, $j\in\mathbb N$.
--
--   Write $\tilde V$ for the optimal value with rewards $\tilde r$ and probabilities $p^\uparrow$. The rounded value of a first move is
--   $$
--   \tilde Q(i)=\tilde r_i+\mathbb E_{p^\uparrow}\big[\tilde V(\text{survivors of }C_{\mathrm{average}}\setminus\{i\})\big],
--   $$
--   and $\tilde X=\max_{i\in C_{\mathrm{average}}\cup C_{\mathrm{quit}}}\tilde Q(i)$. For rewards $\rho$ and the true probabilities, $X^\rho$ is the larger of the optimal value of $C_{\mathrm{average}}$ and of $\max_{q\in C_{\mathrm{quit}}}\big(\rho_q+\mathbb E_p[V(\text{survivors of }C_{\mathrm{average}})]\big)$. The internal accuracy of the algorithm is $e=1/\lceil16/\epsilon\rceil$.
--
--   These objects connect the analysis of §§2–3 to the computed policy.
--
--   **Formalization Note** These are pure specifications, and none of them occurs in the program. The reward grid is relative to $r_{\max}$: the page's rounding after normalizing $r_{\max}=1$, which needs no logarithm. The two bullets of p.9 overlap at $r_i=(\epsilon/n)r_{\max}$, and the value there is $0$. `pUp` and `pDown` are read on average customers only.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.2, p.9; §2.3, p.10; §2.1, p.8; §2.6, p.13

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes

namespace ImpatientQPTAS

/-- The operator `U(·)` of §2.3, Segev, arXiv:2209.13878v1, p.10: rounds `x > 0` up to the nearest
power of `1 + δ`, that is `(1+δ)^k` for the least integer `k` with `x ≤ (1+δ)^k`.

**Formalization Note.** A pure specification. It is read only on `x > 0`, where `Real.logb` is
meaningful, and it appears in no program. -/
noncomputable def U (δ x : ℝ) : ℝ :=
  (1 + δ) ^ ⌈Real.logb (1 + δ) x⌉

/-- The operator `D(·)` of §2.3, Segev, arXiv:2209.13878v1, p.10: rounds `x > 0` down to the nearest
power of `1 + δ`, that is `(1+δ)^k` for the greatest integer `k` with `(1+δ)^k ≤ x`. -/
noncomputable def D (δ x : ℝ) : ℝ :=
  (1 + δ) ^ ⌊Real.logb (1 + δ) x⌋

/-- The rounded-up probability `p↑`, §2.3, Segev, arXiv:2209.13878v1, p.10, with `δ = ε²/16`: `U(x)`
when `x ≤ ε/4` and `1 − D(1 − x)` otherwise.

**Formalization Note.** The value is the page's on the average range `[ε/n², 1 − ε/n]`, which is the
only place it is read. It depends on `ε` only; `n` enters through the hypothesis "average". -/
noncomputable def pUp (ε x : ℝ) : ℝ :=
  if x ≤ ε / 4 then U (ε ^ 2 / 16) x else 1 - D (ε ^ 2 / 16) (1 - x)

/-- The rounded-down probability `p↓`, §2.3, Segev, arXiv:2209.13878v1, p.10, with `δ = ε²/16`:
`U(x)/(1+δ)` when `x ≤ ε/4` and `1 − (1+δ)·D(1 − x)` otherwise. -/
noncomputable def pDown (ε x : ℝ) : ℝ :=
  if x ≤ ε / 4 then U (ε ^ 2 / 16) x / (1 + ε ^ 2 / 16)
  else 1 - (1 + ε ^ 2 / 16) * D (ε ^ 2 / 16) (1 - x)

/-- The rounded-down reward `r̃`, §2.2, Segev, arXiv:2209.13878v1, p.9: `0` when `x ≤ (ε/n)·r_max`,
and otherwise `x` rounded down to the grid `r_max·(1+ε)^(-j)`, `j ∈ ℕ`.

**Formalization Note.** The grid is relative to `r_max`: the page's rounding after normalizing
`r_max = 1`, the same count of values and the same bounds of Lemma 2.3, and computable with no
logarithm. The two bullets of p.9 overlap at `x = (ε/n)·r_max`; this takes the value `0` there. -/
noncomputable def rRound (ε : ℝ) (n : ℕ) (rm x : ℝ) : ℝ :=
  if x ≤ ε / (n : ℝ) * rm then 0
  else rm * (1 + ε) ^ (-⌈Real.logb (1 + ε) (rm / x)⌉)

/-- The internal accuracy `e = 1/m`, `m = ⌈16/ε⌉`, at which the program runs. The paper's chain ends
at `1 − O(ε)` with `1/ε ∈ ℕ` (p.15); `13·e < ε` makes the guarantee the printed `1 − ε`. -/
noncomputable def accuracy (ε : ℝ) : ℝ :=
  1 / (⌈16 / ε⌉₊ : ℝ)

/-- The rounded rewards at accuracy `e`, against the global `r_max` of the instance. -/
noncomputable def rTilde {n : ℕ} (e : ℝ) (I : Instance n) : Fin n → ℝ :=
  fun i => rRound e n (rmax I.r) (I.r i)

/-- The rounded-up probabilities at accuracy `e`. Read only on average customers. -/
noncomputable def pTilde {n : ℕ} (e : ℝ) (I : Instance n) : Fin n → ℝ :=
  fun i => pUp e (I.p i)

/-- The rounded value of serving `i` first, then playing optimally among the surviving average
customers: `Q̃(i) = r̃_i + E_{p↑}[Ṽ(survivors of C_average \ {i})]`, with `Ṽ = V r̃ p↑`. -/
noncomputable def Qt {n : ℕ} (e : ℝ) (I : Instance n) (i : Fin n) : ℝ :=
  rTilde e I i +
    thin (pTilde e I) ((Caverage e I).erase i) (V (rTilde e I) (pTilde e I))

/-- `X̃ = max_{i ∈ C_average ∪ C_quit} Q̃(i)`, and `0` when that set is empty. -/
noncomputable def Xt {n : ℕ} (e : ℝ) (I : Instance n) : ℝ :=
  maxOn (Caverage e I ∪ Cquit e I) (Qt e I)

/-- `X^ρ`, for rewards `ρ` and the true departure probabilities: the larger of the optimal value of
`C_average`, and the best value of serving a quitter first and then playing optimally among the
surviving average customers. Both are `0` when the sets are empty. -/
noncomputable def Xval {n : ℕ} (e : ℝ) (I : Instance n) (ρ : Fin n → ℝ) : ℝ :=
  max (V ρ I.p (Caverage e I))
    (maxOn (Cquit e I) fun q => ρ q + thin I.p (Caverage e I) (V ρ I.p))

end ImpatientQPTAS


