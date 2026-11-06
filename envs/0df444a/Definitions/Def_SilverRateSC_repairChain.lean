-- Prove2me | Definitions.Def_SilverRateSC_repairChain
-- name    : SilverRateSC_repairChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:53.599326+00:00
-- url     : https://prove2.me/theorems/fb6ff138-e928-4cce-b711-a92362bacefc
-- title:
--   Huber repair components constructed successively at the repair checkpoints
-- statement:
--   Given checkpoints $t_1<\dots<t_q$ (with $t_0=0$) in a list of stepsizes $h_1,h_2,\dots$ and an incoming pair $(\ell_1,D_1)$, the $i$-th repair has gap stepsizes $h_{t_{i-1}+1},\dots,h_{t_i-1}$ and checkpoint stepsize $b_i=h_{t_i}$. Its outgoing pair is given by (13)–(14):
--   $$\ell_{i+1}=\frac{(\kappa-1)(1-\chi_i)\delta_{\rm H}}2,\qquad D_{i+1}=D_i\frac{(1-1/\kappa)b_i\chi_i\eta_i}{2[2+(\kappa-1)(1-\chi_i)]}.$$
--   This produces the pairs $(\ell_i,D_i)_{1\le i\le q+1}$ of Lemma 4.2.
--
--   **Formalization Note** The function is indexed from $0$: its value at $i$ is $(\ell_{i+1},D_{i+1})$. `ckpt ts i` is $t_i$ and `gapList h ts i` the $i$-th gap.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §4.2, p.18; Lemma 3.2, p.16

import Mathlib
import Definitions.Def_SilverRateSC_repairPhi

namespace SilverRateSC

/-- The `i`-th selected checkpoint `t_i` of the list `ts = [t_1, …, t_q]`, with `t_0 = 0`. -/
def ckpt (ts : List ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else ts.getD (i - 1) 0

/-- The stepsizes `h_{t_{i−1}+1}, …, h_{t_i−1}` of the `i`-th gap (`i ≥ 1`). -/
noncomputable def gapList (h : ℕ → ℝ) (ts : List ℕ) (i : ℕ) : List ℝ :=
  (List.range' (ckpt ts (i - 1) + 1) (ckpt ts i - ckpt ts (i - 1) - 1)).map h

/-- **Huber repair components constructed successively** at the checkpoints `t_1 < ⋯ < t_q`
(§4.2, Lemma 4.2): from the incoming pair `(ℓ_1, D_1)`, the `i`-th repair has gap stepsizes
`h_{t_{i−1}+1}, …, h_{t_i−1}` (with `t_0 = 0`) and checkpoint stepsize `b_i = h_{t_i}`, and
produces `(ℓ_{i+1}, D_{i+1})` by (13)–(14):
`ℓ_{i+1} = (κ − 1)(1 − χ_i)δ_H/2`, `D_{i+1} = D_i (1 − 1/κ) b_i χ_i η_i / (2[2 + (κ − 1)(1 − χ_i)])`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §4.2 and Lemma 3.2, pp. 15–18.

**Formalization Note** `repairChain κ h ts ℓ₁ D₁ i` is the pair `(ℓ_{i+1}, D_{i+1})` (index
shifted by one, so `i = 0` is the incoming pair). `D_{i+1}` is the value the identity (14) of
Lemma 3.2 assigns to the Huber repair trajectory; the stepsizes are `h : ℕ → ℝ` at 1-based
positions. -/
noncomputable def repairChain (κ : ℝ) (h : ℕ → ℝ) (ts : List ℕ) (ℓ₁ D₁ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (ℓ₁, D₁)
  | i + 1 => repairStep κ (gapList h ts (i + 1)) (h (ckpt ts (i + 1)))
      (repairChain κ h ts ℓ₁ D₁ i).1 (repairChain κ h ts ℓ₁ D₁ i).2

end SilverRateSC


