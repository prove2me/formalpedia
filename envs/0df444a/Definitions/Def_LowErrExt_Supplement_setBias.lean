-- Prove2me | Definitions.Def_LowErrExt_Supplement_setBias
-- name    : LowErrExt_Supplement_setBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:37.504614+00:00
-- url     : https://prove2.me/theorems/430de809-aa56-480f-81b3-02f63a932223
-- title:
--   Bias $\mathrm{bias}[\mathsf{IP}(X,Y)]$ of the inner product on two sets, and the bias of a bit
-- statement:
--   For finite sets $X,Y\subseteq\mathbb F_2^n$, the **bias of the inner product** on $X\times Y$ is
--   $$\mathrm{bias}[\mathsf{IP}(X,Y)]=\Big|\mathbb E_{x\sim X,\,y\sim Y}\big[(-1)^{\mathsf{IP}(x,y)}\big]\Big|,$$
--   where $x$ and $y$ are uniform and independent on $X$ and $Y$, and $\mathsf{IP}(x,y)=\sum_i x_iy_i\in\mathbb F_2$.
--
--   For a random bit $\mathbf W\sim\mathbb F_2$, the **bias** is $\mathrm{bias}[\mathbf W]=|\mathbb E[(-1)^{\mathbf W}]|$.
--
--   The first is the quantity approximate duality (Theorem 1.3) starts from; the second measures how far a parity of a bilinear map is from constant or from unbiased (Theorem 1.4).
--
--   **Formalization Note** The inner product is the published `LowErrExt.ip`. The expectation is undefined on an empty set; Lean's convention $x/0=0$ gives bias $0$ there, so a lower bound $\varepsilon>0$ on the bias forces both sets to be nonempty.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), §1.2, p.6 (bias[IP(X, Y)]); p.7 (bias of a parity)

import Mathlib
import Definitions.Def_LowErrExt_bias

namespace LowErrExt.Supplement

open LowErrExt

/-- **Bias of the inner product on a pair of sets.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §1.2,
p.6: "let IP : F₂ⁿ × F₂ⁿ → F₂ denote the inner product function over F₂, let X, Y ⊆ F₂ⁿ, and define
bias[IP(X, Y)] := |E_{x∼X, y∼Y}[(−1)^{IP(x,y)}]|."
`setBias S T` is the absolute value of the average of `(−1)^{IP(x,y)}` over `x ∈ S`, `y ∈ T`
(`x`, `y` uniform and independent).

**Formalization Note.** The inner product is the published `LowErrExt.ip`; `(−1)^b` for `b ∈ 𝔽₂`
uses the representative `b.val ∈ {0, 1}`. The expectation is undefined on an empty set; Lean's
`x / 0 = 0` makes `setBias` equal to `0` when `S` or `T` is empty, so a hypothesis
`ε ≤ setBias S T` with `ε > 0` forces both sets to be nonempty, and `setBias S T = 1` likewise. -/
noncomputable def setBias {n : ℕ} (S T : Finset (Fin n → ZMod 2)) : ℝ :=
  |(∑ x ∈ S, ∑ y ∈ T, (-1 : ℝ) ^ (ip x y).val) / ((S.card : ℝ) * (T.card : ℝ))|

/-- **Bias of a bit.** `bitBias W = |E[(−1)^W]|` for a random bit `W ∼ 𝔽₂`
(Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §1.2,
p.7, "bias[ψ(f(X, Y)|_{(X,Y)∈P})]"; for a bit, bias[Z] = |E[(−1)^Z]|, p.26).

**Formalization Note.** `(−1)^b` uses the representative `b.val ∈ {0, 1}`. -/
noncomputable def bitBias (W : PMF (ZMod 2)) : ℝ :=
  |∑ b : ZMod 2, (W b).toReal * (-1 : ℝ) ^ b.val|

end LowErrExt.Supplement


