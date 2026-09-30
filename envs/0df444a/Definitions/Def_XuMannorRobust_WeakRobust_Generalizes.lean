-- Prove2me | Definitions.Def_XuMannorRobust_WeakRobust_Generalizes
-- name    : XuMannorRobust_WeakRobust_Generalizes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:48:09.633561+00:00
-- url     : https://prove2.me/theorems/daae2866-0627-40b5-9f6a-440474bb0a16
-- title:
--   A learning method generalizes w.r.t. a training sequence $\mathbf s^*$ (Definition 8)
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses and $l$ a loss. A **learning method** is a sequence $\mathcal A = \{\mathcal A^n\}_{n \in \mathbb N}$ of learning algorithms $\mathcal A^n : \mathcal Z^n \to \mathcal H$; write $\mathcal A_{\mathbf s(n)}$ for the hypothesis it learns from an $n$-sample set. Fix a sequence of training samples $\mathbf s^* = (s^*_1, s^*_2, \dots)$ and write $\mathbf s^*(n)$ for its first $n$ elements. The method **generalizes w.r.t. $\mathbf s^*$** if
--
--   $$\lim_{n \to \infty} \big| \mathcal L(\mathcal A_{\mathbf s^*(n)}) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n)) \big| = 0,$$
--
--   where $\mathcal L$ is the expected loss under $\mu$ and $L(h, \mathbf s^*(n))$ the average loss of $h$ on $\mathbf s^*(n)$.
--
--   The training sequence is fixed and deterministic: the notion says that the gap between the training error and the expected error of the learned hypothesis vanishes along this particular sequence. Theorem 8 characterizes it by weak robustness.
--
--   **Formalization Note** Only part 1 of Definition 8 is formalized (part 2, generalization with probability 1 over random sequences, is out of scope). The limit is `Filter.Tendsto … atTop (𝓝 0)` in $\mathbb R$. The method is a dependent function `A : (n : ℕ) → (Fin n → Z) → H`.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 409, Definition 8 (1)

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Setup

open MeasureTheory Filter Topology

namespace XuMannorRobust.WeakRobust

/-- **Generalization w.r.t. a training sequence** (Xu & Mannor 2012, p. 409, Definition 8 (1)).
A learning method `A = {A^n}` (with `A n : Zⁿ → H`) generalizes w.r.t. the fixed training sequence
`s*` if `lim_n |𝓛(A_{s*(n)}) − L(A_{s*(n)}, s*(n))| = 0`. -/
def Generalizes {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z) (l : H → Z → ℝ)
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) : Prop :=
  Tendsto
    (fun n => |expectedLoss μ l (A n (firstN sStar n))
      - avgLoss l (A n (firstN sStar n)) (firstN sStar n)|)
    atTop (𝓝 0)

end XuMannorRobust.WeakRobust


