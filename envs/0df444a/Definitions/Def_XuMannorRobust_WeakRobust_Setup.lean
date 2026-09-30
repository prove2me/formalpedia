-- Prove2me | Definitions.Def_XuMannorRobust_WeakRobust_Setup
-- name    : XuMannorRobust_WeakRobust_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:44:41.642608+00:00
-- url     : https://prove2.me/theorems/47c59a9b-e1f3-4b5b-bf2a-ad5fd5753f08
-- title:
--   Expected loss $\mathcal L(h)$, average loss $L(h, \mathbf t(n))$ and the prefix $\mathbf s(n)$
-- statement:
--   Let $\mathcal Z$ be a measurable space of samples, $\mathcal H$ a set of hypotheses and $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss function, and let $\mu$ be a probability measure on $\mathcal Z$. For a hypothesis $h \in \mathcal H$ the **expected loss** is
--
--   $$\mathcal L(h) = \mathbb E_{z \sim \mu}\, l(h, z),$$
--
--   and for an $n$-sample set $\mathbf t(n) = (t_1, \dots, t_n) \in \mathcal Z^n$ the **average loss** of $h$ on $\mathbf t(n)$ is
--
--   $$L(h, \mathbf t(n)) = \frac1n \sum_{i=1}^n l(h, t_i).$$
--
--   For an infinite sequence of samples $\mathbf s = (s_1, s_2, \dots)$, the **prefix** $\mathbf s(n) = (s_1, \dots, s_n)$ is its first $n$ elements.
--
--   These are the three objects of Section 8 of Xu and Mannor: a learning method trained on the prefix $\mathbf s^*(n)$ of a fixed training sequence is judged by comparing its training average loss $L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n))$ with its expected loss, or with its average loss on a fresh test sample.
--
--   **Formalization Note** The expectation is the Bochner integral, which Lean sets to $0$ for a non-integrable function; every theorem of this mission assumes the loss is measurable with values in $[0, M]$, so it is integrable against a probability measure. The factor $1/n$ is $0$ for $n = 0$, where the average loss is therefore $0$. Indices run over `Fin n`, i.e. $0, \dots, n-1$, so the prefix is $(s_0, \dots, s_{n-1})$ in Lean.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, pp. 408-409, Sect. 8 (setup: s(n), L(h, t(n)), L(h))

import Mathlib

open MeasureTheory

namespace XuMannorRobust.WeakRobust

/-- **Expected loss** (Xu & Mannor 2012, p. 409, Sect. 8): `𝓛(h) = E_{z∼μ} l(h, z)`, the Bochner
integral of the loss of the hypothesis `h` against the sample distribution `μ`. -/
noncomputable def expectedLoss {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (l : H → Z → ℝ) (h : H) : ℝ :=
  ∫ z, l h z ∂μ

/-- **Average loss on a sample set** (Xu & Mannor 2012, p. 409, Sect. 8):
`L(h, t(n)) = (1/n) ∑_{i=1}^n l(h, t_i)` for an `n`-sample set `t(n) = (t_1, …, t_n)`. -/
noncomputable def avgLoss {Z H : Type*} {n : ℕ} (l : H → Z → ℝ) (h : H) (t : Fin n → Z) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, l h (t i)

/-- **First `n` elements of a sample sequence** (Xu & Mannor 2012, p. 408, Sect. 8): for a sequence
`s = (s_1, s_2, …)`, `s(n) = (s_1, …, s_n)`. Lean indices start at `0`. -/
def firstN {Z : Type*} (s : ℕ → Z) (n : ℕ) : Fin n → Z :=
  fun i => s i

end XuMannorRobust.WeakRobust


