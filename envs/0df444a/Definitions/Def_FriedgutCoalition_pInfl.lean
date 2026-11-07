-- Prove2me | Definitions.Def_FriedgutCoalition_pInfl
-- name    : FriedgutCoalition_pInfl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:32.659625+00:00
-- url     : https://prove2.me/theorems/c6dba8be-27e6-486a-a238-fb65bcc1b857
-- title:
--   $p$-biased influence $\mathbf I^p_i(f)$ and total $p$-biased influence $\mathbf I^p(f)$ (Definition 2.1)
-- statement:
--   Let $p\in[0,1]$ and $f:\{0,1\}^n\to\{0,1\}$. The $p$-biased influence of variable $i$ on $f$ is the probability that resampling bit $i$ changes the output:
--
--   $$\mathbf I^p_i(f)=\Pr_{x,y\sim\mu_p}\big[f(x_1,\dots,x_i,\dots,x_n)\ne f(x_1,\dots,y_i,\dots,x_n)\big],$$
--
--   with $x$ and $y$ independent. The total $p$-biased influence is
--
--   $$\mathbf I^p(f)=\sum_{i=1}^n\mathbf I^p_i(f).$$
--
--   This is the notion of influence in Hatami's pseudo-junta theorem, as used in the paper (Theorem 3.4), and the quantity the encoding of §4 controls.
--
--   **Formalization Note** The probability is written as a sum over pairs $(x,y)$ of $\mu_p(x)\mu_p(y)\,[f(x)\ne f(x^{(i\leftarrow y_i)})]$. It is the resampling influence, not the pivotal influence $\Pr_x[f(x^{i\to1})\ne f(x^{i\to0})]$, which is larger by the factor $1/(2p(1-p))$. The definition accepts any real $p$ and any finite set of coordinates.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Definition 2.1, p.5

import Mathlib
import Definitions.Def_FriedgutCoalition_wProb

namespace FriedgutCoalition

/-!
# The `p`-biased (resampling) influence, Definition 2.1

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), Definition 2.1, p.5:
`I^p_i(f) = Pr_{x, y ∼ µ_p}[f(x₁, …, x_i, …, x_n) ≠ f(x₁, …, y_i, …, x_n)]` and `I^p(f) = ∑_i I^p_i(f)`.

**Formalization Note.** Stated literally, as a sum over pairs `(x, y)` of independent `µ_p` samples of
`µ_p(x) µ_p(y) [f x ≠ f (x with coordinate i replaced by y_i)]`. This is the resampling influence, not
the pivotal influence `Pr_x[f(x^{i→1}) ≠ f(x^{i→0})]`; the two differ by the factor `2p(1 − p)`.
The definition takes any real `p`; the paper's range is `p ∈ [0, 1]`. Coordinates are any finite type.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `I^p_i(f)`, the `p`-biased influence of coordinate `i` on `f : {0,1}^ι → {0,1}`. -/
noncomputable def pInfl (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x : ι → Bool, ∑ y : ι → Bool,
    (∏ k, bern p (x k)) * (∏ k, bern p (y k)) *
      (if f x ≠ f (Function.update x i (y i)) then 1 else 0)

/-- `I^p(f) = ∑_i I^p_i(f)`, the total `p`-biased influence. -/
noncomputable def totalPInfl (p : ℝ) (f : (ι → Bool) → Bool) : ℝ :=
  ∑ i, pInfl p f i

end FriedgutCoalition


