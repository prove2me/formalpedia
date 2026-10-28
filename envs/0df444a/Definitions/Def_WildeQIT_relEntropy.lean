-- Prove2me | Definitions.Def_WildeQIT_relEntropy
-- name    : WildeQIT_relEntropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:50:39.984041+00:00
-- url     : https://prove2.me/theorems/4c8c254d-dcb9-412e-b455-162a48a16a3e
-- title:
--   Relative entropy $D(p\|q)$ (Definitions 10.5.1–10.5.2)
-- statement:
--   **Definition 10.5.1 (Support).** Let $\mathcal{X}$ be a finite set. The support of a function $f:\mathcal{X}\to\mathbb{R}$ is the subset of $\mathcal{X}$ on which $f$ is non-zero: $\operatorname{supp}(f)\equiv\{x : f(x)\neq 0\}$.
--
--   **Definition 10.5.2 (Relative entropy).** Let $p$ be a probability distribution on the alphabet $\mathcal{X}$ and let $q:\mathcal{X}\to[0,\infty)$. The relative entropy $D(p\|q)$ is
--
--   $$
--   D(p\|q) \equiv \begin{cases} \displaystyle\sum_{x} p(x)\,\log\bigl(p(x)/q(x)\bigr) & \text{if } \operatorname{supp}(p)\subseteq\operatorname{supp}(q),\\[6pt] +\infty & \text{otherwise,}\end{cases}
--   $$
--
--   with the logarithm base $2$ and the convention that terms with $p(x)=0$ contribute $0$.
--
--   The relative entropy is the fundamental divergence of information theory: mutual information and conditional mutual information are relative entropies between a joint distribution and a product (or Markov) distribution, and its non-negativity (Theorem 10.7.1) and monotonicity under channels (Corollary 10.7.2) are the sources of all entropy inequalities of the chapter. Note that $q$ is only required to be a non-negative function, not a probability distribution.
--
--   **Formalization Note.** `WildeQIT.relEntropy p q` takes `p : WildeQIT.FinDist α` and an arbitrary real function `q : α → ℝ` and returns an extended real number (`EReal`): the real value $\sum_x p(x)\log_2(p(x)/q(x))$ coerced into `EReal` when `Function.support p.prob ⊆ Function.support q` (Mathlib's `Function.support f = {x | f x ≠ 0}` is exactly Definition 10.5.1), and `⊤` ($=+\infty$) otherwise. Terms with $p(x)=0$ vanish automatically (`Real.logb 2 0 = 0`). Wilde's standing assumption $q\ge 0$ is not built into the definition; theorems about $D(p\|q)$ carry it as an explicit hypothesis.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Relative Entropy, Definition 10.5.2, LaTeX label def-cie:rel-ent (book source roster-items.csv line 16628); support as in Definition 10.5.1 (line 16617).

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.EReal.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.5.1 (Support) and
Definition 10.5.2 (Relative entropy). The support of `f : 𝒳 → ℝ` is `supp(f) = {x : f(x) ≠ 0}`
(Mathlib's `Function.support`). For a probability distribution `p` on `𝒳` and `q : 𝒳 → [0,∞)`,
`D(p‖q) ≡ ∑_x p(x) log (p(x)/q(x))` if `supp(p) ⊆ supp(q)`, and `+∞` otherwise.
-/

namespace WildeQIT

open Classical in
/-- Definition 10.5.2. The relative entropy `D(p‖q)` of a probability distribution `p` on `α`
with respect to a function `q : α → ℝ` (intended non-negative), in bits, as an extended real:
`D(p‖q) = ∑_x p(x) log₂ (p(x)/q(x))` when `supp p ⊆ supp q`, and `+∞` otherwise.
Here `supp f = {x | f x ≠ 0}` (Definition 10.5.1). Terms with `p(x) = 0` contribute `0`. -/
noncomputable def relEntropy {α : Type} [Fintype α] (p : FinDist α) (q : α → ℝ) : EReal :=
  if Function.support p.prob ⊆ Function.support q then
    ((∑ x, p.prob x * Real.logb 2 (p.prob x / q x) : ℝ) : EReal)
  else ⊤

end WildeQIT


