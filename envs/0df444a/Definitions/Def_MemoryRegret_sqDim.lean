-- Prove2me | Definitions.Def_MemoryRegret_sqDim
-- name    : MemoryRegret_sqDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:25.891896+00:00
-- url     : https://prove2.me/theorems/2cfb1069-8124-4793-92e9-980d00115cab
-- title:
--   Statistical query dimension
-- statement:
--   Let $X$ be a finite set, $H\subseteq\{0,1\}^X$ and $\mu$ a probability distribution on $X$. The **statistical query dimension of $H$ with respect to $\mu$**, $\mathrm{SQDim}_\mu(H)$, is the largest integer $d$ for which there are $f_1,\dots,f_d\in H$ with
--   $$\Bigl|\mathbb E_{x\sim\mu}\bigl[(-1)^{f_i(x)+f_j(x)}\bigr]\Bigr|\le\frac1d\qquad\text{for all } i\ne j.$$
--   The **distribution-independent statistical query dimension** is $\mathrm{SQDim}(H)=\max_\mu\mathrm{SQDim}_\mu(H)$, the maximum over all distributions on $X$.
--
--   This is the combinatorial parameter that governs the memory-regret tradeoff of the mission's goal theorem.
--
--   **Formalization Note** "Largest" and "max" are `sSup` of sets of natural numbers. The inner set is bounded because for $d\ge2$ a repeated function would have correlation $1>1/d$, so the witnesses are distinct and $d\le|\{0,1\}^X|$; the outer values are then bounded naturals, so the supremum is an attained maximum. If $X$ is empty there is no distribution and the value is $0$.
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Definition 2, p.8

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_sgn

namespace MemoryRegret

/-- `corrWrt μ f g = E_{x∼µ}[(−1)^{f(x)+g(x)}] = ∑_x µ(x)·(−1)^{f(x)}·(−1)^{g(x)}`. -/
noncomputable def corrWrt {X : Type} [Fintype X] (μ : X → ℝ) (f g : X → Bool) : ℝ :=
  ∑ x, μ x * (sgn (f x) * sgn (g x))

/-- SQDim_µ(H): the largest `d` such that there exist `f_1, …, f_d ∈ H` with
`|E_{x∼µ}[(−1)^{f_i(x)+f_j(x)}]| ≤ 1/d` for all `i ≠ j` (Definition 2, p.8). -/
noncomputable def sqDimWrt {X : Type} [Fintype X] (μ : X → ℝ) (H : Set (X → Bool)) : ℕ :=
  sSup {d : ℕ | ∃ f : Fin d → X → Bool, (∀ i, f i ∈ H) ∧
    ∀ i j, i ≠ j → |corrWrt μ (f i) (f j)| ≤ 1 / (d : ℝ)}

/-- **Statistical query dimension (Definition 2).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Definition 2, p.8 ([Kea98, BFJ+94]): "Given a distribution µ over X, the statistical query
dimension of H with respect to µ, denoted by SQDim_µ(H), is the largest integer d such that
there exist d functions f_1, …, f_d ∈ H satisfying |E_{x∼µ}[(−1)^{f_i(x)+f_j(x)}]| ≤ 1/d for
all i ≠ j. The distribution-independent statistical query dimension of H is defined as
SQDim(H) := max_µ SQDim_µ(H), where maximum is over all distributions over X."

`sqDim H` is the largest value of `sqDimWrt μ H` over probability vectors `μ` on `X`.

**Formalization Note.** "Largest" and "max" are `sSup` of sets of natural numbers. For a
probability vector `µ` the set defining `sqDimWrt μ H` is bounded: when `d ≥ 2`, two equal
witnesses `f_i = f_j` would have correlation `1 > 1/d`, so the witnesses are distinct and
`d ≤ |X → Bool|` (proved in the mission's sanity file). Hence the values of `sqDimWrt` over
probability vectors are bounded naturals, and the outer `sSup` is a maximum that is attained.
`d = 0` always qualifies (no witnesses), and `d = 1` qualifies exactly when `H` is nonempty.
Labels are `Bool` (`false = 0`); `(−1)^{a+b}` is `sgn a * sgn b`. If `X` is empty there is no
probability vector and `sqDim H = 0`. -/
noncomputable def sqDim {X : Type} [Fintype X] (H : Set (X → Bool)) : ℕ :=
  sSup {d : ℕ | ∃ μ : X → ℝ, IsProbVec μ ∧ sqDimWrt μ H = d}

end MemoryRegret


