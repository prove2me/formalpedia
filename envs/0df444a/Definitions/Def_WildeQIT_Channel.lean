-- Prove2me | Definitions.Def_WildeQIT_Channel
-- name    : WildeQIT_Channel
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:41:50.129218+00:00
-- url     : https://prove2.me/theorems/e6878b6a-a681-4523-82fa-56a4941d5a29
-- title:
--   Classical channel $N(y|x)$ and its action $Np$, $Nq$ (Corollary 10.7.2)
-- statement:
--   A **classical channel** from an input alphabet $\mathcal{X}$ to an output alphabet $\mathcal{Y}$ is a conditional probability distribution $N(y|x)$: for every input letter $x$, a probability distribution over output letters $y$. It acts on a probability distribution $p$ on $\mathcal{X}$ by
--
--   $$
--   (Np)(y) \;\equiv\; \sum_x N(y|x)\,p(x),
--   $$
--
--   which is again a probability distribution, and on an arbitrary vector $q:\mathcal{X}\to\mathbb{R}$ by the same formula $(Nq)(y)=\sum_x N(y|x)\,q(x)$.
--
--   Channels are the maps under which the relative entropy is monotone (Corollary 10.7.2, Theorem 10.8.4).
--
--   **Formalization Note.** `WildeQIT.Channel α β` abbreviates `α → WildeQIT.FinDist β`, so `(N x).prob y` is $N(y|x)$; `N.apply p : FinDist β` is $Np$ and `N.applyFun q : β → ℝ` is $Nq$ for a plain real vector `q`. The two agree on `p.prob`.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Corollary 10.7.2, §Data-Processing Inequality, LaTeX label cor-cie:mono-rel-ent (roster-items.csv line 17041); the notions 'conditional probability distribution N(y|x) (classical channel)', Np and Nq used in its statement.

import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Corollary 10.7.2 (Monotonicity of relative
entropy): a classical channel is a conditional probability distribution `N(y|x)`; it acts on a
probability distribution `p` by `(Np)(y) = ∑_x N(y|x) p(x)` and on a vector `q` by
`(Nq)(y) = ∑_x N(y|x) q(x)`.
-/

namespace WildeQIT

/-- A classical channel from `α` to `β`: for every input letter `x`, a probability distribution
`N x` over output letters, so that `(N x).prob y` is `N(y|x)`. -/
abbrev Channel (α β : Type) [Fintype β] := α → FinDist β

namespace Channel

variable {α β : Type} [Fintype α] [Fintype β]

/-- The output distribution `Np`, `(Np)(y) = ∑_x N(y|x) p(x)`. -/
noncomputable def apply (N : Channel α β) (p : FinDist α) : FinDist β where
  prob y := ∑ x, (N x).prob y * p.prob x
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg ((N x).nonneg y) (p.nonneg x)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, (N _).sum_eq_one, one_mul]
    exact p.sum_eq_one

/-- The action on an arbitrary vector `q : α → ℝ`: `(Nq)(y) = ∑_x N(y|x) q(x)`. -/
noncomputable def applyFun (N : Channel α β) (q : α → ℝ) : β → ℝ :=
  fun y => ∑ x, (N x).prob y * q x

@[simp] theorem apply_prob (N : Channel α β) (p : FinDist α) (y : β) :
    (N.apply p).prob y = ∑ x, (N x).prob y * p.prob x := rfl

@[simp] theorem applyFun_apply (N : Channel α β) (q : α → ℝ) (y : β) :
    N.applyFun q y = ∑ x, (N x).prob y * q x := rfl

end Channel

end WildeQIT


