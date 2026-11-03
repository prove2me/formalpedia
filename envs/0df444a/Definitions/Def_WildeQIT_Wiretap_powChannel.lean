-- Prove2me | Definitions.Def_WildeQIT_Wiretap_powChannel
-- name    : WildeQIT_Wiretap_powChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:00.555436+00:00
-- url     : https://prove2.me/theorems/94d0256a-714d-4fc8-9aed-7251cf991a18
-- title:
--   Tensor power $N^{\otimes n}$ of a classical channel
-- statement:
--   Let $N\equiv p_{Y|X}$ be a classical channel and $n\ge 0$. The channel $N^{\otimes n}$ describes $n$ independent uses of $N$: on input sequences $x^n=(x_1,\dots,x_n)$ it outputs sequences $y^n=(y_1,\dots,y_n)$ with
--
--   $$
--   p_{Y^n|X^n}(y^n|x^n)=\prod_{i=1}^{n} p_{Y_i|X_i}(y_i|x_i),
--   $$
--
--   where each factor is the transition probability of $N$. Its mutual information $I(N^{\otimes n})=\max_{p_{X^n}} I(X^n;Y^n)$ allows arbitrary correlated input distributions on sequences; normalized by $n$, it defines the regularized mutual information $I_{\mathrm{reg}}(N)$.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). Sequences are functions on $\{0,\dots,n-1\}$ (the book's index $i$ is $i-1$); for $n=0$ the input and output alphabets each contain only the empty sequence.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Section 13.1.1, eq. (13.11), p. 390

import Definitions.Def_WildeQIT_Channel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace WildeQIT.Wiretap

open WildeQIT

/-- **The `n`-fold tensor power `N^{⊗n}` of a classical channel.**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.1.1, (13.11), p. 390:
`N^{⊗n}` denotes `n` channels with `p_{Yⁿ|Xⁿ}(yⁿ|xⁿ) = ∏_{i=1}^n p_{Y_i|X_i}(y_i|x_i)`.

`powChannel N n` maps an input sequence `xⁿ : Fin n → α` to the product distribution
`yⁿ ↦ ∏ᵢ N(yᵢ|xᵢ)` on output sequences `Fin n → β`.

**Formalization Note.** Sequences are indexed by `Fin n` (the book's index `i` is `i − 1`); for
`n = 0` both alphabets are the one-point type of empty sequences. -/
noncomputable def powChannel {α β : Type} [Fintype β] [DecidableEq β]
    (N : Channel α β) (n : ℕ) : Channel (Fin n → α) (Fin n → β) :=
  fun x =>
    { prob := fun y => ∏ i, (N (x i)).prob (y i)
      nonneg := fun y => Finset.prod_nonneg fun i _ => (N (x i)).nonneg (y i)
      sum_eq_one := by
        rw [← Fintype.prod_sum (fun i b => (N (x i)).prob b)]
        simp [(N _).sum_eq_one] }

end WildeQIT.Wiretap


