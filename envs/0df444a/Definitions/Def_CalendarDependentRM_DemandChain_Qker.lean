-- Prove2me | Definitions.Def_CalendarDependentRM_DemandChain_Qker
-- name    : CalendarDependentRM_DemandChain_Qker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:05.312227+00:00
-- url     : https://prove2.me/theorems/5134b7eb-666c-4620-b48c-377645508951
-- title:
--   The kernel Q of display (22), the multi-step transition and the marginal law
-- statement:
--   For the mixing argument behind the martingale bound, write $V^k(q)=P\{D^k=q\}$ and define
--
--   $$
--   Q^k(p,q)=\frac1{1-\epsilon}\big[P\{D^k=q\mid D^{k-1}=p\}-\epsilon V^k(q)\big].
--   $$
--
--   Under the transition assumption, $Q^k$ is a transition matrix, defining the auxiliary non-stationary chain $Y$ with $P\{Y^k=q\mid Y^{k-1}=p\}=Q^k(p,q)$. The definition also gives the multi-step transition probabilities of a chain from its one-step kernels, by the Chapman–Kolmogorov recursion.
--
--   **Formalization Note** The paper writes $\theta=1-\epsilon$ in this passage; that $\theta$ is not the survival rate, so it is written out here. At $\epsilon=1$ the paper's factor is undefined and Lean gives $Q=0$. The multi-step probability is a kernel computed from transitions, which is what the paper's conditional probabilities $P\{D^\ell=q\mid D^k=p\}$ mean at any state.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §J, display (22), ER p.20 (PDF 42); ER p.21 (PDF 43)

import Mathlib
import Definitions.Def_CalendarDependentRM_DemandChain

open scoped Classical

namespace CalendarDependentRM

namespace DemandChain

variable {K T : ℕ} (C : DemandChain K T)

/-- The multi-step transition `P{Z^{k+n} = q | Z^k = p}` of the non-stationary chain with one-step kernels `A`
(`A m s q` is the transition from stage `m - 1` into stage `m`), by the Chapman–Kolmogorov recursion used in the
proof of Lemma J.1 of Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Extended Results p. 21.

**Formalization Note** `multiStep A k 0 p q = 1(p = q)`. The value past the last stage is `0` and never used. -/
noncomputable def multiStep (A : Fin K → Fin T → Fin T → ℝ) (k : ℕ) : ℕ → Fin T → Fin T → ℝ
  | 0, p, q => if p = q then 1 else 0
  | n + 1, p, q =>
    if h : k + n + 1 < K then ∑ s, multiStep A k n p s * A ⟨k + n + 1, h⟩ s q else 0

/-- **The marginal `V^k(q) = P{D^k = q}`**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Extended
Results p. 20. -/
noncomputable def marginal (k : Fin K) (q : Fin T) : ℝ :=
  C.prob (fun d => d k = q)

/-- **The kernel `Q^k(p, q)` of display (22)**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, display (22),
Extended Results p. 20: `Q^k(p, q) = (1/θ) [P{D^k = q | D^{k−1} = p} − (1 − θ) V^k(q)]`, where in this passage
`θ = 1 − ε`.

**Formalization Note** The `θ` of (22) is not the survival rate, so it is written out as `1 − ε`. These are the
one-step transitions of the auxiliary chain `Y`: `P{Y^k = q | Y^{k−1} = p} = Q^k(p, q)`. At `ε = 1`, Lean's `1/0 = 0`
gives `Q = 0`, and the paper's `(1/θ)` is undefined. -/
noncomputable def Qker (ε : ℝ) (k : Fin K) (p q : Fin T) : ℝ :=
  (1 / (1 - ε)) * (C.trans k p q - ε * C.marginal k q)

end DemandChain

end CalendarDependentRM


