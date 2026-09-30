-- Prove2me | Definitions.Def_XuMannorRobust_WeakRobust_WeaklyRobust
-- name    : XuMannorRobust_WeakRobust_WeaklyRobust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:51:02.809141+00:00
-- url     : https://prove2.me/theorems/055387d8-e3b1-46f2-8219-2da30881a2f6
-- title:
--   A learning method is weakly robust w.r.t. a training sequence $\mathbf s^*$ (Definition 9)
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, $l$ a loss, $\mathcal A = \{\mathcal A^n\}$ a learning method and $\mathbf s^*$ a fixed sequence of training samples with prefixes $\mathbf s^*(n)$. Let $\mathbf t(n) \sim \mu^n$ be a test sample of $n$ i.i.d. draws from $\mu$. The method is **weakly robust w.r.t. $\mathbf s^*$** if there is a sequence of sets $\mathcal D_n \subseteq \mathcal Z^n$ such that $\Pr(\mathbf t(n) \in \mathcal D_n) \to 1$ and
--
--   $$\lim_{n \to \infty} \Big\{ \max_{\hat{\mathbf s}(n) \in \mathcal D_n} \big| L(\mathcal A_{\mathbf s^*(n)}, \hat{\mathbf s}(n)) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n)) \big| \Big\} = 0. \qquad (6)$$
--
--   Intuitively, $\mathcal D_n$ is a set of "perturbed copies" of the training set that carries almost all of the test-sample probability, and on every such copy the learned hypothesis has nearly its training error.
--
--   **Formalization Note** Only part 1 of Definition 9 is formalized. Equation (6) is encoded as: there exist sets $D_n$ and reals $\eta_n \to 0$ with $|L(\mathcal A_{\mathbf s^*(n)}, \hat{\mathbf s}) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n))| \le \eta_n$ for all $n$ and all $\hat{\mathbf s} \in D_n$. This avoids a supremum over a possibly empty set (whose Lean value would be $0$); it is equivalent to the paper's reading for losses bounded by $M$, because $\Pr(\mathbf t(n) \in D_n) \to 1$ forces $D_n \neq \emptyset$ eventually and $\eta_n = M$ covers the finitely many earlier $n$. The convergence $\mu^n(D_n) \to 1$ is in $[0, \infty]$. The sets $D_n$ need not be measurable, as in the paper; for a non-measurable $D_n$, $\mu^n(D_n)$ is the outer measure.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 409, Definition 9 (1), Eq. (6)

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Setup

open MeasureTheory Filter Topology

namespace XuMannorRobust.WeakRobust

/-- **Weak robustness w.r.t. a training sequence** (Xu & Mannor 2012, p. 409, Definition 9 (1)).
A learning method `A` is weakly robust w.r.t. `s*` if there is a sequence of sets `D_n ⊆ Zⁿ` with
`Pr(t(n) ∈ D_n) → 1`, `t(n) ∼ μⁿ`, and
`lim_n max_{ŝ(n) ∈ D_n} |L(A_{s*(n)}, ŝ(n)) − L(A_{s*(n)}, s*(n))| = 0` (Eq. (6)).

Eq. (6) is encoded as a bound `η n` valid on all of `D_n` with `η n → 0`, not as a supremum (a
supremum over an empty `D_n` would be Lean's junk value `0`). The sets `D_n` need not be measurable;
`Measure.pi … (D n)` is then the outer measure. -/
def WeaklyRobust {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z) (l : H → Z → ℝ)
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) : Prop :=
  ∃ (D : (n : ℕ) → Set (Fin n → Z)) (η : ℕ → ℝ),
    Tendsto (fun n => Measure.pi (fun _ : Fin n => μ) (D n)) atTop (𝓝 1) ∧
    Tendsto η atTop (𝓝 0) ∧
    ∀ n, ∀ t ∈ D n,
      |avgLoss l (A n (firstN sStar n)) t
        - avgLoss l (A n (firstN sStar n)) (firstN sStar n)| ≤ η n

end XuMannorRobust.WeakRobust


