-- Prove2me | Definitions.Def_EnvelopeMSLP_IsTameData
-- name    : EnvelopeMSLP_IsTameData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:52.727803+00:00
-- url     : https://prove2.me/theorems/e0501bc3-e786-4e54-86fa-c6af52696acc
-- title:
--   Tame data, the hypothesis (T) of the correction
-- statement:
--   Let $\Theta\subseteq\mathbb R$ and $d:\mathbb R\to\mathbb R^\iota$. The data $d$ are **tame on $\Theta$** when for every polynomial $p$ in the entries of the data,
--   $$\Theta\cap\partial\{\theta\in\Theta: p(d(\theta))=0\}\quad\text{is Lebesgue null.}$$
--   Theorems 2 and 3 of the paper are false for differentiable, even $C^\infty$, data, because the zero set of a polynomial in the data can have a fat boundary. This condition is what the proof of Theorem 2 needs, and real-analytic data satisfy it.
--
--   **Formalization Note** The boundary is intersected with $\Theta$ because the boundary of an open $\Theta$ can itself have positive measure, and such $\Theta$ must not be excluded. The condition mentions the data only, never a solution, a basis or the value.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), correction of Theorems 2 and 3, pp.10, 13 (no printed counterpart)

import Mathlib

namespace EnvelopeMSLP

/-- **Tame data, the hypothesis (T) of the correction of Theorems 2 and 3.** For every polynomial `p`
in the entries of the data, the set `Θ ∩ ∂{θ ∈ Θ : p(d(θ)) = 0}` is Lebesgue null.

No printed counterpart. Theorems 2 and 3 of Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), pp.10, 13, are false as printed: the proof of
Theorem 2 claims that `D(Θ) ∩ S_i` is connected, and a `C^∞` curve can meet a manifold in a Cantor
set of positive measure.

**Formalization Note.** The boundary is intersected with `Θ` because the boundary of an open `Θ`
itself can have positive measure, and such `Θ` must not be excluded. The condition mentions the
data only, never a solution, a basis or the value. -/
def IsTameData {ι : Type*} (Θ : Set ℝ) (d : ℝ → ι → ℝ) : Prop :=
  ∀ p : MvPolynomial ι ℝ,
    MeasureTheory.volume (Θ ∩ frontier {θ | θ ∈ Θ ∧ MvPolynomial.eval (d θ) p = 0}) = 0

end EnvelopeMSLP


