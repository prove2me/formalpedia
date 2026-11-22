-- Prove2me | Definitions.Def_AlmostPeriodic_BohrAlmostPeriodic
-- name    : AlmostPeriodic_BohrAlmostPeriodic
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T18:34:40.789056+00:00
-- url     : https://prove2.me/theorems/95722be0-099a-4d29-b9cc-4cb9e7ab31fc
-- title:
--   Relatively dense sets and Bohr almost periodic functions $f:\mathbb R\to E$
-- statement:
--   **Bohr almost periodic functions.** A subset $A\subseteq\mathbb R$ is *relatively dense* if there is a length $L>0$ such that every closed interval of length $L$ contains a point of $A$:
--   $$\exists L>0\ \forall a\in\mathbb R:\quad A\cap[a,a+L]\neq\varnothing .$$
--   Let $E$ be a normed (additive) group. A function $f:\mathbb R\to E$ is *almost periodic in the sense of H. Bohr* (uniformly almost periodic) if $f$ is continuous and, for every $\varepsilon>0$, its set of $\varepsilon$-translation numbers
--   $$T(f,\varepsilon)=\{\tau\in\mathbb R:\ \|f(x+\tau)-f(x)\|\le\varepsilon\ \text{ for all } x\in\mathbb R\}$$
--   is relatively dense.
--
--   Every continuous periodic function (with a non-zero period) is almost periodic, while for instance $x\mapsto x$ is not. Bohr's theory of these functions (boundedness and uniform continuity, closure under sums, products and uniform limits, mean values, Bohr–Fourier series and Parseval's identity) is the classical model of self-approximation under translation. Masullo's §7.1.1 recalls it (for analytic functions on vertical strips) as the motivation for Bagchi's weaker notion of strong recurrence, which is what the paper actually uses.
--
--   **Formalization Note.** `AlmostPeriodic.IsRelativelyDense A` uses closed intervals $[a,a+L]$; `AlmostPeriodic.IsBohrAlmostPeriodic f` allows values in any `NormedAddCommGroup`. Whether one writes $\le\varepsilon$ or $<\varepsilon$ in the translation condition does not change the notion, since $\varepsilon>0$ is arbitrary.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 312–313, §7.1.1 (Almost periodic functions; the paper recalls Bohr's notion without stating the definition); classical reference: H. Bohr, Zur Theorie der fastperiodischen Funktionen I, II, III, Acta Math. 45 (1924), 46 (1925), 47 (1926) [Bohr1, Bohr2, Bohr3], and H. Bohr, Almost Periodic Functions, Chelsea Publishing Company, New York, 1947 [Bohr4] (dated 1933 in the paper's bibliography), cited by the paper in §7.1.1.

import Mathlib

/-!
# Bohr almost periodic functions on the real line

Relatively dense subsets of `ℝ` and (uniformly) almost periodic functions in the sense of
H. Bohr.

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), §7.1.1, p. 312
(almost periodic functions of H. Bohr, [Bohr1, Bohr2, Bohr3, Bohr4]).
-/

namespace AlmostPeriodic

/-- A subset `A ⊆ ℝ` is *relatively dense* if there is a length `L > 0` such that every closed
interval `[a, a + L]` contains a point of `A`. -/
def IsRelativelyDense (A : Set ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, (A ∩ Set.Icc a (a + L)).Nonempty

/-- A function `f : ℝ → E` with values in a normed additive group is *almost periodic in the
sense of Bohr* (uniformly almost periodic) if it is continuous and, for every `ε > 0`, its set
of `ε`-translation numbers `{τ ∈ ℝ | ∀ x, ‖f (x + τ) - f x‖ ≤ ε}` is relatively dense. -/
def IsBohrAlmostPeriodic {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) : Prop :=
  Continuous f ∧
    ∀ ε : ℝ, 0 < ε → IsRelativelyDense {τ : ℝ | ∀ x : ℝ, ‖f (x + τ) - f x‖ ≤ ε}

end AlmostPeriodic


