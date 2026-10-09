-- Prove2me | Definitions.Def_CustAssort_AugGreedy_SubmodularOn
-- name    : CustAssort_AugGreedy_SubmodularOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:41.257003+00:00
-- url     : https://prove2.me/theorems/e1a601e5-29c1-4677-b203-9869809a77a5
-- title:
--   Footnote 1, p. 9 — submodularity on a finite ground set
-- statement:
--   A real-valued set function $g$ is submodular on a finite ground set $\Omega$ when its marginal gain from adding an element cannot increase as the chosen set grows. Concretely, for $A\subseteq B\subseteq\Omega$ and $i\in\Omega\setminus B$,
--
--   $$
--   g(A\cup\{i\})-g(A)\ge g(B\cup\{i\})-g(B).
--   $$
--
--   This is the paper's local, diminishing-marginal definition. It applies to functions that may fail to be submodular outside $\Omega$.
--
--   **Formalization Note** The Lean predicate is polymorphic over the element type and reverses the two sides of the displayed inequality without changing its meaning.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), §4, footnote 1, p. 9

import Mathlib

namespace CustAssort.AugGreedy

/-- The marginal definition of submodularity on a finite ground set (footnote 1, p. 9). -/
def SubmodularOn {α : Type*} [DecidableEq α] (g : Finset α → ℝ) (Ω : Finset α) : Prop :=
  ∀ A B : Finset α, A ⊆ B → B ⊆ Ω → ∀ i ∈ Ω \ B,
    g (insert i B) - g B ≤ g (insert i A) - g A

end CustAssort.AugGreedy


