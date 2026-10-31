-- Prove2me | Definitions.Def_FuchsThesis_Types_probEvent
-- name    : FuchsThesis_Types_probEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:03.898065+00:00
-- url     : https://prove2.me/theorems/53356867-eed0-4823-9b67-0366e6be790f
-- title:
--   Probability $P(E)$ of a set of outcome strings
-- statement:
--   An experiment with single-trial distribution $p_0$ is repeated $n$ times independently, so a string $\vec b\in\mathcal B^n$ has probability $P(\vec b)=\prod_i p_0(b_i)$. An event is a set $E$ of outcome strings, and its probability is
--
--   $$
--   P(E)=\sum_{\vec b\in E}P(\vec b)=\sum_{\vec b\in E}\prod_{i=1}^{n}p_0(b_i).
--   $$
--
--   The event of interest is a type class $T(p_1)$, the set of strings whose empirical frequency distribution is $p_1$.
--
--   **Formalization Note** The space of strings is finite, so an event is a `Finset`. The dependence on $p_0$, implicit in the source's $P(E)$, is an explicit argument. The product is the published `HolevoCQ.wordProb`.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.2, p.25; eq. (2.82), p.26

import Mathlib
import Definitions.Def_HolevoCQ_wordProb

set_option autoImplicit false

open HolevoCQ

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.3.2, p.25 (PDF 34), and the first line of (2.82), p.26 (PDF 35): the
probability `P(E)` of an event `E`, a set of outcome strings, is the sum of the string probabilities
`P(⃗b) = ∏ᵢ p0(bᵢ)` (`wordProb`) over `⃗b ∈ E`.

**Formalization Note.** Strings are functions `Fin n → β`, and the source's repeated trials are
independent, as (2.82) shows; that is the product `wordProb`. The space of strings `Bⁿ` is finite,
so an event is a `Finset`. The source
calls this `P(E)`; `P(T(p1))` is `probEvent p0 (typeClass p1)`, with the dependence on `p0` explicit. -/
def probEvent {β : Type} {n : ℕ} (p0 : β → ℝ) (E : Finset (Fin n → β)) : ℝ :=
  ∑ s ∈ E, wordProb p0 n s

end FuchsThesis.Types


