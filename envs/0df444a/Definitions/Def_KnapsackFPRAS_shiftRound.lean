-- Prove2me | Definitions.Def_KnapsackFPRAS_shiftRound
-- name    : KnapsackFPRAS_shiftRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:51.153655+00:00
-- url     : https://prove2.me/theorems/5042c8de-e267-4fce-8f3b-e83819a880ac
-- title:
--   Random-shift rounding $\alpha_s(s'j)=s\lfloor (j+H)/J\rfloor$
-- statement:
--   Let $s'>0$ be a spacing, $J\ge1$ an integer, and $s=Js'$ the coarser spacing. A value $x=s'j$ with $j\in\mathbb Z$ is rounded with a **shift** $H\in\{0,\dots,J-1\}$ to
--
--   $$
--   \alpha_s(s'j) := s\left\lfloor\frac{j+H}{J}\right\rfloor .
--   $$
--
--   When $H$ is uniform, $\alpha_s(x)$ takes the two neighbouring multiples of $s$ around $x$, with the probabilities that make it unbiased.
--
--   **Formalization Note** The arguments are $s'$, $J$, $H$ and the index $j$; the page's side conditions ($J$ a power of two, $s\le S$) are not part of the definition.
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), §4.6.3, Eq. (23), p.26 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Eq. (23)**, p.26. Random-shift rounding: a value `s′ j` (`j ∈ ℤ`) on spacing `s′` is
rounded to the spacing `s = J s′` with shift `H ∈ {0, …, J − 1}` by
`α_s(s′ j) := s ⌊(j + H) / J⌋`.

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), §4.6.3, Eq. (23), p.26 (PDF p.27).

**Formalization Note.** The value is given by its index `j` and the old spacing `s′`; the new
spacing is `s = J · s′`. The shift `H` is a natural number (the statements draw it from
`Fin J`), and the floor is the real floor of `(j + H)/J`. The page's side conditions (`J` a
power of two, `s ≤ S`) are not part of the definition. -/
noncomputable def shiftRound (s' : ℝ) (J H : ℕ) (j : ℤ) : ℝ :=
  (J : ℝ) * s' * ⌊((j : ℝ) + H) / J⌋
end KnapsackFPRAS


