-- Prove2me | Definitions.Def_ChoresEFX_IsAdmissibleMatching
-- name    : ChoresEFX_IsAdmissibleMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:20.578625+00:00
-- url     : https://prove2.me/theorems/0fe2007a-ebaf-4de3-82c3-8f900e11a037
-- title:
--   Sorted-Slot Rounding: sort orders, slots, shares and admissible matchings
-- statement:
--   Given shares $w\ge0$, agent $i$ has $\ell_i=\lceil\sum_g w_{ig}\rceil$ unit slots. Her chores are placed in an order that is nonincreasing in $q_g$, with chores of price $p_g>\beta$ first among those with $q_g=\beta$. The share of chore $g$ in slot $j$ is the length of $[W,W+w_{ig})\cap[j,j+1)$, where $W$ is the total share placed before $g$.
--
--   An **admissible matching** is an injective map $\pi$ from the chores to the slots such that:
--
--   1. the share of $g$ in $\pi(g)$ is positive;
--   2. every slot whose real mass is $1$ is in the image of $\pi$.
--
--   The rounded bundle $Y_i$ consists of the chores matched to slots of agent $i$.
--
--   This is the second stage of the algorithm. It turns a fractional allocation into an integral one.
--
--   **Formalization Note** The printed algorithm adds dummy chores and takes a perfect matching. The form above has no dummies. A perfect matching restricts to an admissible matching, because a full slot has no dummy share. Conversely, when dummies are spread over the slots with positive deficit, an admissible matching extends to a perfect matching. Hence the outputs are those over all dummy placements. `maxOn` is the maximum over a bundle and $0$ on the empty bundle.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §3.2 pp.9–10; Algorithm 3, p.10

import Mathlib
import Definitions.Def_ChoresEFX_IsCappedPriceStructure

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- **Sort orders of SSR**, §3.2, p.9 and Algorithm 3, line 3, p.10.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

For each agent, `o i` ranks the chores. A chore placed earlier has a capped price at least as large,
and "among chores with `q_g = β`, break ties by placing chores with `p_g > β` first".

**Formalization Note.** If `h` has `p_h > β` then `q_h = β`, so an earlier `g` has `q_g = β` too: the
second clause is exactly the printed tie rule. Other ties are free (paper.md decision 8). -/
def IsSortedOrder (β : ℝ) (p : κ → ℝ) (o : ι → κ → ℕ) : Prop :=
  (∀ i, Function.Injective (o i)) ∧
    ∀ i g h, o i g < o i h → capped β p h ≤ capped β p g ∧ (β < p h → β < p g)

/-- The number of slots of agent `i`, `ℓ_i = ⌈∑_g w_ig⌉`, Algorithm 3, line 2, p.10 (Qin et al., STOC
2027 submission). -/
noncomputable def numSlots (w : ι → κ → ℝ) (i : ι) : ℕ := ⌈∑ g, w i g⌉₊

open Classical in
/-- The total share `W` of agent `i` placed before chore `g` in her order, §3.2, p.9 (Qin et al., STOC
2027 submission). -/
noncomputable def shareBefore (w : ι → κ → ℝ) (o : ι → κ → ℕ) (i : ι) (g : κ) : ℝ :=
  ∑ h ∈ univ.filter (fun h => o i h < o i g), w i h

/-- **The share of chore `g` in slot `j` of agent `i`**: the length of
`[W, W + w_ig) ∩ [j, j + 1)`, Algorithm 3, line 3, p.10 (Qin et al., STOC 2027 submission). -/
noncomputable def slotMass (w : ι → κ → ℝ) (o : ι → κ → ℕ) (i : ι) (g : κ) (j : ℕ) : ℝ :=
  max 0 (min (shareBefore w o i g + w i g) ((j : ℝ) + 1) - max (shareBefore w o i g) (j : ℝ))

/-- The real mass of slot `j` of agent `i` (before the dummy chores of Algorithm 3, line 6, p.10; Qin et
al., STOC 2027 submission). -/
noncomputable def slotLoad (w : ι → κ → ℝ) (o : ι → κ → ℕ) (i : ι) (j : ℕ) : ℝ :=
  ∑ g, slotMass w o i g j

/-- **Admissible matchings**, Algorithm 3, lines 5–9, p.10 (Qin et al., STOC 2027 submission): an
injective map from the real chores to slots along positive shares, covering every slot whose real mass
is `1`.

**Formalization Note.** This is the dummy-free form of the perfect matching of the printed algorithm.
A perfect matching restricts to such a map, because a full slot has no dummy share. Conversely, if every
dummy is spread uniformly over the slots with positive deficit, such a map extends to a perfect matching
(paper.md decision 9). So the outputs are those over all dummy placements. -/
structure IsAdmissibleMatching (w : ι → κ → ℝ) (o : ι → κ → ℕ)
    (π : κ → Σ i, Fin (numSlots w i)) : Prop where
  injective : Function.Injective π
  positive : ∀ g, 0 < slotMass w o (π g).1 g (π g).2
  covers_full : ∀ (i : ι) (j : Fin (numSlots w i)), slotLoad w o i j = 1 → ∃ g, π g = ⟨i, j⟩

/-- **The rounded bundles** `Y_i`, Algorithm 3, line 9, p.10 (Qin et al., STOC 2027 submission): each
real chore goes to the agent owning its matched slot. -/
noncomputable def ssrBundle {w : ι → κ → ℝ} (π : κ → Σ i, Fin (numSlots w i)) (i : ι) : Finset κ :=
  univ.filter fun g => (π g).1 = i

/-- The largest value of `q` on a bundle, `max_{g ∈ S} q_g`, display (7), p.10 (Qin et al., STOC 2027
submission).

**Formalization Note.** A real `⨆` over a finite type, attained on a nonempty bundle; on the empty
bundle it is `0`, which makes (7) read `0 ≤ E_i` there. -/
noncomputable def maxOn (q : κ → ℝ) (S : Finset κ) : ℝ := ⨆ g : S, q g

end ChoresEFX


