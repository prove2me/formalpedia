-- Prove2me | Definitions.Def_LocalBreadth_Supplement_betaH
-- name    : LocalBreadth_Supplement_betaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:18:59.411853+00:00
-- url     : https://prove2.me/theorems/e26d5f39-2a9a-47a2-9c55-d42f1d71ace0
-- title:
--   Guaranteed densities $\beta_{G,h}(L)$ and $\beta_h(L)$
-- statement:
--   For a generator $G$, a threshold $h$ and a language $L$, $\beta_{G,h}(L)$ is the largest $\alpha\in[0,1]$ such that $G$ guarantees $\delta_h(O,L)\ge\alpha$ on every full enumeration of $L$ when $L$ is the target; equivalently
--   $$\beta_{G,h}(L)=\inf_{x\text{ full enumeration of }L}\delta_h(O_x,L).$$
--   The per-language optimum is
--   $$\beta_h(L)=\sup_G\beta_{G,h}(L),$$
--   the supremum over generators that are (fresh and) eventually valid on the entire candidate family $\mathcal X$.
--
--   These quantities compare what one generator achieves at $L$ with the best achievable at $L$ alone; §6 shows that the per-language optima need not be attained simultaneously in dimension $d\ge2$.
--
--   **Formalization Note** Since $\delta_h\in[0,1]$, the infimum over full enumerations is the largest admissible $\alpha$. Following the paper's global convention, the generators in $\beta_h$ are fresh and universally eventually valid on $\mathcal X$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §6, p.42

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_GeneratorP
import Definitions.Def_LocalBreadth_Supplement_deltaH

namespace LocalBreadth.Supplement

variable {P : Type} [Preorder P]

/-- `β_{G,h}(L)`, §6, p.42: the largest `α ∈ [0, 1]` such that `G` guarantees `δ_h(O, L) ≥ α` on every
full enumeration of `L`. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…).

**Formalization Note.** Written as the infimum of `δ_h(O, L)` over full enumerations of `L`. Since
`δ_h ∈ [0, 1]`, this infimum lies in `[0, 1]` and is the largest admissible `α` (the set of such `α` is
`[0, inf]`). Every infinite countable `L` has a full enumeration, so the index is nonempty. -/
noncomputable def betaG (h : ℕ → ℝ) (G : GeneratorP P) (L : Set P) : ℝ :=
  ⨅ x : {x : ℕ → P // IsFullEnumerationP L x}, deltaH h (outputSetP G x.1) L

/-- `β_h(L) = sup_G β_{G,h}(L)`, §6, p.42, the supremum over generators eventually valid on the entire
family `X`.

**Formalization Note.** "Eventually valid" carries the paper's global freshness convention (p.13,
p.51): the supremum is over fresh, universally eventually valid generators on `X`. Values lie in
`[0, 1]`, so the real supremum is genuine whenever such a generator exists. -/
noncomputable def betaH (h : ℕ → ℝ) (X : Set (Set P)) (L : Set P) : ℝ :=
  ⨆ G : {G : GeneratorP P // IsFreshP X G ∧ IsEventuallyValidP X G}, betaG h G.1 L

end LocalBreadth.Supplement


