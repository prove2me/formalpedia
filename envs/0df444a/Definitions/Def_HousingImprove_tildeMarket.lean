-- Prove2me | Definitions.Def_HousingImprove_tildeMarket
-- name    : HousingImprove_tildeMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:56.457759+00:00
-- url     : https://prove2.me/theorems/99714169-8838-4475-8e48-66f96ffcd8f6
-- title:
--   The modified market $\widetilde H$
-- statement:
--   Let $X$ be an allocation and $H'$ a housing market, let $p$ be an agent, and let $Q$ be a set of agents $a\neq p$ that, in $H'$, prefer $p$'s house to the one they obtain in $X$ ($X(a)\prec'_a p$). For a $p$-improvement $H'$ of $H$, the admissible $Q$ (`IsQChoice`) are those containing every such agent whose preferences changed: these are the sets $\{q_i: X(q_i)\prec'_{q_i}p\}$ of p.11 for the series $q_1,\dots,q_k$, Algorithm 1's $\{a: \prec_a\neq\prec'_a,\ X(a)\prec'_a p\}$ being the smallest and $\{a\neq p: X(a)\prec'_a p\}$ (`Qset`) the largest. The market $\widetilde H$ has the agent set $\widetilde N=N\cup\widetilde Q$, where $\widetilde Q=\{\tilde q:q\in Q\}$ consists of one new agent per $q\in Q$, and the following preferences:
--
--   1. an agent $a\in N\setminus Q$ has the preferences of $H'$;
--   2. an agent $q\in Q$ has the preferences of $H'$ with $\tilde q$ taking the place of $p$ (so $p$ itself becomes unacceptable to $q$);
--   3. a new agent $\tilde q$ prefers only the house of $p$ to her own.
--
--   Equivalently, the acceptability graph $\widetilde G$ of $\widetilde H$ is that of $H'$ with every arc $(q,p)$, $q\in Q$, subdivided into $(q,\tilde q)$ and $(\tilde q,p)$. Algorithm HM-Improve works on sub-allocations of $\widetilde H$.
--
--   **Formalization Note** $\widetilde N$ is `N ⊕ {q // q ∈ Q}`. Houses unacceptable to an agent are placed below all acceptable ones and are mutually incomparable (the order of $H'$ among unacceptable houses is not kept); no statement of the mission compares two unacceptable houses. Every statement about HM-Improve is made for every admissible $Q$; the program `hmImproveProg` uses `Qset`.
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, p.11 (the set Q) and p.12 (the market H̃, its acceptability graph G̃)

import Mathlib
import Definitions.Def_HousingImprove_Market

namespace HousingImprove

universe u

variable {N : Type u}

/-- The set `Q` of agents that, in `H'`, prefer `p`'s house to the one they obtain in `X`
(Schlotter, Biró, Fleiner, arXiv:2110.06875v3, p.11 and Algorithm 1, line 2:
"`Q = {q_i : X(q_i) ≺'_{q_i} p, 1 ≤ i ≤ k}`").

This is the largest admissible `Q` (`IsQChoice`): the one for the series `q₁, …, q_k` listing every
agent other than `p` (an agent whose preferences did not change undergoes a trivial
`(p, q)`-improvement). The program `hmImproveProg` uses it. -/
def Qset (H' : Market N) (X : Equiv.Perm N) (p : N) : Set N :=
  {a | a ≠ p ∧ H'.lt a (X a) p}

/-- The admissible choices of the set `Q` (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, p.11:
"Let `q₁, …, q_k` denote the agents for which `H'` can be obtained from `H` by a series of
`(p, q_i)`-improvements … Let `Q` denote that set of only those agents among `q₁, …, q_k` that in `H'`
prefer `p`'s house to the one they obtain in allocation `X`"; Algorithm 1, line 2:
"`Q = {a ∈ N : ≺_a ≠ ≺'_a and X(a) ≺'_a p}`").

**Formalization Note.** A series `q₁, …, q_k` must contain every agent whose preferences changed,
and may contain any other agent `≠ p` (an unchanged agent undergoes a trivial
`(p, q)`-improvement). So the sets `Q` the page allows are exactly those between the agents with
changed preferences in `Qset` (Algorithm 1, line 2) and `Qset` itself. Every statement about
HM-Improve is made for every such `Q`. -/
def IsQChoice (H H' : Market N) (X : Equiv.Perm N) (p : N) (Q : Set N) : Prop :=
  (∀ a, a ≠ p → H'.lt a ≠ H.lt a → H'.lt a (X a) p → a ∈ Q) ∧ Q ⊆ Qset H' X p

/-- The agent set `Ñ = N ∪ Q̃` of `H̃` (p.12): the agents of `N` (`inl a`) and one new agent `q̃`
(`inr ⟨q, _⟩`) for each `q ∈ Q`. -/
abbrev Tilde (Q : Set N) : Type u :=
  N ⊕ {q : N // q ∈ Q}

/-- The house of `N` whose place an agent of `Ñ` takes: `a ↦ a` for `a ∈ N`, and `q̃ ↦ p`. -/
def tildeIota (p : N) {Q : Set N} : Tilde Q → N
  | .inl a => a
  | .inr _ => p

/-- Acceptability in `H̃` (p.12): for `a ∈ N` the `H'`-acceptable houses, except that for `q ∈ Q`
the new agent `q̃` takes the place of `p`; for `q̃` its own house and `p`'s. -/
def tildeAcc (H' : Market N) (p : N) (Q : Set N) :
    Tilde Q → Tilde Q → Prop
  | .inl a, .inl b => H'.Acceptable a b ∧ ¬ (a ∈ Q ∧ b = p)
  | .inl a, .inr q => q.1 = a
  | .inr _, .inl b => b = p
  | .inr q, .inr q' => q = q'

/-- The order of agent `c` of `H̃` among the houses acceptable to `c`. -/
def tildeRel (H' : Market N) (p : N) (Q : Set N) :
    Tilde Q → Tilde Q → Tilde Q → Prop
  | .inl a, x, y => H'.lt a (tildeIota p x) (tildeIota p y)
  | .inr q, x, y => x = .inr q ∧ y = .inl p

/-- The market **`H̃`** (arXiv:2110.06875v3, p.12), for a set `Q` of agents (`IsQChoice`): "for each
`q ∈ Q`, it adds a new agent `q̃` to `H'`, with `q̃` taking the place of `p` in the preferences of `q`;
the only house that agent `q̃` prefers to her own will be the house of `p` (the preferences of `p`
remain unchanged)."

`x ≺̃_c y` holds if both are acceptable to `c` and `c` ranks them so (for `a ∈ N` as in `H'`, with
`q̃` read as `p`; for `q̃`, `q̃ ≺ p`), or if `x` is unacceptable and `y` acceptable.

**Formalization Note.** The acceptability graph `G̃` is that of `H'` with each arc `(q, p)`,
`q ∈ Q`, subdivided into `(q, q̃)` and `(q̃, p)`. Houses unacceptable to an agent are placed below
all acceptable ones and are mutually incomparable: the order of `H'` among houses unacceptable to an
agent is not kept. No statement of the mission compares two unacceptable houses. -/
def tildeMarket (H' : Market N) (p : N) (Q : Set N) : Market (Tilde Q) where
  lt c x y :=
    (tildeAcc H' p Q c x ∧ tildeAcc H' p Q c y ∧ tildeRel H' p Q c x y) ∨
    (¬ tildeAcc H' p Q c x ∧ tildeAcc H' p Q c y)
  isStrictOrder c := by
    have hirr : ∀ x, ¬ tildeRel H' p Q c x x := by
      intro x
      cases c with
      | inl a => exact (H'.isStrictOrder a).irrefl _
      | inr q => rintro ⟨rfl, h⟩; cases h
    have htr : ∀ x y z, tildeRel H' p Q c x y → tildeRel H' p Q c y z → tildeRel H' p Q c x z := by
      intro x y z h₁ h₂
      cases c with
      | inl a => exact (H'.isStrictOrder a).trans _ _ _ h₁ h₂
      | inr q => obtain ⟨_, rfl⟩ := h₁; obtain ⟨h, _⟩ := h₂; cases h
    exact
      { irrefl := fun x h => by
          rcases h with ⟨_, _, h⟩ | ⟨h₁, h₂⟩
          · exact hirr x h
          · exact h₁ h₂
        trans := fun x y z h₁ h₂ => by
          rcases h₁ with ⟨hx, hy, h₁⟩ | ⟨hx, hy⟩ <;> rcases h₂ with ⟨_, hz, h₂⟩ | ⟨hy', hz⟩
          · exact Or.inl ⟨hx, hz, htr _ _ _ h₁ h₂⟩
          · exact absurd hy hy'
          · exact Or.inr ⟨hx, hz⟩
          · exact absurd hy hy' }

end HousingImprove


