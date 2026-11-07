-- Prove2me | Definitions.Def_ClawFreeChoosable_SatisfiesP
-- name    : ClawFreeChoosable_SatisfiesP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:38.609181+00:00
-- url     : https://prove2.me/theorems/16f1e7c9-e4cf-4a9c-bff4-ee07db6100d9
-- title:
--   The precolouring-extension property (Pk)
-- statement:
--   Let $G$ be a graph and $k$ a nonnegative integer.
--
--   A **(Pk)-instance** is a tuple $(G, S, \phi, L)$ where $S$ is a clique of simplicial vertices of $G$ (possibly empty), $\phi$ is a proper colouring of $G[S]$, and $L$ is a list assignment with $|L(v)| \ge k$ for every $v \notin S$. The instance is **colourable** if $G$ has a proper colouring $f$ with $f = \phi$ on $S$ and $f(v) \in L(v)$ for every $v \notin S$. The graph $G$ **satisfies (Pk)** if every (Pk)-instance on $G$ is colourable.
--
--   Theorem 1.3 says that every claw-free perfect graph satisfies (Pk) for every $k \ge \omega(G)$.
--
--   **Formalization Note** Colours range over an arbitrary type; $\phi$ and $L$ are maps on all of $V(G)$, of which only $\phi$ on $S$ and $L$ off $S$ are read. The paper defines (Pk) for $k \ge \omega(G)$ only; this condition is not built into the property but is a hypothesis of every theorem that uses it.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Definition 7.2, pp.9–10

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsSimplicialClique

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **(Pk)-instance** (arXiv:2611.01068v1, Definition 7.2, pp.9–10): `(G, S, ϕ, L)` where `S` is a
clique of simplicial vertices of `G` (possibly empty), `ϕ` is a proper colouring of `G[S]`, and
`L` is a list assignment with `|L(v)| ≥ k` for every `v ∉ S`.

**Formalization Note.** Colours range over an arbitrary type `α`. `ϕ` and `L` are total maps on
`V`; only `ϕ` on `S` and `L` off `S` are ever read. The paper's standing requirement
`k ≥ ω(G)` is not bundled here; each theorem states it as `G.cliqueNum ≤ k`. -/
def IsPInstance {V α : Type} (G : SimpleGraph V) (k : ℕ) (S : Set V) (ϕ : V → α)
    (L : V → Finset α) : Prop :=
  IsSimplicialClique G S ∧ (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → ϕ u ≠ ϕ v) ∧
    ∀ v, v ∉ S → k ≤ (L v).card

/-- A (Pk)-instance `(G, S, ϕ, L)` is **colorable** (Definition 7.2, p.10): `G` has a proper
colouring extending `ϕ` and using a colour from `L(v)` at every `v ∉ S`. -/
def PColorable {V α : Type} (G : SimpleGraph V) (S : Set V) (ϕ : V → α)
    (L : V → Finset α) : Prop :=
  ∃ f : V → α, (∀ u v, G.Adj u v → f u ≠ f v) ∧ (∀ s ∈ S, f s = ϕ s) ∧
    ∀ v, v ∉ S → f v ∈ L v

/-- `G` **satisfies (Pk)** (arXiv:2611.01068v1, Definition 7.2, p.10): every (Pk)-instance on `G`,
over every colour type, is colorable.

**Formalization Note.** The paper defines (Pk) for integers `k ≥ ω(G)`; that condition is a
separate hypothesis `G.cliqueNum ≤ k` of every theorem that uses the property. -/
def SatisfiesP {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (α : Type) (S : Set V) (ϕ : V → α) (L : V → Finset α),
    IsPInstance G k S ϕ L → PColorable G S ϕ L

end ClawFreeChoosable


