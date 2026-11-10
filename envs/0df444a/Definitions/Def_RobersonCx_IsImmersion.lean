-- Prove2me | Definitions.Def_RobersonCx_IsImmersion
-- name    : RobersonCx_IsImmersion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:33.433858+00:00
-- url     : https://prove2.me/theorems/5348b3d8-95ab-42ad-8ce2-9e527601310b
-- title:
--   Weak immersion $H\preccurlyeq_{\mathrm{imm}}G$
-- statement:
--   Let $H$ and $G$ be graphs. An **immersion model** of $H$ in $G$ is an injective map $\iota:V(H)\to V(G)$ together with a path $P_e$ in $G$ for each edge $e=hh'\in E(H)$ such that
--
--   1. the endpoints of $P_e$ are $\iota(h)$ and $\iota(h')$;
--   2. $E(P_e)\cap E(P_{e'})=\emptyset$ whenever $e\neq e'$.
--
--   $H$ **immerses** in $G$, written $H\preccurlyeq_{\mathrm{imm}}G$, if such a model exists. The paths may share internal vertices and may pass through other branch vertices $\iota(V(H))$: this is the **weak** immersion relation.
--
--   Immersion is the containment relation of the immersion analogue of the Strong Roberson Conjecture; $\mathrm{Forb}_{\mathrm{imm}}(H)$ is built from it.
--
--   **Formalization Note** The paths are indexed by ordered adjacent pairs $(a,b)$ (`P a b h : G.Walk (ι a) (ι b)` with `IsPath`), and edge-disjointness is required only between the paths of different edges $\{a,b\}\neq\{a',b'\}$; choosing one orientation per edge gives the paper's model and conversely, so the relation is the same.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §2.2, Definition 3, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `IsImmersion H G`: `H` immerses in `G`, `H ≼_imm G` (Definition 3, p.6 (PDF p.8)). An immersion model
is an injective map `ι : V(H) → V(G)` together with, for each edge `e = hh′ ∈ E(H)`, a path `P_e` in `G` with
endpoints `ι(h)` and `ι(h′)`, such that `E(P_e) ∩ E(P_e′) = ∅` whenever `e ≠ e′`. This is the *weak*
immersion relation: the paths may share internal vertices and may pass through other branch vertices (p.6).

**Formalization Note** The paths are indexed by ordered adjacent pairs `(a, b)`, `P a b : G.Walk (ι a) (ι b)`
with `IsPath`; edge-disjointness is required between the paths of *different* edges `s(a, b) ≠ s(a′, b′)`
only. Choosing one orientation of each edge turns such a family into the paper's model, and orienting the
paper's paths both ways (reversing one) gives such a family, so the two notions coincide. -/
def IsImmersion {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ (ι : W → V) (P : ∀ a b : W, H.Adj a b → G.Walk (ι a) (ι b)),
    Function.Injective ι ∧
    (∀ (a b : W) (h : H.Adj a b), (P a b h).IsPath) ∧
    (∀ (a b : W) (h : H.Adj a b) (a' b' : W) (h' : H.Adj a' b'), s(a, b) ≠ s(a', b') →
      (P a b h).edges.Disjoint (P a' b' h').edges)

end RobersonCx


