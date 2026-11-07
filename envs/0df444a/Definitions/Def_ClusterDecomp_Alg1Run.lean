-- Prove2me | Definitions.Def_ClusterDecomp_Alg1Run
-- name    : ClusterDecomp_Alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:33.483929+00:00
-- url     : https://prove2.me/theorems/6ce25943-e2ac-4c35-b7de-54c6424db797
-- title:
--   Algorithm 1 (Fair-Cut Trimming) and the auxiliary graph $H_A$
-- statement:
--   Given $A\subseteq V$ and parameters $\varepsilon,p$, set $\alpha=1+\varepsilon/16$ and $\beta=(1+\varepsilon/10)p$. The auxiliary graph $H_A$ has vertices $A\cup\{s,t\}$, capacity $w(u,v)$ on $u,v\in A$, capacity $w(v,V\setminus A)$ on $\{s,v\}$ and capacity $\beta\deg(v)$ on $\{v,t\}$. Algorithm 1 computes an $\alpha$-fair $s,t$-cut $(S,T)$ of $H_A$ and returns $B=T\setminus\{t\}$. The number of edges counted for $H_A$ is $|E(G[A])|+2|A|$.
--
--   This is the single fair-cut call that turns a low-conductance set into a backbone of high inner conductance.
--
--   **Formalization Note** The cut in line 10 is left free: `Alg1Run G A ε p B` holds for every $\alpha$-fair cut, so every lemma stated over it holds for whatever cut the black box returns. The vertices of $H_A$ are `↥A ⊕ Bool`.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Algorithm 1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ClusterDecomp_Conductance
import Definitions.Def_ClusterDecomp_IsFairCut

open Finset

namespace ClusterDecomp

/-!
# Algorithm 1 (Fair-Cut Trimming) as a relation

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Algorithm 1, p.9 (PDF p.11).

**Formalization Note.**
* The vertices of `H_A` are `↥A ⊕ Bool`, with `s = inr false` and `t = inr true`.
* `HAcap` has no `s`–`t` edge. Loops of `G` inside `A` are kept (lines 3–5 add every edge with both ends in `A`); they
  carry no flow and cross no cut.
* Line 10 "compute an α-fair cut" is free in the relation: `Alg1Run` holds for **every** `α`-fair cut, not only for a
  minimum cut, so a lemma stated over `Alg1Run` holds for whatever cut the black box returns.
* `α = 1 + ε/16` and `β = (1 + ε/10)p`, as printed on line 1.
-/

/-- The source `s` of `H_A`. -/
abbrev srcA {V : Type*} (A : Finset V) : ↥A ⊕ Bool := Sum.inr false

/-- The sink `t` of `H_A`. -/
abbrev snkA {V : Type*} (A : Finset V) : ↥A ⊕ Bool := Sum.inr true

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The capacities of the auxiliary graph `H_A` (Algorithm 1, lines 2–9): `w(u, v)` on `u, v ∈ A`, `w(v, V ∖ A)` on
`{s, v}`, `β·deg(v)` on `{v, t}`, and `0` otherwise. -/
def HAcap (G : WGraph V) (A : Finset V) (β : ℝ) : ↥A ⊕ Bool → ↥A ⊕ Bool → ℝ
  | .inl u, .inl v => G.w u v
  | .inr false, .inl v => G.cut {(v : V)} Aᶜ
  | .inl v, .inr false => G.cut {(v : V)} Aᶜ
  | .inl v, .inr true => β * G.deg v
  | .inr true, .inl v => β * G.deg v
  | .inr _, .inr _ => 0

/-- The backbone of a cut (line 11, `B ← T ∖ {t}`): the vertices of `A` on the sink side. -/
noncomputable def backboneOf (A : Finset V) (S : Finset (↥A ⊕ Bool)) : Finset V :=
  (A.attach.filter fun v => Sum.inl v ∉ S).map (Function.Embedding.subtype _)

/-- `B` is a possible output of Algorithm 1 on `A` with parameters `ε`, `p`: `B = T ∖ {t}` for some `α`-fair `s,t`-cut
of `H_A`, with `α = 1 + ε/16` and `β = (1 + ε/10)p`. -/
def Alg1Run (G : WGraph V) (A : Finset V) (ε p : ℝ) (B : Finset V) : Prop :=
  ∃ S : Finset (↥A ⊕ Bool),
    IsFairCut (HAcap G A ((1 + ε / 10) * p)) (srcA A) (snkA A) S (1 + ε / 16) ∧
      B = backboneOf A S

/-- `|E(H_A)|` as counted by Algorithm 1: the edges of `G[A]` (lines 3–5) and two edges per vertex of `A` (lines 6–9), zero
capacities included. -/
noncomputable def numEdgesHA (G : WGraph V) (A : Finset V) : ℕ :=
  (G.edgesIn A).card + 2 * A.card

end ClusterDecomp


