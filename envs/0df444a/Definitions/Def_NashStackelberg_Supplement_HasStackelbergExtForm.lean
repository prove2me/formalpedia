-- Prove2me | Definitions.Def_NashStackelberg_Supplement_HasStackelbergExtForm
-- name    : NashStackelberg_Supplement_HasStackelbergExtForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:32:10.280067+00:00
-- url     : https://prove2.me/theorems/42945a43-8dac-582d-bbb6-658efd4c97ef
-- title:
--   Extended formulation as a Stackelberg feasible region
-- statement:
--   A set $S\subseteq\mathbb R^m$ has an **extended formulation as a Stackelberg feasible region** if there are $p\ge0$ additional leader variables $u\in\mathbb R^p$, a single follower solving a linear program with a simple parameterization in the leader's variables $(s,u)$,
--   $$
--   \mathrm{SOL}(s,u)=\operatorname*{arg\,min}_{y}\Big\{(c+H(s,u))^\top y\ :\ A(s,u)+By\le b\Big\},
--   $$
--   and leader constraints $A_L(s,u)+B_Ly\le b_L$ such that
--   $$
--   S=\big\{s\in\mathbb R^m:\ \exists\,u,\,y\ \text{ with }\ A_L(s,u)+B_Ly\le b_L\ \text{ and }\ y\in\mathrm{SOL}(s,u)\big\}.
--   $$
--   That is, $S$ is the projection onto $s$ of the feasible region $\{(w,y):(w,y)\in\mathcal S,\ y\in\mathrm{SOL}(P(w))\}$ of a simple Stackelberg game with one LP follower; the lifted variables $u$ and $y$ are projected out, and the leader's objective plays no role.
--
--   This is the notion of Lemmas 1 and 2, which build the feasible regions of the trivial NASP of the hardness proof of Theorem 2.
--
--   **Formalization Note** The follower is the published `FollowerGame` with $K=1$ and $Q=0$, and $\mathrm{SOL}$ is the published `FollowerGame.SOL` (any optimal solution; optimistic convention). The leader vector is $s$ followed by $u$.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, EC §9.1, Lemmas 1–2 and their proofs, pp.30–31; Definition 3, p.7; Definition 8, p.30

import Mathlib
import Definitions.Def_NashStackelberg_FollowerGame_SOL

open Matrix

namespace NashStackelberg.Supplement

/-- **Extended formulation as a (simple) Stackelberg feasible region** (Carvalho, Dragotto,
Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, EC §9.1,
Lemmas 1–2 and their proofs, pp.30–31; Definition 3, p.7; Definition 8, p.30).

A set `S ⊆ ℝᵐ` has an extended formulation as a Stackelberg feasible region if there are `p`
extra leader variables `u`, one follower solving a linear program with a simple parameterization
in the leader's variables `(s, u)` (published `FollowerGame` with `K = 1` follower and `Q = 0`:
`min (c + H(s, u))ᵀ y  s.t.  A(s, u) + B y ≤ b`), and leader constraints
`AL (s, u) + BL y ≤ bL` on the joint vector, such that
`S = {s : ∃ u y, AL (s, u) + BL y ≤ bL and y ∈ SOL(P(s, u))}`,
i.e. `S` is the projection onto `s` of the feasible region
`{(w, y) : (w, y) ∈ 𝓢, y ∈ SOL(P(w))}` of a simple Stackelberg game with a single LP follower
(the leader's objective plays no role). `SOL(P(w))` is the follower's optimal set (published
`FollowerGame.SOL`; optimistic convention).

**Formalization Note.** The leader vector is `Fin.append s u : Fin (m + p) → ℝ`, `s` first.
The follower's vector is the published `(k : Fin G.K) → Fin (G.d k) → ℝ`; with `G.K = 1` the sum
`∑ k, BL k *ᵥ y k` is the single term `BL y`. The followers' cross-coupling `C` of `G` is never
used when `K = 1`. This is the form of the proofs of Lemma 1 ((7a)–(7b)) and Lemma 2
(`{(w, y) : A w + B y ≤ b, y ∈ argmin{fᵀ y : C w + D y ≤ g}}`), with the follower's objective
allowed the simple parameterization `(H w)ᵀ y` of Definition 8. -/
def HasStackelbergExtForm {m : ℕ} (S : Set (Fin m → ℝ)) : Prop :=
  ∃ (p : ℕ) (G : FollowerGame (m + p)), G.K = 1 ∧ (∀ k, G.Q k = 0) ∧
    ∃ (rL : ℕ) (AL : Matrix (Fin rL) (Fin (m + p)) ℝ)
      (BL : (k : Fin G.K) → Matrix (Fin rL) (Fin (G.d k)) ℝ) (bL : Fin rL → ℝ),
      S = {s | ∃ (u : Fin p → ℝ) (y : (k : Fin G.K) → Fin (G.d k) → ℝ),
        AL *ᵥ Fin.append s u + ∑ k, BL k *ᵥ y k ≤ bL ∧ y ∈ G.SOL (Fin.append s u)}

end NashStackelberg.Supplement


