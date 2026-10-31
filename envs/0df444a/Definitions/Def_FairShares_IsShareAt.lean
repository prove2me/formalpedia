-- Prove2me | Definitions.Def_FairShares_IsShareAt
-- name    : FairShares_IsShareAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:36.692988+00:00
-- url     : https://prove2.me/theorems/f10f0096-8f54-4123-a3ca-d654c0a62202
-- title:
--   Share for a class of valuations (Definition 2), at fixed $m$ and $n$
-- statement:
--   Fix $m$ goods and $n$ agents. Let $D$ be a set of valuations on the bundles of $M=\{0,\dots,m-1\}$ and let $t$ assign a real number $t(v)$ to each valuation (the share $s(v,n)$ at this $n$). Then $t$ is a **share** on $D$ if:
--
--   1. **Realizability:** for every $v\in D$, $t(v)\le\max_{S\subseteq M} v(S)$;
--   2. **Name independence:** for every permutation $\sigma$ of $M$ and every $v\in D$ such that the renamed valuation $v^\sigma(S)=v(\sigma(S))$ also lies in $D$, $t(v^\sigma)=t(v)$.
--
--   Given a share, a bundle $S$ is **acceptable** for $v$ if $v(S)\ge t(v)$.
--
--   **Formalization Note** Realizability is written as "some bundle $S$ has $t(v)\le v(S)$", which is the same as $t(v)\le\max_S v(S)$ since there are finitely many bundles. Name independence is required only for renamings that stay in $D$, because a share is only constrained on the class.
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Definition 2, p.9

import Mathlib

namespace FairShares

/-- **Share for a class of valuations, at a fixed number of items and agents (Definition 2).**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Definition 2, p.9: "A share function (or simply share) s for a class of valuations C is a
function that outputs a real value s(v, n) when given two parameters: a valuation function
v ∈ C over a set of items M, and the number of agents n. It needs to satisfy two properties:
• Realizability: for every v ∈ C and n it holds that s(v, n) ≤ max_{S⊆M} v(S).
• Name independence: renaming the items does not change the value of the share."

For a set `D` of valuations on the bundles of `Fin m` and a function `t` (the share `s(·, n)` at
a fixed number `n` of agents), `IsShareAt D t` says:
1. realizability: for every `v ∈ D` some bundle `S` has `t v ≤ v S`, i.e. `t v ≤ max_S v(S)`;
2. name independence: for every permutation `σ` of the items and every `v ∈ D` whose renaming
   `S ↦ v (σ S)` also lies in `D`, the share of the renamed valuation equals that of `v`.

**Formalization Note.** "`t v ≤ v S` for some `S`" is `t v ≤ max_{S ⊆ M} v(S)` because there are
finitely many bundles. Renamings of `Fin m` are the permutations `Equiv.Perm (Fin m)`; the share
is only constrained on valuations in the class, so name independence is required only when the
renamed valuation is again in `D`. -/
def IsShareAt {m : ℕ} (D : Set (Finset (Fin m) → ℝ)) (t : (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  (∀ v ∈ D, ∃ S : Finset (Fin m), t v ≤ v S) ∧
  ∀ σ : Equiv.Perm (Fin m), ∀ v ∈ D, (fun S => v (S.map σ.toEmbedding)) ∈ D →
    t (fun S => v (S.map σ.toEmbedding)) = t v

end FairShares


