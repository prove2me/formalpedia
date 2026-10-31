-- Prove2me | Definitions.Def_FiniteMemPOMDP_IsRepresentative
-- name    : FiniteMemPOMDP_IsRepresentative
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:42.14583+00:00
-- url     : https://prove2.me/theorems/b0f0f155-86ae-4e7d-83ae-09bbaf89a0d2
-- title:
--   Representative histories $h^j$ of the occurring super-supports
-- statement:
--   The super-supports that occur with positive probability under $\mathbb P^{p^*}_\sigma$ are $\mathcal D^1,\dots,\mathcal D^J$, and for each $j$ a history $h^j$ is fixed with $\mathcal D^j=\mathcal B_{m_j}(h^j)$.
--
--   `IsRepresentative Γ p σ rep` says that the map `rep` makes such a choice: for every history $h$ with $\mathbb P^{p^*}_\sigma(H=h)>0$, the super-support after `rep (B(h))` equals $B(h)$.
--
--   **Formalization Note** The index $j$ is replaced by the super-support tuple itself; `rep` is unconstrained on tuples that do not occur.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §6.4, p.18

import Mathlib
import Definitions.Def_FiniteMemPOMDP_superSupp

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- **Representative histories `h^j` of the occurring super-supports.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §6.4, p.18: "Denote all different
super-supports that can occur with positive probability by D1, D2, . . . , DJ, i.e.
{D1, D2, . . . , DJ} := ∪_{m≥1} supp Bm. Moreover, since Dj corresponds to a super-support that
occurs at some stage and under some history, there exists hj and mj such that hj ∈ Hmj and
Dj = Bmj(hj)."

`IsRepresentative Γ p σ rep` says that `rep` assigns to every super-support `D` that occurs with
positive `P^p_σ`-probability a history `rep D` whose super-support is `D`: for every history `h`
with `P^p_σ(H = h) > 0`, the super-support after `rep (B(h))` is `B(h)`.

**Formalization Note** The paper enumerates the occurring super-supports as `D^1, …, D^J` and
fixes `h^j` for each; here the super-support tuple itself is the index and `rep` is the choice
`D^j ↦ h^j`. Values of `rep` on tuples that do not occur are unconstrained. -/
def IsRepresentative (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (rep : (ℝ → Set K) → List (A × S)) : Prop :=
  ∀ h : List (A × S), 0 < historyProb Γ p σ h →
    superSuppTuple Γ p σ (rep (superSuppTuple Γ p σ h)) = superSuppTuple Γ p σ h

end FiniteMemPOMDP


