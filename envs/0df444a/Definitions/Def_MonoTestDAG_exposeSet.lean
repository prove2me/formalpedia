-- Prove2me | Definitions.Def_MonoTestDAG_exposeSet
-- name    : MonoTestDAG_exposeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:42.96727+00:00
-- url     : https://prove2.me/theorems/9281c78d-b207-408f-b79d-3ee6b01a9251
-- title:
--   Definition 5.1: matching exposure
-- statement:
--   Let $M=(M_1,\dots,M_s)$ be matchings in a bipartite graph $U=(L,R;E)$. For $Q\subseteq L\cup R$ put $E(Q):=E\cap((Q\cap L)\times(Q\cap R))$ and $\mathrm{Expose}(Q):=\{i\in[s]:E(Q)\cap M_i\ne\emptyset\}$. The witness $M$ has **$(q_0,\rho)$-bounded matching exposure** if $|\mathrm{Expose}(Q)|\le\rho s$ for every $Q$ with $|Q|\le q_0$.
--
--   **Formalization Note.** The matchings lie in $E$, so $E(Q)\cap M_i\ne\emptyset$ says that some edge of $M_i$ has both endpoints in $Q$. That $M$ is a PMRS witness is stated separately wherever this predicate is used. The condition $\rho>0$ is part of the predicate. The module also defines `HasBoundedExposure`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §5.1 and Definition 5.1, p.24

import Mathlib

namespace MonoTestDAG

open Classical in
/-- `Expose(Q) := {i ∈ [s] : E(Q) ∩ M_i ≠ ∅}` with `E(Q) := E ∩ ((Q ∩ L) × (Q ∩ R))`: the indices
of the matchings having an edge with both endpoints in the query set `Q ⊆ L ∪ R`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §5.1, p.24.

**Formalization Note.** The matchings `M_i` are subsets of `E`, so `E(Q) ∩ M_i ≠ ∅` is "some edge
of `M_i` has both endpoints in `Q`". -/
noncomputable def exposeSet {L R : Type} {s : ℕ} (M : Fin s → Finset (L × R))
    (Q : Finset (L ⊕ R)) : Finset (Fin s) :=
  Finset.univ.filter (fun i => ∃ e ∈ M i, (Sum.inl e.1 : L ⊕ R) ∈ Q ∧ (Sum.inr e.2 : L ⊕ R) ∈ Q)

/-- **Definition 5.1 (bounded matching exposure).** For `q₀ ∈ ℕ` and `ρ > 0`, the witness
`M = (M_1, …, M_s)` has `(q₀, ρ)`-bounded matching exposure if every `Q ⊆ L ∪ R` with `|Q| ≤ q₀`
has `|Expose(Q)| ≤ ρ s`.

Yoshida, arXiv:2602.15341 (sha256 454609db…), Definition 5.1, p.24.

**Formalization Note.** `ρ > 0` is part of the predicate. That `M` is an `(s, η)`-PMRS witness is
stated separately (`IsPMRSWitness`) wherever the paper uses this definition. -/
def HasBoundedExposure {L R : Type} {s : ℕ} (M : Fin s → Finset (L × R)) (q₀ : ℕ) (ρ : ℝ) :
    Prop :=
  0 < ρ ∧ ∀ Q : Finset (L ⊕ R), Q.card ≤ q₀ → ((exposeSet M Q).card : ℝ) ≤ ρ * (s : ℝ)

end MonoTestDAG


