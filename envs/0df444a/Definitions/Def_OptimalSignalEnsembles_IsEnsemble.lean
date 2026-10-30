-- Prove2me | Definitions.Def_OptimalSignalEnsembles_IsEnsemble
-- name    : OptimalSignalEnsembles_IsEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:59.61634+00:00
-- url     : https://prove2.me/theorems/384cf972-da68-48cf-addb-543c5c598d45
-- title:
--   Finite ensemble of $A$-states
-- statement:
--   Let $A \subseteq M_d(\mathbb C)$ be a set of matrices (in the paper, the set of **available states**). A pair $(p,\rho)$ with $p = (p_1,\dots,p_n)$ and $\rho = (\rho_1,\dots,\rho_n)$ is a **finite ensemble of $A$-states** if
--
--   1. $p_k \ge 0$ for every $k$,
--   2. $\sum_{k=1}^n p_k = 1$, and
--   3. $\rho_k \in A$ for every $k$.
--
--   This is the signal ensemble of the paper: the sender prepares $\rho_k$ with probability $p_k$, choosing the signal states from the available set $A$ (for a noisy channel, the set of its possible outputs).
--
--   **Formalization Note** Ensembles are indexed by $\mathrm{Fin}\,n$ for some $n \in \mathbb N$, which covers every finite index set. Zero weights are allowed. Taking $A$ to be the set of all density matrices gives an arbitrary finite ensemble of density matrices.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 1, p.1 and Sec. 2, p.3

import Mathlib

namespace OptimalSignalEnsembles

/-- `IsEnsemble A p ρ`: `(p, ρ)` is a **finite ensemble of `A`-states** — the weights are a
probability vector (`pₖ ≥ 0`, `∑ₖ pₖ = 1`) and every member `ρₖ` lies in the set `A`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 1, p.1
("Alice prepares the system in the signal state ρ_k with probability p_k") and Sec. 2, p.3
("an ensemble of signal states in the available set A").

**Formalization Note.** Ensembles are indexed by `Fin n` for some `n : ℕ`; this covers every
finite index set. Zero weights are allowed (a member with `pₖ = 0` plays no role). With
`A = {σ | IsDensityMatrix σ}` this is an arbitrary finite ensemble of density matrices. -/
def IsEnsemble {d : Type} {n : ℕ} (A : Set (Matrix d d ℂ)) (p : Fin n → ℝ)
    (ρ : Fin n → Matrix d d ℂ) : Prop :=
  (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧ ∀ k, ρ k ∈ A

end OptimalSignalEnsembles


