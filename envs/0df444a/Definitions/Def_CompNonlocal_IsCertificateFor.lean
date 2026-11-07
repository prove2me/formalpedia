-- Prove2me | Definitions.Def_CompNonlocal_IsCertificateFor
-- name    : CompNonlocal_IsCertificateFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:37.594502+00:00
-- url     : https://prove2.me/theorems/1252f545-afd7-4847-b07e-a47652b53ad4
-- title:
--   Single-copy certificate with gap $\gamma$
-- statement:
--   A game $G=(Q,A,B,\mathrm{Val})$ certifies the two-qubit state $\omega$ with single-copy gap $\gamma\in(0,1]$ if:
--
--   1. $Q,A,B,\mathrm{Val}$ are uniform QPT;
--   2. there are $c,s:\mathbb N\to[0,1]$ such that, for all sufficiently large $\kappa$, the honest players on $\omega$ are accepted with probability at least $c(\kappa)$ (completeness);
--   3. for every pair of polynomial-size families $A',B'$ and every family $\{\tau_\kappa\}$ of separable two-qubit states, for all sufficiently large $\kappa$ (onset depending on the strategy), the acceptance probability is at most $s(\kappa)$ (soundness);
--   4. $c(\kappa)-s(\kappa)>1/\mathrm{poly}(\kappa)$ eventually;
--   5. $c(\kappa)-s(\kappa)\ge\gamma-\mathsf{negl}(\kappa)$.
--
--   **Formalization Note** Separable states are finite convex combinations of products of qubit density matrices on the two qubits of the certified state (Reading 4).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definitions 10, 11, p.25

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_acc
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

set_option autoImplicit false

namespace CompNonlocal

/-- A single-copy certificate with gap `γ`. Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 10, p.25 with `k = 1` (Definition 11, p.25) and the γ-clause of Definition 11:

1. the four algorithms are uniform QPT;
2. there are `c, s : ℕ → [0, 1]` with completeness: for all sufficiently large `κ`, the honest
   players on the state `ω` are accepted with probability at least `c(κ)`;
3. soundness: "For every pair of quantum circuit families A′, B′ of polynomial size with classical
   advice of polynomial length, and every family of separable states {τ_AB}, for all sufficiently
   large κ, with the onset allowed to depend on the fixed strategy, … Pr[V accepts] ≤ s(κ)";
4. "γ(κ) := c(κ) − s(κ) … γ(κ) > 1/poly(κ) for all sufficiently large κ";
5. "For γ ∈ (0, 1], we say that ω_AB is γ-single-copy certifiable if c(κ) − s(κ) ≥ γ − negl(κ)".

**Formalization Note** Separable states are the published `QAlgorithms.Entanglement.IsSeparableDensity`
(finite convex combinations of products of density matrices) on the two qubits `C² ⊗ C²` of the
certified state (Reading 4). "1/poly" is `1 / (q(κ) + 1)` for some `q : Polynomial ℕ`. -/
def IsCertificateFor (c : Certificate) (ω : Matrix (Bool × Bool) (Bool × Bool) ℂ) (γ : ℝ) :
    Prop :=
  Uniform c.Qg ∧ Uniform c.A ∧ Uniform c.B ∧ Uniform c.Val ∧ 0 < γ ∧ γ ≤ 1 ∧
    ∃ cc s : ℕ → ℝ, (∀ κ, 0 ≤ cc κ ∧ cc κ ≤ 1) ∧ (∀ κ, 0 ≤ s κ ∧ s κ ≤ 1) ∧
      (∀ᶠ κ in Filter.atTop, cc κ ≤ c.acc κ c.A c.B ω) ∧
      (∀ A' B' : Family, PolySize A' → PolySize B' →
        ∀ τ : ℕ → Matrix (Bool × Bool) (Bool × Bool) ℂ,
          (∀ κ, QAlgorithms.Entanglement.IsSeparableDensity (τ κ)) →
          ∀ᶠ κ in Filter.atTop, c.acc κ A' B' (τ κ) ≤ s κ) ∧
      (∃ q : Polynomial ℕ, ∀ᶠ κ in Filter.atTop, 1 / ((q.eval κ : ℕ) + 1 : ℝ) < cc κ - s κ) ∧
      (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ, γ - μ κ ≤ cc κ - s κ)

end CompNonlocal


