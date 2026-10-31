-- Prove2me | Definitions.Def_QKPSDP_IsRegularFOSP
-- name    : QKPSDP_IsRegularFOSP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:52.597431+00:00
-- url     : https://prove2.me/theorems/3317fe58-6ee8-46fb-94c1-2694afadefbb
-- title:
--   Regular first-order stationary points of (SQKELR)
-- statement:
--   $R$ is a **regular first-order stationary point** of (SQKELR) if $R \in \mathcal K_{n,r}$, $R$ is regular, and some $(\mu,\lambda) \in \mathbb R^n\times\mathbb R$ satisfy the KKT equation (32).
--
--   This is the hypothesis of Lemma 4.10.
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10, p.16; p.12; (32), p.14

import Mathlib
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_KKT1

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.10, p.16 ("`R` is a regular first order stationary
point of (SQKELR)"), with p.12 and (32), p.14: `R ∈ K_{n,r}`, `R` is regular (LICQ holds), and
some multipliers `(μ, λ) ∈ ℝⁿ × ℝ` satisfy the first-order KKT equation (32). -/
def IsRegularFOSP {n r : ℕ} [NeZero r] (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (τ : ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  R ∈ K a τ ∧ IsRegular a τ R ∧ ∃ (μ : Fin n → ℝ) (lam : ℝ), KKT1 C a τ R μ lam

end QKPSDP


