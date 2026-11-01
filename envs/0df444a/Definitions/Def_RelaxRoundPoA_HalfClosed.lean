-- Prove2me | Definitions.Def_RelaxRoundPoA_HalfClosed
-- name    : RelaxRoundPoA_HalfClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:16.228518+00:00
-- url     : https://prove2.me/theorems/dc6834aa-8600-44d3-a4f6-c5021cd805b5
-- title:
--   Weight classes closed under halving
-- statement:
--   The weight classes $(\mathcal V_i)_{i\in N}$ are **closed under halving** if for every agent $i$
--
--   $$
--   w\in\mathcal V_i\ \Longrightarrow\ \tfrac12 w\in\mathcal V_i,
--   $$
--
--   where $\tfrac12 w$ is the function $x\mapsto w(x)/2$.
--
--   Lemma 1 and Theorem 3′ use the deviation "bid half your value", $b_i'=\tfrac12 v_i$, and pretend that agent $i$ has valuation $\tfrac12 v_i$; this closure makes both admissible. Every class of the paper's applications is closed under nonnegative scaling.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, pp.8–9 (Lemma 1, Theorem 3′)

import Mathlib

open NNReal

namespace RelaxRoundPoA

/-- **Weight classes closed under halving.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, pp.8–9: Lemma 1 and Theorem 3′ use the
deviation `b'_i = ½ v_i` and "pretend that each bidder `i` has valuation `½ v_i`", so `½ v_i` must
be an admissible bid and valuation whenever `v_i` is.

`HalfClosed Val` says that `w ∈ Val i` implies `x ↦ w(x)/2 ∈ Val i`, for every agent `i`.

**Formalization Note** The paper uses this closure without stating it; it holds for every class of
the paper's applications (all of them are closed under nonnegative scaling). -/
def HalfClosed {N : Type*} {Ω' : Type*} (Val : N → Set (Ω' → ℝ≥0)) : Prop :=
  ∀ i, ∀ w ∈ Val i, (fun x => w x / 2) ∈ Val i

end RelaxRoundPoA


