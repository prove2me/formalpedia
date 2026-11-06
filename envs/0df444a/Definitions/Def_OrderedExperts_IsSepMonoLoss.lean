-- Prove2me | Definitions.Def_OrderedExperts_IsSepMonoLoss
-- name    : OrderedExperts_IsSepMonoLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:44.409663+00:00
-- url     : https://prove2.me/theorems/87f654fc-10d5-4cd5-8798-07cf7407f526
-- title:
--   A loss of the separated monotone problem
-- statement:
--   Let $(\mathcal A,\preceq)$ be a totally ordered action space with least element $\bot$ and greatest element $\top$. A pair $(\ell^\uparrow,\ell^\downarrow)$ of functions $\mathcal A\to\mathbb R$ is a **loss of the separated monotone problem** if
--   1. $\ell^\uparrow$ is nondecreasing, takes values in $[0,1/2]$, and $\ell^\uparrow(\bot)=0$;
--   2. $\ell^\downarrow$ is nonincreasing, takes values in $[0,1/2]$, and $\ell^\downarrow(\top)=0$.
--
--   The round's loss is $\ell(a)=\ell^\uparrow(a)+\ell^\downarrow(a)\in[0,1]$, and querying an action reveals both components separately.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.1, p.5

import Mathlib

namespace OrderedExperts

/-- **A loss of the separated monotone problem.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.1, p.5: "On each
round the adversary chooses a nondecreasing component `ℓ↑t : A → [0, 1/2]` with `ℓ↑t(⊥) = 0` and a
nonincreasing component `ℓ↓t : A → [0, 1/2]` with `ℓ↓t(⊤) = 0`, and the loss is their sum,
`ℓt(a) = ℓ↑t(a) + ℓ↓t(a)`."

`IsSepMonoLoss up down` says that `up` is nondecreasing with values in `[0, 1/2]` and `up ⊥ = 0`, and
`down` is nonincreasing with values in `[0, 1/2]` and `down ⊤ = 0`, on a totally ordered action space
with least element `⊥` and greatest element `⊤`. -/
def IsSepMonoLoss {A : Type*} [LinearOrder A] [BoundedOrder A] (up down : A → ℝ) : Prop :=
  Monotone up ∧ Antitone down ∧ (∀ x, 0 ≤ up x ∧ up x ≤ 1 / 2) ∧
    (∀ x, 0 ≤ down x ∧ down x ≤ 1 / 2) ∧ up ⊥ = 0 ∧ down ⊤ = 0

end OrderedExperts


