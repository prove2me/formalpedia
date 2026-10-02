-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp
-- name    : TeschlODE_SturmLiouville_IsCompactOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:20:18.802216+00:00
-- url     : https://prove2.me/theorems/9ca21745-a91e-416d-a22e-e90d0588dfda
-- title:
--   Compact linear operator on an inner product space
-- statement:
--   Let $H_0$ be a complex inner product space (not necessarily complete) and $A : H_0 \to H_0$ a linear operator defined on all of $H_0$. The operator is **compact** if for every bounded sequence $(f_n)$ in $H_0$ the sequence $(A f_n)$ has a subsequence that converges in $H_0$.
--
--   The limit is required to be an element of $H_0$ itself, not of its completion. Every compact operator in this sense is bounded (Problem 5.9).
--
--   **Formalization Note.** "Bounded" is `Bornology.IsBounded (Set.range f)` for the norm of the inner product space; a subsequence is `f ∘ φ` with `φ` strictly increasing.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 150, §5.2

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 150: a linear operator `A` defined on all of the inner product space `H₀`
is *compact* if every sequence `A fₙ` has a convergent subsequence whenever `fₙ` is bounded.
The limit is required to lie in `H₀` itself (`H₀` is not assumed complete). -/
def IsCompactOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) : Prop :=
  ∀ f : ℕ → E, Bornology.IsBounded (Set.range f) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : E,
      Filter.Tendsto (fun n => A (f (φ n))) Filter.atTop (nhds g)

end TeschlODE.SturmLiouville


