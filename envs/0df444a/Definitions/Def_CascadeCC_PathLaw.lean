-- Prove2me | Definitions.Def_CascadeCC_PathLaw
-- name    : CascadeCC_PathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:21.741074+00:00
-- url     : https://prove2.me/theorems/80934213-a7c1-409f-b44d-0a1c767b416f
-- title:
--   Path law of an adaptive decision rule with finitely many outcomes
-- statement:
--   Fix a set $A$ of actions, a finite set $O$ of outcomes, and a kernel $P$, where $P(a,o)$ is the probability of outcome $o$ under action $a$. An adaptive decision rule $\pi$ maps the list of outcomes seen so far, oldest first, to an action. Over $N$ periods, the mass of a path $\omega=(\omega_1,\dots,\omega_N)\in O^N$ is
--
--   $$
--   \prod_{t=1}^N P\bigl(\pi(\omega_1,\dots,\omega_{t-1}),\,\omega_t\bigr),
--   $$
--
--   and the expectation of a function $f$ of the path is the finite sum $\sum_{\omega\in O^N}\mathrm{mass}(\omega)\,f(\omega)$.
--
--   This is the general finite-horizon adaptive law, kept apart from the pricing model, so that any model whose periods have finitely many outcomes can use it. A rule that sees only the past outcomes is non-anticipating by construction.
--
--   **Formalization Note** No normalization is built in: the mass is a product of the kernel's values. The first $t$ outcomes of a path are `pathPrefix ω t`, a list.
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, §3, p.11 (non-anticipating policies; expectation of the demand)

import Mathlib

namespace CascadeCC

/-- The first `t` outcomes of a path `ω` of length `N`, oldest first. At `t = 0` it is the empty
history, and at `t ≥ N` it is the whole path. -/
def pathPrefix {O : Type*} {N : ℕ} (ω : Fin N → O) (t : ℕ) : List O :=
  (List.ofFn ω).take t

/-- The mass of a path `ω` under an adaptive decision rule `π : List O → A`, which maps the outcomes
seen so far, oldest first, to an action, and a kernel `P`, where `P a o` is the probability of outcome
`o` under action `a`: the product over the periods of the one-period probabilities.

**Formalization Note** This is the general finite-horizon, finite-outcome adaptive law, used for the
paper's non-anticipating policies (SSRN abstract_id=3362921, p.11): a rule that sees only the list of
past outcomes is non-anticipating by construction. No normalization is built in. -/
noncomputable def pathMass {A O : Type*} {N : ℕ} (P : A → O → ℝ) (π : List O → A)
    (ω : Fin N → O) : ℝ :=
  ∏ t : Fin N, P (π (pathPrefix ω t)) (ω t)

/-- The expectation of a function of the path under `pathMass`: a finite sum over all paths. -/
noncomputable def pathExpect {A O : Type*} [Fintype O] {N : ℕ} (P : A → O → ℝ) (π : List O → A)
    (f : (Fin N → O) → ℝ) : ℝ :=
  ∑ ω : Fin N → O, pathMass P π ω * f ω

end CascadeCC


