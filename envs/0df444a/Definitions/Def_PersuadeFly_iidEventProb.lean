-- Prove2me | Definitions.Def_PersuadeFly_iidEventProb
-- name    : PersuadeFly_iidEventProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:13.826116+00:00
-- url     : https://prove2.me/theorems/2963d0b8-95c2-4ba8-87cc-42b1185806d1
-- title:
--   The probability $\mathbf P_\mu(E)$ for $t$ iid states
-- statement:
--   For a set $E$ of sequences $(\omega_\tau)_{\tau<t}$, the probability that $t$ independent draws from $\mu$ fall in $E$:
--   $$
--   \mathbf P_\mu(E)=\sum_{(\omega_\tau)\in E}\ \prod_{\tau<t}\mu(\omega_\tau).
--   $$
--   This is the law under which Lemma 1 is stated; it is the state marginal of the path law.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 1, p.33

import Mathlib

namespace PersuadeFly

/-- **`P_μ(E)` for `t` iid states.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 1, p.33: the probability of a set `E` of state
sequences `(ω_τ)_{τ < t}` when the `ω_τ` are iid with law `μ`, i.e. `∑_{s ∈ E} ∏_{τ<t} μ(s_τ)`.

**Formalization Note** This is the state marginal of the path law (`pathProb`) restricted to the first
`t` rounds. -/
noncomputable def iidEventProb {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (t : ℕ) (E : Set (Fin t → Ω)) :
    ℝ :=
  ∑ s : Fin t → Ω, E.indicator (fun s => ∏ τ, μ (s τ)) s

end PersuadeFly


