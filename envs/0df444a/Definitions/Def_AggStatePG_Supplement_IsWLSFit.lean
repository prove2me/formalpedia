-- Prove2me | Definitions.Def_AggStatePG_Supplement_IsWLSFit
-- name    : AggStatePG_Supplement_IsWLSFit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:21:37.299797+00:00
-- url     : https://prove2.me/theorems/45150e55-ef73-4acd-9ad6-fce091611370
-- title:
--   Weighted least-squares fit $\hat Q\in\arg\min_{\hat Q\in\mathcal Q_\phi}\|\hat Q-Q\|_{2,w\times1}$
-- statement:
--   For state weights $w\in\mathbb R^{|\mathcal S|}$, the inner product (6) $\langle Q,Q'\rangle_{w\times1}=\sum_{s}\sum_{a}w(s)Q(s,a)Q'(s,a)$ induces the norm
--   $$\|Q\|_{2,w\times1}=\sqrt{\sum_{s\in\mathcal S}\sum_{a\in\mathcal A}w(s)Q(s,a)^2}.$$
--   Given a target $Q\in\mathbb R^{|\mathcal S|\times|\mathcal A|}$ and an aggregation $\phi$, a table $\hat Q$ is a **weighted least-squares fit of $Q$ in $\mathcal Q_\phi$** if
--   $$\hat Q\in\arg\min_{\hat Q'\in\mathcal Q_\phi}\|\hat Q'-Q\|_{2,w\times1}.$$
--
--   This is the approximate policy evaluation step of approximate policy iteration: with uniform weights in Algorithm 1, with the on-policy occupancy weights $\eta_{\pi_t}$ in Algorithms 2 and 4.
--
--   **Formalization Note** The squared norm $\langle\hat Q-Q,\hat Q-Q\rangle_{w\times1}$ is minimized; for the nonnegative weights used in the paper the two problems have the same minimizers. The predicate names one minimizer: when a segment has zero weight the minimizer is not unique, and any element of the argmin is allowed.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §5, p.11 (the norm ‖Q‖_{2,w×1}); Algorithm 1 step (2), p.12; Algorithm 4 step (2), p.17

import Mathlib
import Definitions.Def_AggStatePG_wInner
import Definitions.Def_AggStatePG_Supplement_aggQSet

namespace AggStatePG.Supplement

/-- The **weighted least-squares fit in `Q_φ`** (Russo, *Approximation Benefits of Policy Gradient
Methods with Aggregated States*, arXiv:2007.11684v3, §5, p.11 (the norm), Algorithm 1 step (2), p.12,
and Algorithm 4 step (2), p.17): `Q̂ ∈ argmin_{Q̂ ∈ Q_φ} ‖Q̂ − Q‖_{2,w×1}`, where
`‖Q‖_{2,w×1} = √(∑_s ∑_a w(s) Q(s,a)²)` is the norm induced by the inner product (6).
`IsWLSFit w φ Q Q̂` says that `Q̂` is one such minimizer.

**Formalization Note.** The minimized quantity is the squared norm `⟨Q̂ − Q, Q̂ − Q⟩_{w×1}`
(`wInner`, published); for the nonnegative weights the paper uses (`w ∈ Δ(S)`, `η_π`) the square root
is monotone, so the minimizers are the same. The predicate selects *one* minimizer: when some
segment carries zero weight the minimizer is not unique, and the algorithms allow any element of the
argmin. -/
def IsWLSFit {S A ι : Type*} [Fintype S] [Fintype A]
    (w : S → ℝ) (φ : S → ι) (Q Qhat : S → A → ℝ) : Prop :=
  Qhat ∈ (aggQSet φ : Set (S → A → ℝ)) ∧
    ∀ Q' ∈ (aggQSet φ : Set (S → A → ℝ)),
      AggStatePG.wInner w (Qhat - Q) (Qhat - Q) ≤ AggStatePG.wInner w (Q' - Q) (Q' - Q)

end AggStatePG.Supplement


