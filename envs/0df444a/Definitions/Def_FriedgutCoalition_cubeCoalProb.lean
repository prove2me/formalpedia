-- Prove2me | Definitions.Def_FriedgutCoalition_cubeCoalProb
-- name    : FriedgutCoalition_cubeCoalProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:31.582022+00:00
-- url     : https://prove2.me/theorems/2d102404-9038-4e0a-9b08-c18a3e6f3222
-- title:
--   Coalition probability $\mathbf P^b_S(f)$ and expectation $\mathbb E[f]$ on the solid cube $[0,1]^n$
-- statement:
--   Equip $[0,1]^n$ with the uniform (Lebesgue product) measure $\lambda$. For $f:[0,1]^n\to\{0,1\}$, $S\subseteq[n]$ and $b\in\{0,1\}$, the coalition probability is
--
--   $$\mathbf P^b_S(f)=\Pr_{x\sim\lambda}\big[\exists\, j\in[0,1]^S:\ f(j,x_{-S})=b\big],$$
--
--   and $\mathbb E[f]=\lambda(\{x: f(x)=1\})$. The paper uses these only for monotone or Borel measurable $f$, for which the success event is Lebesgue measurable.
--
--   They are the quantities in which Friedgut's conjecture and Corollary 3.2 are stated.
--
--   **Formalization Note** $\mathbf P^b_S(f)$ is defined as $1-\lambda^*(F)$, where $F=\{x:\ \forall j,\ f(j,x_{-S})\ne b\}$ is the failure set and $\lambda^*$ is Lebesgue outer measure. This is the inner measure of the success event: it equals the probability above whenever the event is measurable and is never larger than it. $\mathbb E[f]$ is the outer measure of $\{f=1\}$, which is the expectation whenever that set is measurable. No Bochner integral is used, so a non-measurable integrand cannot produce the value $0$.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), §2.1, p.5 ("We use the same definitions for monotone or Borel measurable functions f : [0,1]ⁿ → {0,1} …")

import Mathlib

namespace FriedgutCoalition

/-!
# Coalition probability and expectation on the solid cube `[0,1]ⁿ`

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), §2.1, p.5: "We use the same definitions for monotone or
Borel measurable functions `f : [0,1]ⁿ → {0,1}`, with each coordinate sampled uniformly from `[0,1]` and
coalition assignments chosen from `[0,1]^S`."

**Formalization Note.**
* `[0,1]` is `unitInterval` with Lebesgue measure, and `[0,1]ⁿ` is `Fin n → unitInterval` with the
  product measure (`MeasureSpace.pi`), a probability measure.
* `P^b_S(f) := 1 − µ*(F)`, where `F = {x | ∀ j ∈ [0,1]ⁿ, f(S.piecewise j x) ≠ b}` is the failure set and
  `µ*` is the measure applied to an arbitrary set, i.e. Lebesgue outer measure. This is the inner measure
  of the success event. It equals the paper's probability whenever the success event is Lebesgue
  measurable, which the paper proves for monotone and for Borel `f` (p.5), the only functions any
  statement applies it to, and it is never larger than the true value. The coordinates in `S` are
  sampled and then overwritten, which does not change the probability (product measure).
* `E[f] := µ*({x | f x = true})`, which is `E[f]` whenever `{f = 1}` is Lebesgue measurable. It is not a
  Bochner integral, so no junk value `0` arises for a non-measurable integrand.
* `{0,1}` is `Bool`.
-/

open MeasureTheory

/-- `P^b_S(f)` on `[0,1]ⁿ`: one minus the (outer) measure of the set of `x` for which no assignment of
the coordinates in `S` makes `f` output `b`. -/
noncomputable def cubeCoalProb {n : ℕ} (f : (Fin n → unitInterval) → Bool) (S : Finset (Fin n))
    (b : Bool) : ℝ :=
  1 - (volume {x : Fin n → unitInterval |
    ∀ j : Fin n → unitInterval, f (S.piecewise j x) ≠ b}).toReal

/-- `E[f]` on `[0,1]ⁿ` with the uniform measure: the (outer) measure of `{x | f x = 1}`. -/
noncomputable def cubeMean {n : ℕ} (f : (Fin n → unitInterval) → Bool) : ℝ :=
  (volume {x : Fin n → unitInterval | f x = true}).toReal

end FriedgutCoalition


