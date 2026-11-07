-- Prove2me | Definitions.Def_AlgoPFR_condLaw
-- name    : AlgoPFR_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:35.159629+00:00
-- url     : https://prove2.me/theorems/6cd81976-f8f3-4786-be78-4f63be9edc99
-- title:
--   Conditional laws, expectations in $[0,\infty]$, conditional entropy and $I[X:J]$
-- statement:
--   This item fixes four general tools for laws.
--
--   1. $q(\cdot\mid E)$ is the law $q$ conditioned on an event $E$ of positive probability.
--   2. $\mathbb E_{a\sim q}[f(a)]=\sum_a q(a)f(a)$ is taken in $[0,\infty]$, for $f$ nonnegative on the support of $q$.
--   3. For a joint law $q$ of $(X,J)$ with $X\in\mathbb F_2^n$, the conditional law $(X\mid J=j)$ and the conditional entropy $H[X\mid J]=\sum_j\Pr[J=j]\,H[X\mid J=j]$.
--   4. The mutual information
--   $$I[X:J]=H[X]-H[X\mid J].$$
--
--   The label $J$ of the bucketing step takes values in all of $\mathbb N$, which is why expectations over labels live in $[0,\infty]$: an upper bound on a divergent real series would otherwise hold by a junk value.
--
--   **Formalization Note** The source defines $I[X:J]=H[X]+H[J]-H[X,J]$ (Eq. (4)). By the chain rule (3) this is $H[X]-H[X\mid J]$, the form used here, which stays finite for infinite labels. Conditioning on an event of probability zero returns $q$; every use excludes that case or weights it by probability zero.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), §3.2–3.3, pp.13–15, Eqs. (2), (4), (7)

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

open Classical in
/-- The law `q` conditioned on the event `E`.

**Formalization Note.** Conditioning on an event of probability zero has no meaning; the definition
returns `q` itself there. Every statement of the mission either excludes that case by a support
hypothesis or weights the result by the probability of the event, which is then `0`. -/
def condLaw {α : Type} (q : PMF α) (E : Set α) : PMF α :=
  if h : ∃ a ∈ E, a ∈ q.support then q.filter E h else q

/-- The expectation `E_{a∼q}[f a]` of a real function that is nonnegative on the support of `q`, as
an element of `[0, ∞]`.

**Formalization Note.** Bucket labels range over all of `ℕ`, and a non-summable real `tsum` would
be the junk value `0`, which would make an upper bound on it vacuous. An `ℝ≥0∞` sum has no junk
value. Every `f` used in the mission (`d`, `Δ`, `Φ`, `C_access`) is nonnegative, so `ofReal` loses
nothing. -/
def expect {α : Type} (q : PMF α) (f : α → ℝ) : ℝ≥0∞ :=
  ∑' a, q a * ENNReal.ofReal (f a)

/-- For a joint law `q` of `(X, J)` the conditional law `(X | J = j)`, as in
arXiv:2609.20771 (sha256 60e45066…), Lemma 3.6, p.15. -/
def labelFiber {n : ℕ} {ι : Type} (q : PMF (Vec n × ι)) (j : ι) : PMF (Vec n) :=
  (condLaw q {ω | ω.2 = j}).map Prod.fst

/-- The conditional entropy `H[X | J] = ∑_j p_J(j) H[X | J = j]`, Eq. (2), p.13 of
arXiv:2609.20771 (sha256 60e45066…).

**Formalization Note.** The real `tsum` is safe here: `H[X | J = j] ≤ n` for every `j`, so the
series always converges. -/
def condEntropy {n : ℕ} {ι : Type} (q : PMF (Vec n × ι)) : ℝ :=
  ∑' j, ((q.map Prod.snd) j).toReal * entropy (labelFiber q j)

/-- The mutual information `I[X : J]` of a joint law `q` of `(X, J)`.

**Formalization Note.** Eq. (4), p.14 of arXiv:2609.20771 (sha256 60e45066…) defines
`I[X : J] = H[X] + H[J] − H[X, J]`. By the chain rule (3) this equals `H[X] − H[X | J]`, which is the
form used here. The label `J` may range over a countably infinite set, where `H[J]` itself can be
infinite, while `H[X] − H[X | J]` is always a finite real. -/
def labelInfo {n : ℕ} {ι : Type} (q : PMF (Vec n × ι)) : ℝ :=
  entropy (q.map Prod.fst) - condEntropy q

end

end AlgoPFR


