-- Prove2me | Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
-- name    : ArrowDebreu_ThmI_AssumptionsItoIV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:36:01.513992+00:00
-- url     : https://prove2.me/theorems/e81486f4-ae96-4487-8a68-b22a025d29aa
-- title:
--   Assumptions I–IV of Arrow–Debreu (1954)
-- statement:
--   Let an economy with production sets $Y_j$, consumption sets $X_i$, utilities $u_i$, endowments $\zeta_i$ and shares $\alpha_{ij}$ be given, and let $Y = \sum_j Y_j$ and $\Omega = \{x \geqq 0\}$. The paper's standing assumptions are the following, each a separate predicate.
--
--   1. **I.a.** Each $Y_j$ is a closed convex subset of $\mathbb R^l$ containing $0$.
--   2. **I.b.** $Y \cap \Omega = \{0\}$ (no output without input).
--   3. **I.c.** $Y \cap (-Y) = \{0\}$ (irreversibility).
--   4. **II.** Each $X_i$ is a closed convex subset of $\mathbb R^l$ bounded from below: there is $\xi_i$ with $\xi_i \leqq x_i$ for all $x_i \in X_i$.
--   5. **III.a.** Each $u_i$ is continuous on $X_i$.
--   6. **III.b.** For every $x_i \in X_i$ there is $x_i' \in X_i$ with $u_i(x_i') > u_i(x_i)$ (no satiation).
--   7. **III.c.** For $x_i, x_i' \in X_i$, if $u_i(x_i) > u_i(x_i')$ and $0 < t < 1$, then $u_i[t x_i + (1-t) x_i'] > u_i(x_i')$.
--   8. **IV.a.** For every $i$ there is $x_i \in X_i$ with $x_i < \zeta_i$, i.e. $x_{hi} < \zeta_{hi}$ for **every** commodity $h$.
--   9. **IV.b.** $\alpha_{ij} \ge 0$ for all $i, j$, and $\sum_{i=1}^m \alpha_{ij} = 1$ for every $j$.
--
--   **Assumptions I–IV** is the conjunction of all nine; it is the hypothesis of Theorem I. Keeping the assumptions separate lets later statements (for instance Theorem II, which replaces IV.a by a weaker assumption) reuse them individually.
--
--   **Formalization Note** The paper's strict vector inequality $x < y$ means strict inequality in every component; it is written componentwise, not with the order-theoretic strict inequality on vectors (which would mean "$\leqq$ and $\ne$"). In I.b and I.c "$= 0$" is equality with the set $\{0\}$.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 267–270 (PDF pp. 4–7), Assumptions I.a, I.b, I.c (§1.2.2), II (§1.3.0), III.a, III.b, III.c (§1.3.1), IV.a, IV.b (§1.3.2)

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

variable {l m n : ℕ}

/-- **Assumption I.a** (§1.2.2, p. 267, PDF p. 4): `Y_j` is a closed convex subset of `R^l`
containing `0` (`j = 1, ⋯, n`). -/
def AssumptionIa (E : Economy l m n) : Prop :=
  ∀ j, IsClosed (E.Y j) ∧ Convex ℝ (E.Y j) ∧ (0 : Fin l → ℝ) ∈ E.Y j

/-- **Assumption I.b** (§1.2.2, p. 267, PDF p. 4): `Y ∩ Ω = 0`, i.e. the aggregate production set
meets the nonnegative orthant exactly in `{0}` ("= 0" is equality with the set `{0}`). -/
def AssumptionIb (E : Economy l m n) : Prop :=
  aggProd E ∩ Ω l = {0}

/-- **Assumption I.c** (§1.2.2, p. 267, PDF p. 4): `Y ∩ (−Y) = 0`, equality with the set `{0}`. -/
def AssumptionIc (E : Economy l m n) : Prop :=
  aggProd E ∩ negSet (aggProd E) = {0}

/-- **Assumption II** (§1.3.0, p. 268, PDF p. 5): for every consumer `i`, `X_i` is a closed convex
subset of `R^l` which is bounded from below, i.e. there is a vector `ξ_i` with `ξ_i ≦ x_i` for all
`x_i ∈ X_i` (componentwise order). -/
def AssumptionII (E : Economy l m n) : Prop :=
  ∀ i, IsClosed (E.X i) ∧ Convex ℝ (E.X i) ∧ ∃ ξ : Fin l → ℝ, ∀ x ∈ E.X i, ξ ≤ x

/-- **Assumption III.a** (§1.3.1, p. 269, PDF p. 6): `u_i` is a continuous function on `X_i`, for
every consumer `i`. -/
def AssumptionIIIa (E : Economy l m n) : Prop :=
  ∀ i, ContinuousOn (E.u i) (E.X i)

/-- **Assumption III.b** (§1.3.1, p. 269, PDF p. 6): for any `x_i ∈ X_i` there is `x_i' ∈ X_i`
with `u_i(x_i') > u_i(x_i)` (no satiation), for every consumer `i`. -/
def AssumptionIIIb (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∃ x' ∈ E.X i, E.u i x < E.u i x'

/-- **Assumption III.c** (§1.3.1, p. 269, PDF p. 6): if `u_i(x_i) > u_i(x_i')` and `0 < t < 1`,
then `u_i[t x_i + (1 − t) x_i'] > u_i(x_i')`, for every consumer `i` and all `x_i, x_i' ∈ X_i`. -/
def AssumptionIIIc (E : Economy l m n) : Prop :=
  ∀ i, ∀ x ∈ E.X i, ∀ x' ∈ E.X i, E.u i x' < E.u i x →
    ∀ t : ℝ, 0 < t → t < 1 → E.u i x' < E.u i (t • x + (1 - t) • x')

/-- **Assumption IV.a** (§1.3.2, p. 270, PDF p. 7): `ζ_i ∈ R^l`, and for some `x_i ∈ X_i`,
`x_i < ζ_i`, for every consumer `i`.

**Formalization Note.** The paper's `x < y` means `x_h < y_h` for *every* component `h` (§1.2.1);
it is written `∀ h, x h < ζ i h`, not with Lean's `<` on `Fin l → ℝ` (which means `≤` and `≠`). -/
def AssumptionIVa (E : Economy l m n) : Prop :=
  ∀ i, ∃ x ∈ E.X i, ∀ h, x h < E.ζ i h

/-- **Assumption IV.b** (§1.3.2, p. 270, PDF p. 7): for all `i, j`, `α_{ij} ≧ 0`; for all `j`,
`Σ_{i=1}^m α_{ij} = 1`. -/
def AssumptionIVb (E : Economy l m n) : Prop :=
  (∀ i j, 0 ≤ E.α i j) ∧ ∀ j, ∑ i, E.α i j = 1

/-- **Assumptions I–IV** (§§1.2.2–1.3.2, pp. 267–270, PDF pp. 4–7), the hypotheses of Theorem I:
I.a, I.b, I.c, II, III.a, III.b, III.c, IV.a and IV.b, each a separate field. -/
structure AssumptionsItoIV (E : Economy l m n) : Prop where
  Ia : AssumptionIa E
  Ib : AssumptionIb E
  Ic : AssumptionIc E
  II : AssumptionII E
  IIIa : AssumptionIIIa E
  IIIb : AssumptionIIIb E
  IIIc : AssumptionIIIc E
  IVa : AssumptionIVa E
  IVb : AssumptionIVb E

end ArrowDebreu.ThmI


