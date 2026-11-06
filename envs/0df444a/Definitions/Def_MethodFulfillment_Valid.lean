-- Prove2me | Definitions.Def_MethodFulfillment_Valid
-- name    : MethodFulfillment_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:51.753904+00:00
-- url     : https://prove2.me/theorems/cd300a90-23f9-48c8-a51f-2170ada2199e
-- title:
--   Standing assumptions of the fulfillment model
-- statement:
--   A fulfillment instance is **valid** when it satisfies the paper's standing assumptions:
--
--   1. the discard method $m'(q)$ (the empty set of pairs) is a method of every order type $q$;
--   2. every submethod of a method is a method: if $m\in M(q)$ and $\tilde m\subseteq m$ then $\tilde m\in M(q)$;
--   3. a method of $q$ ships only items of $q$, and each from at most one facility;
--   4. $\kappa>1$, and for every $m\in M(q)$
--   $$c_m\le c_{m'(q)}\le \kappa\, c_m ;$$
--   5. the arrival probabilities are nonnegative and $\sum_{q\in Q}p_t(q)\le 1$ for every $t$ (at most one order arrives per period).
--
--   Item 2 is the consequence of the dummy-facility assumption stated on p.9; the first inequality of item 4 is the assumption, made without loss of generality on p.36, that the discard method is the most expensive method of $q$; the second is $c_{m'(q)}/c_m\le\kappa$ (p.9).
--
--   **Formalization Note** The ratio bound is stated multiplied out, so no positivity of costs is assumed; together with $\kappa>1$ the two inequalities force every cost to be nonnegative. The paper's "Sik < T" in Definition 4 is not assumed.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), §2, pp.7–9; proof of Lemma 2, p.36

import Mathlib
import Definitions.Def_MethodFulfillment_Instance

namespace MethodFulfillment

/-- The standing assumptions of the model (Amil, Makhdoumi & Wei, manuscript, PDF sha256
197c13b9…, §2, pp.7–9, and the proof of Lemma 2, p.36):
1. the discard method `m′(q)` (Lean `∅`) is a method of every order type;
2. every submethod of a method is a method ("under the dummy facility assumption, any submethod
   … is a method itself", p.9);
3. a method ships only items of its order type, each from at most one facility (display, p.8);
4. `κ > 1`, the discard method is the most expensive method of `q` (p.36), and
   `c_{m′(q)} / c_m ≤ κ` for every `m ∼ q` (p.9);
5. the arrival probabilities are nonnegative and at most one order arrives per period
   (`∑_q p_t(q) ≤ 1`, p.7).

**Formalization Note.** The ratio `c_{m′(q)}/c_m ≤ κ` is stated cross-multiplied,
`c q ∅ ≤ κ * c q m`; with `c q m ≤ c q ∅` and `κ > 1` it forces every cost to be nonnegative, so
no positivity of costs is assumed. "Higher" (p.7) / "largest" (p.36) is read as `≤`. Nothing else
is assumed; in particular Definition 4's "`S_{ik} < T`" (p.15) is not. -/
structure Valid {I K Q : Type} [Fintype Q] {T : ℕ} (P : Instance I K Q T) : Prop where
  /-- The discard method `m′(q) = ∅` belongs to `M(q)`. -/
  discard_mem : ∀ q, ∅ ∈ P.methods q
  /-- Every submethod of a method is a method. -/
  down_closed : ∀ q, ∀ m ∈ P.methods q, ∀ m' : Finset (I × K), m' ⊆ m → m' ∈ P.methods q
  /-- A method of `q` ships only items of `q`. -/
  pair_item : ∀ q, ∀ m ∈ P.methods q, ∀ x ∈ m, x.1 ∈ P.items q
  /-- A method ships each item from at most one facility. -/
  one_facility : ∀ q, ∀ m ∈ P.methods q, ∀ x ∈ m, ∀ x' ∈ m, x.1 = x'.1 → x = x'
  /-- `κ > 1`. -/
  one_lt_kappa : 1 < P.κ
  /-- The discard method is the most expensive method of `q` (p.36). -/
  cost_le_discard : ∀ q, ∀ m ∈ P.methods q, P.c q m ≤ P.c q ∅
  /-- `c_{m′(q)} ≤ κ c_m` for every method `m` of `q` (p.9). -/
  discard_le_kappa_mul : ∀ q, ∀ m ∈ P.methods q, P.c q ∅ ≤ P.κ * P.c q m
  /-- Arrival probabilities are nonnegative. -/
  prob_nonneg : ∀ t q, 0 ≤ P.p t q
  /-- At most one order arrives per period. -/
  prob_sum_le_one : ∀ t, ∑ q, P.p t q ≤ 1

end MethodFulfillment


