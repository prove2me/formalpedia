-- Prove2me | Definitions.Def_CompetingSellers_priceRep
-- name    : CompetingSellers_priceRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:53.510077+00:00
-- url     : https://prove2.me/theorems/68d7e955-14dc-49e6-91f7-34687cb7a2c5
-- title:
--   The proper pricing representation $P_M$ of a mechanism
-- statement:
--   For a mechanism $M$ of a seller whose good the buyer values at $v_i$ ($v_A=a$, $v_B=b$), let
--   $$K_i=\{(x,p)\in[0,1]\times[0,v_i]:\exists\sigma,\ \mathbb E_{M(\sigma)}[q]=x,\ \mathbb E_{M(\sigma)}[t]\le p\},$$
--   $C_i=\operatorname{conv}K_i$, and $P_M(x)=\min\{p:(x,p)\in C_i\}$ (and $\infty$ if there is no such $p$). The paper identifies each mechanism with this representation ("$M(x)=P_M(x)$", p.18): $\mathrm{util}_M$, $z^\pm_M$ and $\mathrm{Aug}_M$ are those of $P_M$.
--
--   Observation 2.2 states that $P_M$ is proper and essentially equivalent to $M$.
--
--   **Formalization Note** The minimum is an infimum in $[0,\infty]$. The cutoff $v_i$ follows the proof: options costing more than $v_i$ are never used by a utility-maximizing buyer.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Proof of Observation A.2, p.50 and of Observation 2.2, p.54 (PDF 57); p.18

import Mathlib
import Definitions.Def_CompetingSellers_Mech
import Definitions.Def_CompetingSellers_utilP

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

variable {S : Type} [MeasurableSpace S] {null : S}

/-- The auxiliary menu `K_i = {(x, p) ∈ [0, 1] × [0, v_i] : ∃ μ ∈ im(M_i), E_μ[q] = x,
E_μ[t] ≤ p}` of a mechanism of a seller whose good the buyer values at `v_i` (proof of
Observation A.2, p.50). -/
def menuK (vi : ℝ) (M : Mech S null) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ vi ∧ ∃ σ : S, M.alloc σ = q.1 ∧ M.pay σ ≤ ENNReal.ofReal q.2}

/-- **The proper pricing representation `P_M`** (Observation 2.2 and its proof, pp.17, 54).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), proof of Observation 2.2, p.54 (PDF 57): "Let `C_i = conv K_i`
and `x̄_i = max{x : (x, p) ∈ C_i}`. Define `P_{M_i}(x) = min{p : (x, p) ∈ C_i}` for
`0 ≤ x ≤ x̄_i`, and `∞` for `x > x̄_i`." p.18: "Henceforth, we identify each mechanism `M` with
its essentially equivalent proper pricing rule: `M(x) = P_M(x)`."

`priceRep v_i M` is `P_M` for a mechanism of the seller whose good is worth `v_i` to the buyer
(`a` for Alice, `b` for Bob).

**Formalization Note.** The minimum is an infimum in `ℝ≥0∞` (`∞` where no `(x, p)` lies in
`conv K_i`). The helpers `mUtil`, `mZPlus`, `mZMinus`, `mAug` are the paper's `util_M`, `z⁺_M`,
`z⁻_M`, `Aug_M` of a mechanism, computed from `P_M` as on p.17–19. -/
noncomputable def priceRep (vi : ℝ) (M : Mech S null) (x : ℝ) : ℝ≥0∞ :=
  ⨅ (p : ℝ) (_ : (x, p) ∈ convexHull ℝ (menuK vi M)), ENNReal.ofReal p

/-- `util_M(v)` of a mechanism of the seller valued `v_i` (p.18): `util_{P_M}(v)`. -/
noncomputable def mUtil (vi : ℝ) (M : Mech S null) (v : ℝ) : ℝ := utilP (priceRep vi M) v

/-- `z⁺_M(v)` (p.17): the largest maximizer of `v x − P_M(x)`. -/
noncomputable def mZPlus (vi : ℝ) (M : Mech S null) (v : ℝ) : ℝ := zPlus (priceRep vi M) v

/-- `z⁻_M(v)` (p.17): the smallest maximizer of `v x − P_M(x)`. -/
noncomputable def mZMinus (vi : ℝ) (M : Mech S null) (v : ℝ) : ℝ := zMinus (priceRep vi M) v

/-- `Aug_M(v, w) = util_M(w) − util_M(max(0, w − v))` (eq. (2), p.19). -/
noncomputable def mAug (vi : ℝ) (M : Mech S null) (v w : ℝ) : ℝ := augP (priceRep vi M) v w

end CompetingSellers


