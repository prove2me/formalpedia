-- Prove2me | Definitions.Def_RevenueOrdered_UDPmin_Reduction
-- name    : RevenueOrdered_UDPmin_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:32.361454+00:00
-- url     : https://prove2.me/theorems/e80858f9-dcb4-4b9c-99bb-fdf04d03c4dd
-- title:
--   The assortment instance of Theorem 4.6: products $[n]\times\{v_1,\dots,v_m\}$ and the choice model $\mathcal P=\frac1m\sum_i\mathcal P_i$
-- statement:
--   Fix a $\mathrm{UDP}_{\min}$ instance with items $[n]$, consumers $[m]$, interest sets $B_i$ and valuations $v_i>0$. The proof of Theorem 4.6 builds the following assortment instance.
--
--   1. **Products.** $\mathcal C:=[n]\times\{v_1,\dots,v_m\}$, all pairs of an item and a valuation value (equal valuations give one value).
--   2. **Revenues.** $r((x,v)):=m\cdot v$.
--   3. **The sets $Q_i(S)$.** For $S\subseteq\mathcal C$ and consumer $i$,
--   $$Q_i(S):=\{(x,v)\in S:\ x\in B_i,\ v\le v_i,\ \text{and } v'\ge v\ \text{for all }(x',v')\in S\text{ with }x'\in B_i\}.$$
--   4. **Choice probabilities.** $\mathcal P_i((x,v),S):=1/|Q_i(S)|$ if $(x,v)\in Q_i(S)$ and $0$ otherwise, and
--   $$\mathcal P(y,S):=\frac1m\sum_{i=1}^m\mathcal P_i(y,S).$$
--   5. **Price assignment of an assortment.** $p_S(x):=\min\{v:(x,v)\in S\}$ if some $(x,v)\in S$, and otherwise a price larger than every valuation (the paper's $+\infty$).
--   6. **Assortment of a price assignment.** $S_p:=\{(x,v)\in\mathcal C: v\ge p(x)\}$.
--
--   This is the dictionary between pricing and assortments through which the paper transfers its revenue-ordered guarantee to uniform pricing.
--
--   **Formalization Note** The valuation set is `Finset.univ.image v`, and `RedProd I = X × {w // w ∈ vals I}`. The paper's $+\infty$ price is replaced, as its Remark on p. 18 allows, by the real $1+\sum_i v_i$, which exceeds every valuation because valuations are positive. The no-purchase probability of this model is `noPurchase (redP I) S` from the model file.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 17–19 (§4.5.1, proof of Theorem 4.6: 𝒞, r, Q_i(S), 𝒫_i, 𝒫, p_S with the Remark on p. 18, S_p)

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Model
import Definitions.Def_RevenueOrdered_UDPmin_Pricing

namespace RevenueOrdered.UDPmin

open Classical in
/-- The set `{v_1, …, v_m}` of consumer valuations (duplicates collapsed). -/
noncomputable def vals {X M : Type*} [Fintype M] (I : Instance X M) : Finset ℝ :=
  Finset.univ.image I.v

/-- The product set of the assortment instance of Theorem 4.6 (Berbeglia–Joret,
arXiv:1606.01371v3, §4.5.1, p. 17): `𝒞 := [n] × {v_1, …, v_m}`, all pairs of an item and a
consumer valuation. -/
abbrev RedProd {X M : Type*} [Fintype M] (I : Instance X M) : Type _ :=
  X × {w : ℝ // w ∈ vals I}

variable {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]

/-- The revenue function `r((x, v)) := m · v` of the assortment instance (p. 17), `m = |M|`. -/
noncomputable def redRev (I : Instance X M) (y : RedProd I) : ℝ :=
  (Fintype.card M : ℝ) * (y.2 : ℝ)

open Classical in
/-- `Q_i(S) := {(x, v) ∈ S : x ∈ B_i, v ≤ v_i, and v' ≥ v for all (x', v') ∈ S with x' ∈ B_i}`
(p. 17). -/
noncomputable def Q (I : Instance X M) (i : M) (S : Finset (RedProd I)) : Finset (RedProd I) :=
  S.filter (fun y => y.1 ∈ I.B i ∧ (y.2 : ℝ) ≤ I.v i ∧
    ∀ y' ∈ S, y'.1 ∈ I.B i → (y.2 : ℝ) ≤ (y'.2 : ℝ))

open Classical in
/-- `𝒫_i((x, v), S) := 1/|Q_i(S)|` if `(x, v) ∈ Q_i(S)`, and `0` otherwise (p. 17). -/
noncomputable def Pcons (I : Instance X M) (i : M) (y : RedProd I) (S : Finset (RedProd I)) : ℝ :=
  if y ∈ Q I i S then 1 / ((Q I i S).card : ℝ) else 0

/-- The choice probabilities of the assortment instance, `𝒫(y, S) := (1/m) ∑_{i=1}^{m} 𝒫_i(y, S)`
(p. 17), for products `y`. The no-purchase probability is `noPurchase (redP I) S`. -/
noncomputable def redP (I : Instance X M) (y : RedProd I) (S : Finset (RedProd I)) : ℝ :=
  (1 / (Fintype.card M : ℝ)) * ∑ i, Pcons I i y S

/-- A real price strictly above every valuation, used for the paper's `+∞` price
(Remark, p. 18: "simply replace +∞ … by any real larger than v_m"): `1 + ∑_i v_i`. -/
noncomputable def priceTop (I : Instance X M) : ℝ :=
  1 + ∑ i, I.v i

open Classical in
/-- The price assignment `p_S` of the assortment `S` (p. 18): `p_S(x) := min{v : (x, v) ∈ S}` if
some `(x, v) ∈ S`, and otherwise the price `priceTop I > v_m` standing for `+∞`. -/
noncomputable def priceOf (I : Instance X M) (S : Finset (RedProd I)) (x : X) : ℝ :=
  if h : ((S.filter (fun y => y.1 = x)).image (fun y => (y.2 : ℝ))).Nonempty then
    ((S.filter (fun y => y.1 = x)).image (fun y => (y.2 : ℝ))).min' h
  else priceTop I

open Classical in
/-- The assortment `S_p := {(x, v) : x ∈ [n], v ∈ {v_1, …, v_m}, v ≥ p(x)}` of a price
assignment `p` (p. 19). -/
noncomputable def assortOf (I : Instance X M) (p : X → ℝ) : Finset (RedProd I) :=
  Finset.univ.filter (fun y => p y.1 ≤ (y.2 : ℝ))

end RevenueOrdered.UDPmin


