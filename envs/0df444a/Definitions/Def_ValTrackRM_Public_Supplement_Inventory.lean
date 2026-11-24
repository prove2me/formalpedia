-- Prove2me | Definitions.Def_ValTrackRM_Public_Supplement_Inventory
-- name    : ValTrackRM_Public_Supplement_Inventory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:57:03.137069+00:00
-- url     : https://prove2.me/theorems/41bd4888-46e5-4f02-a387-608394a2cce9
-- title:
--   Definitions 2–4 — remaining inventory, price law and Algorithm 1 prime (corrected polarity)
-- statement:
--   A finite price code $p\in\{0,\ldots,m\}$ denotes the offer $r^{(p+1)}$ when $p<m$, and rejection when $p=m$. A rejection earns zero. The remaining inventory of a sold vector $s$ is the number of its false coordinates. The published Algorithm 1 sold law gives both its inventory mass and its joint next-price/inventory mass.
--
--   For a deterministic valuation prefix $W$, let $i$ be its selected minimal-level unit and $\ell$ its level. The corrected Algorithm 1 prime offers a finite price using the unsold conditional probability:
--   $$
--   \Pr[P=r^{(j)}\mid I=a]=\Pr[S_i=0\mid I=a]\frac{q^{(j)}}{\sum_{u=\ell+1}^{m}q^{(u)}}\quad(\ell<j\le m).
--   $$
--   The complementary probability rejects. The next inventory and revenue follow the purchase comparison after the price has been selected. Forward recursion constructs the inventory law and expected revenue of this policy; neither is supplied by an axiom.
--
--   **Formalization Note** Definition 3 reverses the sold/unsold polarity in its steps 2–3. The preceding unsold paragraph on p.14 and the first display of the ec6 proof specify the correction used here. Zero-stock states, zero-mass conditioning states and terminal levels reject. The published base functions, prices, levels and sold law are reused unchanged.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. 14–15, Definitions 2–4; p. ec6, proof of Lemma 2

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

namespace ValTrackRM.Public.Supplement

/-! Definitions 2–4, pp. 14–15. A price code p denotes r^(p+1); p=m denotes
rejection, whose revenue is zero. All probability calculations below are finite sums. -/
abbrev Price (m : ℕ) := Fin (m + 1)

def isMin {m k : ℕ} (sel : (Fin k → Fin (m + 1)) → Fin k) : Prop :=
  ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i

noncomputable def reject {m : ℕ} (p : Price m) : ℝ := if p.val = m then 1 else 0

def inventory {k : ℕ} (s : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => s i = false).card

noncomputable def buys {m : ℕ} (r : ℕ → ℝ) (a : ℕ) (p : Price m)
    (v : Fin (m + 1)) : Bool := decide (0 < a ∧ p.val < m ∧ r (p.val + 1) ≤ r v)

noncomputable def nextStock {m : ℕ} (r : ℕ → ℝ) (a : ℕ) (p : Price m)
    (v : Fin (m + 1)) : ℕ := a - if buys r a p v then 1 else 0

noncomputable def payment {m : ℕ} (r : ℕ → ℝ) (a : ℕ) (p : Price m)
    (v : Fin (m + 1)) : ℝ := if buys r a p v then r (p.val + 1) else 0

/-- Algorithm 1's actual price distribution, before seeing the current valuation. -/
noncomputable def unitPrice {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (L : Fin k → Fin (m + 1))
    (s : Fin k → Bool) (p : Price m) : ℝ :=
  if s (sel L) = false ∧ (L (sel L)).val < m then
    if (L (sel L)).val < p.val + 1 ∧ p.val < m then
      offerProb r m (L (sel L)).val (p.val + 1)
    else 0
  else reject p

noncomputable def a1Stock {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1))) (a : ℕ) : ℝ :=
  ∑ s, soldLaw r sel W s * if inventory s = a then 1 else 0

noncomputable def a1Joint {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1)))
    (a : ℕ) (p : Price m) : ℝ :=
  ∑ s, soldLaw r sel W s * (if inventory s = a then unitPrice r sel (levels sel W) s p else 0)

/-- Selected sold probability conditioned on the remaining inventory; 0/0 is zero. -/
noncomputable def soldConditional {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1))) (a : ℕ) : ℝ :=
  (∑ s, soldLaw r sel W s *
    if inventory s = a ∧ s (sel (levels sel W)) = true then 1 else 0) / a1Stock r sel W a

/-- Definition 3 with its ec6 polarity correction: offer with the UNSOLD probability.
Zero stock, unreachable states, and a terminal level are totalized by rejection. -/
noncomputable def primeKernel {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (V : List (Fin (m + 1)))
    (t a : ℕ) (p : Price m) : ℝ :=
  let W := V.take (t - 1)
  let ℓ := (levels sel W (sel (levels sel W))).val
  if a = 0 ∨ a1Stock r sel W a = 0 ∨ ℓ = m then reject p
  else
    let unsold := 1 - soldConditional r sel W a
    if p.val = m then 1 - unsold
    else if ℓ < p.val + 1 then unsold * offerProb r m ℓ (p.val + 1) else 0

/-- Forward law for any inventory-only pricing policy on a fixed valuation sequence. -/
noncomputable def fixedStock {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (V : List (Fin (m + 1))) : ℕ → ℕ → ℝ
  | 0, b => if b = k then 1 else 0
  | n + 1, b => ∑ a : Fin (k + 1), ∑ p : Price m,
      fixedStock r k K V n a.val * K (n + 1) a.val p *
        if nextStock r a.val p (valIdx V (n + 1)) = b then 1 else 0

noncomputable def fixedConditional {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (V : List (Fin (m + 1))) (t a : ℕ) (p : Price m) : ℝ :=
  fixedStock r k K V (t - 1) a * K t a p / fixedStock r k K V (t - 1) a

noncomputable def fixedRevenue {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (V : List (Fin (m + 1))) : ℝ :=
  ∑ t ∈ Finset.Icc 1 V.length, ∑ a : Fin (k + 1), ∑ p : Price m,
    fixedStock r k K V (t - 1) a.val * K t a.val p * payment r a.val p (valIdx V t)

end ValTrackRM.Public.Supplement


