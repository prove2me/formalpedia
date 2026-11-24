-- Prove2me | Definitions.Def_CrossSell_Pricing_Supplement_Assortment
-- name    : CrossSell_Pricing_Supplement_Assortment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:51:19.273292+00:00
-- url     : https://prove2.me/theorems/47c95aba-114b-454e-be52-e9015dc3ea05
-- title:
--   Definition 3 — aggregate-markup-ordered assortments, including the empty prefix
-- statement:
--   For fixed prices and a complete secondary configuration T, assign main product i the aggregate markup a_i=p_i-c_i+t_i(T_i), where t_i is the published conditional secondary profit. A main enumeration sigma is sorted when a_sigma(j) is weakly decreasing. Its prefix of length m is
--   $$S_m=\{\sigma(j):0\le j<m\}.$$
--   An assortment is aggregate-markup ordered when it is such a prefix of a permutation of the whole finite main universe. All tie orders are admitted. The prefix length ranges from zero to the size of that universe, so the empty assortment is represented explicitly. This boundary convention preserves the decision domain S subset M of (13), including when all main offers reduce the profit relative to outside sales. This definition places no restriction on prices or margins and keeps the ordering dependent on the secondary configuration.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 19, Definition 3; pp. 18–19, problem (13)

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing.Supplement
open Finset
variable {ι κ : Type*}

/-- The first m elements of an enumeration; m=0 is the empty assortment. -/
def offerPrefix [DecidableEq ι] {n : ℕ} (σ : Fin n ≃ ι) (m : ℕ) : Finset ι :=
  (Finset.univ.filter (fun j : Fin n => j.val < m)).image σ

/-- Weak descending order, permitting all tie permutations. -/
def Sorted {n : ℕ} (a : ι → ℝ) (σ : Fin n ≃ ι) : Prop :=
  ∀ j k : Fin n, j ≤ k → a (σ k) ≤ a (σ j)

/-- Definition 3, for the complete universe of main products. -/
def AggregateOrdered [Fintype ι] [DecidableEq ι]
    (T : Option ι → Finset κ) (c p : ι → ℝ) (s r : κ → ℝ)
    (v : Option ι → κ → ℝ) (S : Finset ι) : Prop :=
  ∃ σ : Fin (Fintype.card ι) ≃ ι, Sorted (aggMarkup T c s v p r) σ ∧
    ∃ m : ℕ, m ≤ Fintype.card ι ∧ S = offerPrefix σ m

end CrossSell.Pricing.Supplement


