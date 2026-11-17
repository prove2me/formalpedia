-- Prove2me | Definitions.Def_SupplyRevenue_Supplement_Regularizer
-- name    : SupplyRevenue_Supplement_Regularizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:33:09.282379+00:00
-- url     : https://prove2.me/theorems/ddceaa59-f1a3-4612-a931-2c5ba85c23d1
-- title:
--   Query-free polynomial-time regularizers of source offers
-- statement:
--   A **regularizer** maps the number of items $m$, a denominator exponent $B$, a rational $\varepsilon$ and **one** source offer (its assortment and rational prices) to new rational prices. It sees nothing else: no instance, no type or demand query, no class parameter, no cap and no residual order.
--
--   The input is encoded in binary with self-delimiting codes, with $B$ written in **unary**, and the regularizer is **polynomial-time** if a multi-stack Turing machine maps the code of every input to the code of its output list in time polynomial in the input length. Hence its arithmetic and its output price bits are polynomial in $m$, $B$, the bit size of $\varepsilon$ (at least $\log(1/\varepsilon)$) and the price bits.
--
--   The **regularized offer** keeps the assortment and takes the regularizer's prices, clamped at $0$. This is the "query-free regularization" of Theorem 3.1 (and Lemma 2.3).
--
--   **Formalization Note** An offer is passed as the list over items of `none` (off the assortment) or `some p_j`. Polynomial time is the published `PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime`) on the published codes `encBin`, `encNat`, `encRat`.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), Theorem 3.1, p.7; Lemma 2.3, p.7

import Mathlib
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_Supplement_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace SupplyRevenue
namespace Supplement

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

/-!
# Query-free regularizers of source offers (Theorem 3.1)

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
Theorem 3.1, p.7: "For nonnegative rational prices, a supplied bound 2^B on supported global valuation denominators
permits query-free regularization … No training, construction type/demand query, support enumeration, calibration or
partition is needed. With rational inputs, a matrix uses n source draws, n activation coins and polynomial
arithmetic/price bits in m, B, log(1/ε), cap and sampled-price encodings"; Lemma 2.3, p.7.

**Formalization Note** A regularizer is a function of `m`, the exponent `B`, `ε` and **one** source offer (its
assortment and rational prices), and of nothing else: no instance, type, demand query, `r`, `δ` or residual order. The
input is encoded in binary with the published self-delimiting codes `encBin`, `encRat`, and `B` in **unary** (`encNat`),
so polynomial time is polynomial in `m`, `B`, the size of `ε` (at least `log(1/ε)`) and the price sizes. An offer is the
list over items `j < m` of `none` (off the assortment) or `some p_j`. The output is the list of new prices, encoded with
`encRat`; `PolyTimeRegularizer` asks a polynomial-time string function (Mathlib's multi-stack machines, published
`PolyTimeComputable`) that maps every input code to the output code, which also bounds the output price bits. The
regularized offer keeps the assortment and takes the `j`-th output price, clamped at `0`.
-/

/-- The input of a regularizer: `m`, the denominator exponent `B`, `ε`, and one offer as a list over items. -/
structure RegInput where
  m : ℕ
  B : ℕ
  ε : ℚ
  offer : List (Option ℚ)

/-- Binary code of a regularizer input (`B` in unary). -/
def encRegInput (x : RegInput) : Str :=
  encBin x.m ++ encNat x.B ++ encRat x.ε ++
    x.offer.flatMap fun o => match o with
      | none => [false]
      | some q => true :: encRat q

/-- Binary code of a list of rationals. -/
def encRatList (l : List ℚ) : Str := l.flatMap encRat

/-- A regularizer is computable in polynomial time on these codes. -/
def PolyTimeRegularizer (reg : RegInput → List ℚ) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ x, f (encRegInput x) = encRatList (reg x)

/-- An offer as regularizer data: `some p_j` on the assortment (as a rational), `none` off it. -/
noncomputable def offerData {m : ℕ} (o : Offer m) : List (Option ℚ) :=
  List.ofFn fun j : Fin m => if j ∈ o.assort then some (toRat (o.price j)) else none

/-- The regularized offer: same assortment, the regularizer's prices (clamped at `0`). -/
noncomputable def regOffer (reg : RegInput → List ℚ) (m B : ℕ) (ε : ℚ) (o : Offer m) : Offer m where
  assort := o.assort
  price := fun j => max 0 (((reg ⟨m, B, ε, offerData o⟩).getD j.val 0 : ℚ) : ℝ)
  price_nonneg := fun _ => le_max_left _ _

end Supplement
end SupplyRevenue


