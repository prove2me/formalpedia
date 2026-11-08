-- Prove2me | Definitions.Def_AvoidPlast_FieldScheme
-- name    : AvoidPlast_FieldScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:52.329273+00:00
-- url     : https://prove2.me/theorems/930ea04d-7f01-440e-9fe0-7706032e253a
-- title:
--   Field representation schemes
-- statement:
--   A field representation scheme: a set of admissible sizes; for each admissible $Q$, a field structure on $\{0,\dots,Q-1\}$; and machines deciding admissibility and computing addition and multiplication in time polynomial in $\log Q$, elements being written in $\lceil\log_2Q\rceil$ bits. The numeric order of the elements is the order behind "the first $|H|$ elements". Since the explicit input of Theorem 4.5 carries only $|F|$, the field must be a function of its size. The characteristic-$2$ fields that the paper instantiates, numbered by their binary representations, form a scheme (footnote 19 asks only for an enumerable order).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5 and footnote 19, p.18

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_fixedBits

namespace AvoidPlast

/-- A field representation scheme (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.5 and footnote 19, p.18): for each admissible size
`Q` a field structure on `Fin Q`, with admissibility, addition and multiplication computable in time
polynomial in `log Q`. Elements are written in `⌈log₂ Q⌉` bits, and the numeric order of `Fin Q` is
the order behind "the first `|H|` elements". The theorem's explicit input carries only `|F|`, so the
field must be a function of its size.

**Formalization Note** Footnote 19 asks only that `H` can be enumerated; a field whose elements are
numbered by their binary representations (the paper's characteristic 2 instantiation) is a scheme. -/
structure FieldScheme where
  /-- the admissible field sizes -/
  sizes : Set ℕ
  /-- the field on each admissible size -/
  field : ∀ Q ∈ sizes, Field (Fin Q)
  /-- a machine deciding admissibility -/
  decideSize : Machine 1
  /-- a machine computing the sum, on `(Q, a, b)` -/
  addM : Machine 3
  /-- a machine computing the product, on `(Q, a, b)` -/
  mulM : Machine 3
  /-- the exponent of the time bounds -/
  a : ℕ
  /-- admissibility is decided in time polynomial in `log Q` -/
  decideSize_spec : ∀ Q : ℕ, HaltsWithin decideSize ![Nat.bits Q] ⌈(a : ℝ) * (lg Q + 1) ^ a⌉₊ ∧
    (Accepts decideSize ![Nat.bits Q] ↔ Q ∈ sizes)
  /-- addition is computed in time polynomial in `log Q` -/
  addM_spec : ∀ (Q : ℕ) (hQ : Q ∈ sizes) (u v : Fin Q),
    let xs : Fin 3 → List Bool :=
      ![Nat.bits Q, fixedBits (Nat.clog 2 Q) u.val, fixedBits (Nat.clog 2 Q) v.val]
    HaltsWithin addM xs ⌈(a : ℝ) * (lg Q + 1) ^ a⌉₊ ∧
      output addM xs = fixedBits (Nat.clog 2 Q) (@HAdd.hAdd _ _ _
        (@instHAdd _ (field Q hQ).toAdd) u v).val
  /-- multiplication is computed in time polynomial in `log Q` -/
  mulM_spec : ∀ (Q : ℕ) (hQ : Q ∈ sizes) (u v : Fin Q),
    let xs : Fin 3 → List Bool :=
      ![Nat.bits Q, fixedBits (Nat.clog 2 Q) u.val, fixedBits (Nat.clog 2 Q) v.val]
    HaltsWithin mulM xs ⌈(a : ℝ) * (lg Q + 1) ^ a⌉₊ ∧
      output mulM xs = fixedBits (Nat.clog 2 Q) (@HMul.hMul _ _ _
        (@instHMul _ (field Q hQ).toMul) u v).val

end AvoidPlast


