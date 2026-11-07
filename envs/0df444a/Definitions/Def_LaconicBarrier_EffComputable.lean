-- Prove2me | Definitions.Def_LaconicBarrier_EffComputable
-- name    : LaconicBarrier_EffComputable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:30.326452+00:00
-- url     : https://prove2.me/theorems/334f6827-6899-4e2d-b0ce-ea2c8ab405ed
-- title:
--   Efficiently computable real quantities
-- statement:
--   A real quantity $v(i)$ depending on an index $i$ is **efficiently computable relative to a bound $B$** if one machine, given the encoded index and $1^N$, outputs a rational $q$ (sign, binary numerator and denominator) with
--   $$
--   |q - v(i)| \le \frac{1}{N+1}
--   $$
--   within $(B(i) + N + N_i + 2)^c$ steps. A real constant $a$ (a baseline $c$ or $c_0$) is efficiently computable ($\mathrm{EffReal}(a)$) if it is approximable in this way from $1^N$ in time polynomial in $N$.
--
--   The paper assumes its baselines and error bounds are efficiently computable without fixing the notion; arbitrary-precision approximation is the standard one, and it is what a verifier needs to compare an acceptance probability with a threshold.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.1, p.15 (standing assumption: "baselines, constants, and error bounds are efficiently computable")

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

open KarpLiptonOM

/-- The code of a rational number: its sign bit, and the binary digits (`Nat.bits`, least
significant first) of the absolute value of its numerator and of its denominator, as a tuple. -/
def ratCode (q : ℚ) : List Bool :=
  QAdvFew.PoQOracle.tup [[decide (q < 0)], Nat.bits q.num.natAbs, Nat.bits q.den]

/-- A real-valued quantity `v(i)` is **efficiently computable** relative to a bound `B`: one machine,
given the encoded index `i` and `1^N`, outputs (the code of) a rational within `1/(N+1)` of `v(i)`
within `(B(i) + N + |i| + 2)^c` steps (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript
sha256 1af78662…), §4.1.1, p.15: "baselines, constants, and error bounds are efficiently
computable").

**Formalization Note** The paper does not fix the notion for real numbers; arbitrary-precision
approximation in time polynomial in the precision and the bound is the standard one. -/
def EffComputable {ι : Type*} (enc : ι → List (List Bool)) (v : ι → ℝ) (B : ι → ℕ) : Prop :=
  ∃ (M : OracleTM) (c : ℕ), ∀ (i : ι) (N : ℕ), ∃ q : ℚ, |(q : ℝ) - v i| ≤ 1 / ((N : ℝ) + 1) ∧
    RunsWithin M (enc i ++ [unary N]) (ratCode q)
      ((B i + N + (tupleEnc (enc i)).length + 2) ^ c)

/-- An efficiently computable real constant (a baseline `c`, `c₀`): approximable to within
`1/(N+1)` from `1^N` in time polynomial in `N` (Jain, Mathialagan, Roy, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1.1, p.15). -/
def EffReal (a : ℝ) : Prop :=
  EffComputable (ι := Unit) (fun _ => []) (fun _ => a) (fun _ => 0)

end LaconicBarrier


