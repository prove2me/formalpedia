-- Prove2me | Definitions.Def_LowErrExt_seededOfMachine
-- name    : LowErrExt_seededOfMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:37.682284+00:00
-- url     : https://prove2.me/theorems/67a77b59-ce05-422b-866d-1b315eaeb5c0
-- title:
--   The seeded function $\mathbb F_2^n\times[D]\to\mathbb F_2^m$ computed by a machine
-- statement:
--   Given a function $F$ on tuples of bit strings and parameters $k,b,m,D$, the seeded function $\mathrm{lsCond}:\mathbb F_2^n\times[D]\to\mathbb F_2^m$ is
--   $$\mathrm{lsCond}(x,y)=\text{the first } m \text{ bits of } F(1^k,1^b,1^y,x),$$
--   with $x$ written as a bit string and the seed $y\in\{0,\dots,D-1\}$ in unary. It is how Corollary 3.16's explicit condenser is read off one uniform machine.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Corollary 3.16, p.25

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime

namespace LowErrExt

/-- **A vector of `𝔽₂ⁿ` as a bit string** (`1 ↦ true`, `0 ↦ false`). -/
def bitsOf {n : ℕ} (x : Fin n → ZMod 2) : List Bool :=
  List.ofFn fun i => decide (x i = 1)

/-- **The seeded function `𝔽₂ⁿ × [D] → 𝔽₂ᵐ` computed by a machine with parameters `k`, `b`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Corollary 3.16, p.25 ("an explicit function lsCond : Fn2 × [D] → Fm2").

`seededOfMachine F k b x y` runs `F` on the words `1ᵏ`, `1ᵇ`, `1ʸ` and the bits of `x`, and reads the
first `m` output bits as a vector of `𝔽₂ᵐ`.

**Formalization Note.** The parameters `k`, `b` and the seed `y ∈ [D] = {0, …, D − 1}` are given in
unary; the input length `n` is the length of `x`. Statements using this map also assert that the
output has exactly `m` bits. -/
def seededOfMachine (F : List (List Bool) → List Bool) {n : ℕ} (k b m D : ℕ) :
    (Fin n → ZMod 2) → Fin D → (Fin m → ZMod 2) :=
  fun x y i =>
    if listOut m (F [List.replicate k true, List.replicate b true, List.replicate y true, bitsOf x]) i
    then 1 else 0

end LowErrExt


