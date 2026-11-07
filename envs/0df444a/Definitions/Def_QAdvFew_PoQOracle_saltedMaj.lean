-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_saltedMaj
-- name    : QAdvFew_PoQOracle_saltedMaj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:19.146568+00:00
-- url     : https://prove2.me/theorems/0d924936-906e-4fee-9d00-2a60e9cc3eea
-- title:
--   Salted majority
-- statement:
--   **Salted majority** is the function
--   $$
--   h^{\mathrm{RO}}(x)=1\iff\bigl|\{y\in\{0,1\}^{|x|}:\mathrm{RO}_{2|x|}(x,y)=1\}\bigr|>2^{|x|}/2,
--   $$
--   the majority of the function $\mathrm{RO}_{2|x|}(x,\cdot)$. It is the hard function of Theorem 4.12.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.5, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The `2n`-bit string `(x, y)` for `|x| = n` and `y ∈ {0,1}^n`. -/
def catBits {n : ℕ} (x : Str) (y : Fin n → Bool) : Fin (2 * n) → Bool := fun i =>
  if h : (i : ℕ) < n then x.getD i false else y ⟨i - n, by omega⟩

/-- **Salted majority** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, §4.5, p. 26 (PDF p. 28)):
`h^{RO}(x) = 1 ⟺ |{y ∈ {0,1}^{|x|} : RO_{2|x|}(x, y) = 1}| > 2^{|x|}/2`, the majority of the
function `RO_{2|x|}(x, ·)`. For `O` sampled from a seed with random oracle `RO`, `h^O := h^{RO}`. -/
def saltedMaj (RO : (t : ℕ) → (Fin t → Bool) → Bool) (x : Str) : Bool :=
  decide (2 ^ x.length < 2 * (Finset.univ.filter
    (fun y : Fin x.length → Bool => RO (2 * x.length) (catBits x y) = true)).card)

end QAdvFew.PoQOracle


