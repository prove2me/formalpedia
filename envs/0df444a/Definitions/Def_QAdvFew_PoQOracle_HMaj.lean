-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_HMaj
-- name    : QAdvFew_PoQOracle_HMaj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:30.662316+00:00
-- url     : https://prove2.me/theorems/f92c6b5a-d64b-4f9c-9921-551cea39bf2b
-- title:
--   Parallel repetition of salted majority
-- statement:
--   The parallel repetition $H^{\mathrm{RO}}_r(x_1,\dots,x_r)=(h^{\mathrm{RO}}(x_1),\dots,h^{\mathrm{RO}}(x_r))$ of salted majority, for $x_1,\dots,x_r\in\{0,1\}^n$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.5, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_saltedMaj

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The parallel repetition `H^{RO}_r(x₁, …, x_r) = (h^{RO}(x₁), …, h^{RO}(x_r))` of salted majority
(Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
§4.5, p. 26 (PDF p. 28)), for `x₁, …, x_r ∈ {0,1}^n`. -/
def HMaj (RO : (t : ℕ) → (Fin t → Bool) → Bool) {r n : ℕ} (xs : Fin r → Fin n → Bool) :
    Fin r → Bool :=
  fun i => saltedMaj RO (List.ofFn (xs i))

end QAdvFew.PoQOracle


