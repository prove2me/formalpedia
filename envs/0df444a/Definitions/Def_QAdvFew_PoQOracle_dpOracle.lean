-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_dpOracle
-- name    : QAdvFew_PoQOracle_dpOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:53.470018+00:00
-- url     : https://prove2.me/theorems/e0a5cb85-9104-4081-8bbd-a55dca499cc8
-- title:
--   An algorithm as the oracle of oracle gates
-- statement:
--   An algorithm $\mathcal A:(\{0,1\}^n)^t\to\{0,1\}^t$ as the oracle of the oracle gates of $C^{\mathcal A}$: the query consisting of the $nt$ bits of $(x_1,\dots,x_t)$ followed by $1^i0$, $i<t$, is answered by the $i$-th output bit of $\mathcal A(x_1,\dots,x_t)$, and every other query by $0$.
--
--   **Formalization Note** An oracle gate returns one bit, so a circuit asks for all $t$ output bits with $t$ gates.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 3.12, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_splitTag
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- An algorithm `A : ({0,1}^n)^t → {0,1}^t` as the oracle of oracle gates (Goldin, Lombardi,
Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 3.12,
p. 15 (PDF p. 17): "an `AC0` circuit `C` with oracle gates", `C^A`): the query consisting of the
`n · t` bits of `(x₁, …, x_t)` followed by `1^i 0` with `i < t` is answered by the `i`-th output bit
of `A(x₁, …, x_t)`; every other query by `0`.

**Formalization Note** An oracle gate returns one bit, so the `t` output bits of `A` are asked for
one at a time; a circuit asks for all of them with `t` gates. -/
def dpOracle (n t : ℕ) (A : (Fin t → Fin n → Bool) → (Fin t → Bool)) : Oracle := fun s =>
  if n * t ≤ s.length then
    match splitTag (s.drop (n * t)) with
    | some (i, []) =>
      if h : i < t then A (fun j k => s.getD ((j : ℕ) * n + k) false) ⟨i, h⟩ else false
    | _ => false
  else false

end QAdvFew.PoQOracle


