-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_IsAC0Xor
-- name    : QAdvFew_PoQOracle_IsAC0Xor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:35.878277+00:00
-- url     : https://prove2.me/theorems/5079b2a2-8d35-46fb-bb19-dc325163f5c9
-- title:
--   $\mathsf{AC}^0[\oplus](S,d)$
-- statement:
--   $\mathsf{AC}^0[\oplus](S,d)$ also allows unbounded fan-in parity gates: Boolean circuits without oracle gates, of size at most $S$ and depth at most $d$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.9, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Circuit

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Membership in `AC0[⊕](S, d)` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.9, p. 13 (PDF p. 15): "The class `AC0[⊕](S, d)` also
allows unbounded fan-in parity gates"): a Boolean circuit without oracle gates, of size at most `S`
and depth at most `d`.

**Formalization Note** Size is description length (`Circuit.size`). -/
def IsAC0Xor {ι : Type} [IndexCode ι] (C : Circuit ι) (S : ℝ) (d : ℕ) : Prop :=
  C.NoOracle ∧ (C.size : ℝ) ≤ S ∧ C.depth ≤ d

end QAdvFew.PoQOracle


