-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_IsAC0
-- name    : QAdvFew_PoQOracle_IsAC0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:26.240351+00:00
-- url     : https://prove2.me/theorems/9f40ea76-2474-4941-b4b2-dab38936d368
-- title:
--   $\mathsf{AC}^0(S,d)$
-- statement:
--   $\mathsf{AC}^0(S,d)$ is the class of Boolean circuits of size at most $S$ and depth at most $d$ using unbounded fan-in AND and OR gates and fan-in-one NOT gates, with no parity and no oracle gates.
--
--   **Formalization Note** Size is description length and constants are allowed.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.9, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Circuit

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Membership in `AC0(S, d)` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.9, p. 13 (PDF p. 15)): a Boolean circuit of size at
most `S` and depth at most `d` with unbounded fan-in AND and OR gates and fan-in-one NOT gates (no
parity and no oracle gates).

**Formalization Note** Size is description length (`Circuit.size`); constants are allowed as
inputs of depth `0`. -/
def IsAC0 {ι : Type} [IndexCode ι] (C : Circuit ι) (S : ℝ) (d : ℕ) : Prop :=
  C.NoXor ∧ C.NoOracle ∧ (C.size : ℝ) ≤ S ∧ C.depth ≤ d

end QAdvFew.PoQOracle


