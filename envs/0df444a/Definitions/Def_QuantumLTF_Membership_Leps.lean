-- Prove2me | Definitions.Def_QuantumLTF_Membership_Leps
-- name    : QuantumLTF_Membership_Leps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:51.892086+00:00
-- url     : https://prove2.me/theorems/1f0d13d4-db2a-4150-b2c5-3135d3da73eb
-- title:
--   $L_\epsilon=2^{\lceil\log_2(20T_\epsilon)\rceil}$
-- statement:
--   $L_\epsilon:=2^{\lceil\log_2(20T_\epsilon)\rceil}$, the half-width of the interval of the boundary search.
--
--   **Formalization Note** For $0<\epsilon\le1/2$ one has $T_\epsilon>1$, so the natural-number ceiling agrees with the paper's.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Teps

namespace QuantumLTF.Membership

/-- **`L_ϵ`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22): `L_ϵ := 2^{⌈log₂(20 T_ϵ)⌉}`.

**Formalization Note.** For `0 < ϵ ≤ 1/2`, `T_ϵ ≥ √(2 log 2) > 1`, so `20 T_ϵ > 1` and `⌈·⌉₊` is the
paper's ceiling. -/
noncomputable def Leps (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ ⌈Real.logb 2 (20 * Teps ε)⌉₊

end QuantumLTF.Membership


