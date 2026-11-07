-- Prove2me | Definitions.Def_PRUPermLayer_outDist
-- name    : PRUPermLayer_outDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:18.449771+00:00
-- url     : https://prove2.me/theorems/725babf2-0cbd-4e38-87a9-7443d67ba047
-- title:
--   Output distribution $p_x = |\langle x|U|0^n\rangle|^2$
-- statement:
--   For an $n$-qubit unitary $U$, measuring $U|0^n\rangle$ in the computational basis gives outcome $x \in [N]$ with probability
--   $$
--   p_x = |\langle x | U | 0^n\rangle|^2 .
--   $$
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace PRUPermLayer

/-- The output distribution `p_x = |⟨x|U|0ⁿ⟩|²` of a computational-basis measurement of
`U|0ⁿ⟩` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.19 (PDF p.21)).

**Formalization Note** `|0ⁿ⟩` is the label `QAlgorithms.bitsEquivFin n (fun _ => false)` of the
all-zeros string. -/
noncomputable def outDist {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (x : Fin (2 ^ n)) : ℝ :=
  ‖U x (QAlgorithms.bitsEquivFin n fun _ => false)‖ ^ 2

end PRUPermLayer


