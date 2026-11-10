-- Prove2me | Definitions.Def_NearOptOWF_NmCAPPInst
-- name    : NearOptOWF_NmCAPPInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:34.492852+00:00
-- url     : https://prove2.me/theorems/5fd465d2-a828-46ab-97e1-73138ab7ad7d
-- title:
--   Instance of nmCAPP
-- statement:
--   An instance of the **non-deterministic multiplicative circuit approximation probability problem** (nmCAPP): a non-deterministic circuit $C : \{0,1\}^n \times \{0,1\}^w \to \{0,1\}$, a threshold $\beta$ and an integer $k = 1/\epsilon$. Only instances with $\beta \in [2^n] = \{1, \dots, 2^n\}$ and $k \ge 1$ are yes- or no-instances.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit

namespace NearOptOWF

/-- An **instance of nmCAPP** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10): "Given: a non-deterministic
circuit `C : {0,1}ⁿ → {0,1}^w → {0,1}`, a `β ∈ [2ⁿ]` and an `1/ε ∈ ℕ`"): the lengths `n`, `w`, a
circuit `C` on `n + w` inputs (the input `x` followed by the non-deterministic bits `u`), the threshold
`β` and `k = 1/ε`.

**Formalization Note** The conditions `β ∈ [2ⁿ]` and `k ≥ 1` are part of the yes and no sets
(`nmCAPPYes`, `nmCAPPNo`); a tuple violating them is in neither (a promise problem). -/
structure NmCAPPInst where
  /-- the input length `n` -/
  n : ℕ
  /-- the number `w` of non-deterministic bits -/
  w : ℕ
  /-- the circuit `C(x, u)` -/
  C : KarpLiptonOM.Circuit (n + w)
  /-- the threshold `β` -/
  β : ℕ
  /-- `k = 1/ε` -/
  k : ℕ

end NearOptOWF


