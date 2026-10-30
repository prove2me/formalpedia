-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Gamma
-- name    : RamanujanLostNotebook_PartII_ch12_ch12Gamma
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:20:45.32697+00:00
-- url     : https://prove2.me/theorems/46bc7e0a-29c9-4f06-9db0-9e79bec2a58a
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12Gamma
-- statement:
--   The integer coefficient γ_n of 1/R(z), where R(z)=1−504∑_{k≥1}σ₅(k)z^k.
--   A finite geometric expansion is exact in degree n because its base polynomial has
--   zero constant term. This is the coefficient of q^(2n) in 1/R(q²), p.313.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Sigma5

namespace RamanujanLostNotebook.PartII

/-- The integer coefficient γ_n of 1/R(z), where R(z)=1−504∑_{k≥1}σ₅(k)z^k.
A finite geometric expansion is exact in degree n because its base polynomial has
zero constant term. This is the coefficient of q^(2n) in 1/R(q²), p.313. -/
noncomputable def ch12Gamma (n : ℕ) : ℤ :=
  (∑ j ∈ Finset.range (n + 1),
    (504 * ∑ k ∈ Finset.Icc 1 n,
      Polynomial.C (ch12Sigma5 k) * (Polynomial.X : Polynomial ℤ) ^ k) ^ j).coeff n

end RamanujanLostNotebook.PartII


