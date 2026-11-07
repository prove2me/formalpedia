-- Prove2me | Definitions.Def_PRUPermLayer_piEqTwo
-- name    : PRUPermLayer_piEqTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:06.542224+00:00
-- url     : https://prove2.me/theorems/18538392-9c21-4c61-baad-8b36304ec184
-- title:
--   Equality projector $\Pi_{\mathrm{eq}} = \sum_x |x\rangle\langle x|\otimes|x\rangle\langle x|$
-- statement:
--   On two registers with $N$ basis labels,
--   $$
--   \Pi_{\mathrm{eq}} = \sum_{x\in[N]} |x\rangle\langle x| \otimes |x\rangle\langle x| ,
--   $$
--   whose range is the span of the states with equal labels in the two registers.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)

import Mathlib

namespace PRUPermLayer

/-- The equality projector `Π_eq = Σₓ |x⟩⟨x| ⊗ |x⟩⟨x|` on two registers with `N` labels
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)). -/
def piEqTwo (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.diagonal fun x => if x.1 = x.2 then 1 else 0

end PRUPermLayer


