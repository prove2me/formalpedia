-- Prove2me | Definitions.Def_SubexpPermanent_Main_Contraction
-- name    : SubexpPermanent_Main_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:00:14.338689+00:00
-- url     : https://prove2.me/theorems/f38d0238-13f5-40e2-91b0-d41aa0c3b9f9
-- title:
--   The change of variables of Fact 4.7: $I=[1/(1+\gamma),1]$, $\psi(q)=\log((2-q)/q)$, $s=\lceil\sqrt{1+4\gamma}\rceil$, $\rho=1-1/s$
-- statement:
--   For a budget $\gamma\ge1$ let $I=[1/(1+\gamma),1]$ (`unmatchedInterval γ`), and define
--   $$\psi(q)=\log\frac{2-q}{q},\qquad s=\big\lceil\sqrt{1+4\gamma}\,\big\rceil,\qquad \rho=1-\frac1s .$$
--
--   **Formalization Note.** $s$ is a natural number (`Nat.ceil`). `psi` is defined on all reals; every statement applies it only on $I$, where $(2-q)/q>0$.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 15, Fact 4.7; p. 25 (§7)

import Mathlib

namespace SubexpPermanent.Main

/-! # The change of variables of Fact 4.7 (Kudria–Luo–Majid, p. 15) -/

/-- `I = [1/(1 + γ), 1]`, the range of the unmatched probabilities under budget `γ`. -/
def unmatchedInterval (γ : ℝ) : Set ℝ :=
  Set.Icc (1 / (1 + γ)) 1

/-- `ψ(q) = log((2 − q)/q)`. -/
noncomputable def psi (q : ℝ) : ℝ :=
  Real.log ((2 - q) / q)

/-- `s = ⌈√(1 + 4γ)⌉`. -/
noncomputable def sCeil (γ : ℝ) : ℕ :=
  ⌈Real.sqrt (1 + 4 * γ)⌉₊

/-- `ρ = 1 − 1/s`. -/
noncomputable def rhoContr (γ : ℝ) : ℝ :=
  1 - 1 / (sCeil γ : ℝ)

end SubexpPermanent.Main


