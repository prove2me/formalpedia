-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Supplement_AppendixPacking
-- name    : SublinearChoresMMS_Disposal_Supplement_AppendixPacking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:37.454339+00:00
-- url     : https://prove2.me/theorems/a4d3fed9-910c-44b9-b172-3df73f4699c3
-- title:
--   Appendix B parameters and packing every representative
-- statement:
--   For $n\ge2$ and $1\le k<n$, Appendix B uses
--
--   $$q=\left\lfloor(n^2/\log n)^{1/3}\right\rfloor,\qquad L=\left\lceil(n-k)/q+C_5\log n\right\rceil.$$
--
--   An all-representative packing labels each of the $m/q$ representatives, including the first, by one of $L$ bins. The load of a bin is the sum of its representative costs. The change count counts adjacent distinct labels along the complete representative sequence. Empty and singleton sequences have zero changes. There is no exclusion label or assumed load bound.
--
--   The explicit rate used by the companion theorems is
--
--   $$f(n)=n^{2/3}(\log(2n))^{2/3}.$$
--
--   **Formalization Note** Lemma B.1 ensures $q>0$ beyond an absolute threshold and assumes $q\mid m$. The published representative-cost formula is reused. The rate is only used with $n\ge1$; then $\log(2n)>0$.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Appendix B.1 parameters, printed p. 28 / PDF p. 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf Lemma B.1, printed p. 29 / PDF p. 30; equation (3), printed p. 31 / PDF p. 32.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing

noncomputable section

namespace SublinearChoresMMS.Disposal.Supplement

attribute [local instance] Classical.propDecidable

/-- Appendix B.1, printed 28 / PDF 29. Only used with n≥2 and q>0. -/
def appendixBlockSize (n : ℕ) : ℕ :=
  ⌊Real.rpow ((n : ℝ) ^ 2 / Real.log n) (1 / 3 : ℝ)⌋₊

def appendixBinCount (C₅ : ℝ) (n k : ℕ) : ℕ :=
  ⌈((n - k : ℕ) : ℝ) / appendixBlockSize n + C₅ * Real.log n⌉₊

/-- All representatives, including block zero, have a bin; there is no exclusion label. -/
abbrev AllPacking (m q L : ℕ) := Fin (m / q) → Fin L

def allBinLoad {n m q L : ℕ} (c : Cost n m) (i : Fin n)
    (p : AllPacking m q L) (t : Fin L) : ℝ :=
  ∑ r, if p r = t then representativeCost c i q r else 0

/-- Number of changes along all representatives; zero for zero or one representative. -/
def labelChanges {m q L : ℕ} (p : AllPacking m q L) : ℕ :=
  (Finset.univ.filter (fun r : Fin (m / q) =>
    ∃ h : 0 < r.val, p r ≠ p ⟨r.val - 1, by omega⟩)).card

/-- The explicit rate in (3), printed 31 / PDF 32, extended to small n by log(2n).
It is used only for n≥1 in the companion theorems. -/
def appendixRate (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (2 / 3 : ℝ) * Real.rpow (Real.log (2 * (n : ℝ))) (2 / 3 : ℝ)

end SublinearChoresMMS.Disposal.Supplement


