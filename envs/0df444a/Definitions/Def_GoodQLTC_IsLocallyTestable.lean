-- Prove2me | Definitions.Def_GoodQLTC_IsLocallyTestable
-- name    : GoodQLTC_IsLocallyTestable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:53.735063+00:00
-- url     : https://prove2.me/theorems/9bdd2926-f2f7-4a42-a07a-cbf3235fffcd
-- title:
--   Quantum local testability with soundness $\sigma$ (Definition 3.1)
-- statement:
--   For an integer $w\ge1$ and $\sigma>0$, a CSS code with its specified check list is **$w$-locally testable with soundness $\sigma$** if every check has weight at most $w$ and
--   $$
--   H\succeq\frac{\sigma}{N}D_Q, \tag{3.3}
--   $$
--   i.e. $H-\frac{\sigma}{N}D_Q$ is positive semidefinite on the whole Hilbert space. The module also defines `IsSound` (the operator inequality alone) and `qubitDegree` (the number of listed checks acting on a qubit).
--
--   Soundness says that every state is rejected with probability at least $\sigma/N$ times its distance from the code.
--
--   **Formalization Note** The Loewner order is `Matrix.PosSemidef` of the difference; `1 ≤ w` and `0 < σ` are part of the predicate.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Definition 3.1, Equation (3.3), p.14 (PDF p.17); qubit incidence: Main Theorem, p.3 and proof of Theorem 4.12, p.33

import Mathlib
import Definitions.Def_GoodQLTC_testHam
import Definitions.Def_GoodQLTC_distOp
open scoped ComplexOrder

namespace GoodQLTC

/-- **Soundness** `H ⪰ (σ/N) D_Q` of a CSS code with its full check list, Gay–Jeronimo,
arXiv:2609.20780 (held version), Definition 3.1, Equation (3.3), p.14: the operator
`H − (σ/N) D_Q` is positive semidefinite on all of `H_N`.

**Formalization Note.** `N = |ι|`; the Loewner order is `Matrix.PosSemidef` of the difference, on
the whole Hilbert space (not on basis states). -/
def IsSound {ι κX κZ : Type} [Fintype ι] [DecidableEq ι] [Fintype κX] [Fintype κZ] (σ : ℝ)
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : Prop :=
  (testHam HX HZ - (((σ / (Fintype.card ι : ℝ) : ℝ) : ℂ)) • distOp HX HZ).PosSemidef

/-- **Quantum local testability**, Gay–Jeronimo, arXiv:2609.20780 (held version), Definition 3.1,
p.14: for an integer `w ≥ 1` and `σ > 0`, the code with its specified check list is `w`-locally
testable with soundness `σ` if every check has weight at most `w` and `H ⪰ (σ/N) D_Q`.

**Formalization Note.** The weight of the check `X^{h}` or `Z^{h}` is the Hamming weight of the row
`h`. The conditions `1 ≤ w` and `0 < σ` of the definition's preamble are part of the predicate. -/
def IsLocallyTestable {ι κX κZ : Type} [Fintype ι] [DecidableEq ι] [Fintype κX] [Fintype κZ]
    (w : ℕ) (σ : ℝ) (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : Prop :=
  1 ≤ w ∧ 0 < σ ∧ (∀ a, hammingNorm (HX a) ≤ w) ∧ (∀ b, hammingNorm (HZ b) ≤ w) ∧
    IsSound σ HX HZ

/-- The number of listed checks incident to the qubit `i`: the X-checks and Z-checks whose row has
a nonzero entry at `i` (arXiv:2609.20780, Main Theorem, p.3: "every qubit belongs to at most `w`
checks"; proof of Theorem 4.12, p.33: "the sum of their column weights at each qubit"). -/
def qubitDegree {ι κX κZ : Type} [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) (i : ι) : ℕ :=
  (Finset.univ.filter fun a => HX a i ≠ 0).card + (Finset.univ.filter fun b => HZ b i ≠ 0).card

end GoodQLTC


