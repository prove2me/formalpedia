-- Prove2me | Definitions.Def_MatrixSpencer_GoodPartial
-- name    : MatrixSpencer_GoodPartial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:03.170922+00:00
-- url     : https://prove2.me/theorems/7e01cef4-ac53-492d-80a5-97c9172b67e5
-- title:
--   A partial coloring within the bound
-- statement:
--   For a constant $C$, an instance and a list $x$ of rationals: the list has $n$ entries, $x\in[-1,1]^n$, at least $n/2$ coordinates equal $\pm1$, and with $\sigma=\sqrt{\|\sum_iA_i^2\|}$,
--   $$\Bigl\|\sum_{i=1}^n(x_i-x_i^{(0)})A_i\Bigr\|\le C\sigma\sqrt{\max\{1,\log(d/n)\}}.$$
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11

import Mathlib
import Definitions.Def_MatrixSpencer_PartialInst
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **A good output of the partial-coloring algorithm.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11, with `σ = √‖∑ᵢAᵢ²‖`.

The output `m` is a list of `n` rationals `x` with `x ∈ [−1, 1]ⁿ`, at least `n/2` coordinates equal
to `±1`, and `‖∑ᵢ (xᵢ − xᵢ⁽⁰⁾)Aᵢ‖ ≤ Cσ√max{1, log(d/n)}`. -/
def GoodPartial (C : ℝ) (I : PartialInst) (m : List ℚ) : Prop :=
  open Classical in
  m.length = I.inst.n ∧
    (∀ i : Fin I.inst.n, |m.getD i 0| ≤ 1) ∧
    I.inst.n ≤ 2 * (Finset.univ.filter fun i : Fin I.inst.n => |m.getD i 0| = 1).card ∧
    ‖∑ i : Fin I.inst.n,
        (((m.getD i 0 - I.x0 i : ℚ) : ℝ)) • (I.inst.A i).map (fun q : ℚ => (q : ℝ))‖ ≤
      C * √‖∑ i : Fin I.inst.n, ((I.inst.A i).map (fun q : ℚ => (q : ℝ))) ^ 2‖ *
        √(max 1 (Real.log ((I.inst.d : ℝ) / I.inst.n)))

end MatrixSpencer


