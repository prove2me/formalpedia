-- Prove2me | Definitions.Def_ParityDegreeDepth_Main_Supplement_ThresholdWeight
-- name    : ParityDegreeDepth_Main_Supplement_ThresholdWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:48:24.506194+00:00
-- url     : https://prove2.me/theorems/acac5681-c041-46f5-880d-74f7d6c1bd06
-- title:
--   Margin-one sign witnesses and the threshold weight $W(f)$
-- statement:
--   Let $V_n=\mathbb F_2^n$ and let $f:V_n\to\{-1,1\}$ be a sign function. A real function $g:V_n\to\mathbb R$ is a **margin-one sign witness** for $f$ when
--
--   $$
--   f(x)\,g(x)\ge 1\qquad\text{for every }x\in V_n .
--   $$
--
--   The witness $g$ is an arbitrary real function: it need not be sign-valued, integer-valued or of low degree. The **threshold weight** of $f$ is the least spectral norm of a witness,
--
--   $$
--   W(f)=\inf\bigl\{\|\widehat g\|_1 : g \text{ a margin-one sign witness for } f\bigr\},
--   $$
--
--   where $\|\widehat g\|_1=\sum_{\xi}|\widehat g(\xi)|$ is the sum of the absolute normalized Walsh coefficients $\widehat g(\xi)=2^{-n}\sum_x g(x)(-1)^{\xi\cdot x}$, as in the mission's published operational context.
--
--   Taking $g=f$ shows $W(f)\le\|\widehat f\|_1$, so the threshold weight refines the spectral norm in the depth bounds of the mission.
--
--   **Formalization Note** $W$ is the real infimum (`sInf`) of the set of spectral norms of witnesses. For a $\pm1$-valued $f$ this set is nonempty and bounded below by $0$; the paper remarks that the minimum is attained, but attainment is not built into the definition. Functions are real-valued, so a function with no witness (one vanishing somewhere) gets the default value $0$; every statement that uses $W$ assumes $f$ is $\pm1$-valued.
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, SHA-256 02e6bad861054e233c6877aa352d0014cf84172cde536433dd6e24588277680b, Definition C.1, PDF p. 25 (printed p. 24); display defining W(f), PDF p. 4 (printed p. 3).

import Mathlib
import Definitions.Def_ParityDegreeDepth_Main_Context

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main.Supplement

open ParityDegreeDepth.Main

/-- Zhang, STOC 2027 submission #798, Definition C.1 (PDF p. 25, printed p. 24):
`g` is a margin-one sign witness for `f` when `f x * g x ≥ 1` at every point.
The witness `g` is an arbitrary real function. -/
def IsSignWitness {n : ℕ} (f g : Vec n (ZMod 2) → ℝ) : Prop :=
  ∀ x, 1 ≤ f x * g x

/-- Threshold weight `W(f)` (Definition C.1; also PDF p. 4, printed p. 3): the infimum of the
spectral norm `‖ĝ‖₁` over all real margin-one sign witnesses `g` of `f`.
For a `±1`-valued `f` the set is nonempty (`g = f`) and bounded below by `0`; attainment of the
minimum is a remark of the paper and is not built into the definition. For an `f` with no
witness (e.g. `f x = 0` somewhere) Lean's `sInf ∅ = 0`; every statement using `W` assumes
`f` is `±1`-valued. -/
def thresholdWeight {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ g : Vec n (ZMod 2) → ℝ, IsSignWitness f g ∧ spectralNorm g = w}

end ParityDegreeDepth.Main.Supplement


