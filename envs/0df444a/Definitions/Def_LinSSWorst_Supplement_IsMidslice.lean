-- Prove2me | Definitions.Def_LinSSWorst_Supplement_IsMidslice
-- name    : LinSSWorst_Supplement_IsMidslice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:45:34.461406+00:00
-- url     : https://prove2.me/theorems/c2c0f8e0-fe4c-4343-a5c2-110af53d9019
-- title:
--   $\delta$-midslice access structures (Definition A.7)
-- statement:
--   For a constant $\delta\in(0,1/2)$, the **$\delta$-midslice** of an $n$-party access structure $f$ is
--   $$F(x)=\begin{cases}0 & \mathrm{wt}(x)<a,\\ f(x) & a\le\mathrm{wt}(x)\le b,\\ 1 & \mathrm{wt}(x)>b,\end{cases}\qquad a=\lceil(\tfrac12-\delta)n\rceil,\ b=\lfloor(\tfrac12+\delta)n\rfloor.$$
--   A **$\delta$-midslice access structure** is one obtained this way from some $n$-party access structure.
--
--   Midslices are the middle part $f_{\mathrm{mid}}$ of the decomposition used to prove Theorems 1.5 and 1.6.
--
--   **Formalization Note** $a$ and $b$ are `Nat.ceil` and `Nat.floor` of nonnegative reals for $\delta\in(0,1/2)$. When $a>b$ the middle range is empty.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Definition A.7, pp.30–31; p.18

import Mathlib
import Definitions.Def_LinSSWorst_Supplement_IsUpslice

namespace LinSSWorst.Supplement

/-- The **`δ`-midslice** of an `n`-party access structure `f` (Definition A.7, pp.30–31; p.18), from O. Nir,
*Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of
2026-11-02, sha256 5521cfdb…): its `(a : b)`-multislice with `a = ⌈(1/2 − δ) n⌉` and `b = ⌊(1/2 + δ) n⌋`,
that is `F(x) = 0` if `wt(x) < a`, `F(x) = f(x)` if `wt(x) ∈ [a, b]`, and `F(x) = 1` if `wt(x) > b`.

**Formalization Note.** `a` and `b` are `Nat.ceil` and `Nat.floor` of the real numbers `(1/2 − δ) n` and
`(1/2 + δ) n`; for `δ ∈ (0, 1/2)`, the only range used, both are nonnegative, so these are the integer
ceiling and floor of the page. When `a > b` (possible for small `n`) the middle range is empty and the
cases `wt(x) < a`, `wt(x) > b` cover every `x`, as in Definition A.7's formula. -/
noncomputable def midslice {n : ℕ} (δ : ℝ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  if wt x < ⌈(1 / 2 - δ) * (n : ℝ)⌉₊ then false
  else if wt x ≤ ⌊(1 / 2 + δ) * (n : ℝ)⌋₊ then f x
  else true

/-- A **`δ`-midslice access structure** (function) over `n` parties (Definition A.7, p.31; p.18): the
`δ`-midslice of some `n`-party access structure `f`. -/
def IsMidslice {n : ℕ} (δ : ℝ) (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ f : (Fin n → Bool) → Bool, IsAccessStructure f ∧ F = midslice δ f

end LinSSWorst.Supplement


