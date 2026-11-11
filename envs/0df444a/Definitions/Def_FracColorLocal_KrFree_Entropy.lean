-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Entropy
-- name    : FracColorLocal_KrFree_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:33.602655+00:00
-- url     : https://prove2.me/theorems/41e713a4-aad3-4abf-b248-9ca24581642b
-- title:
--   Total variation distance, relative entropy (with +∞) and weighted entropy H_s
-- statement:
--   For real vectors $p,q$ on a finite set:
--
--   $$\|p-q\|_{\mathrm{TV}}=\tfrac12\sum_y|p(y)-q(y)|,\qquad \mathrm{KL}(p\|q)=\sum_y p(y)\log\frac{p(y)}{q(y)},$$
--
--   where terms with $p(y)=0$ are zero, and $\mathrm{KL}(p\|q)=+\infty$ if $p(y)>0=q(y)$ for some $y$. For positive weights $s$ on a finite set $A$, $H_s(p)=\sum_{y\in A}p(y)\log\frac{s(y)}{p(y)}$, zero terms being zero.
--
--   **Formalization Note** `klDiv` takes values in `EReal` (value `⊤` exactly in the support-failure case, otherwise the real sum). Zero terms are zero automatically, since `0 * Real.log _ = 0`.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 37 (PDF 38), §8.5

import Mathlib

namespace FracColorLocal.KrFree

variable {ι : Type*} [Fintype ι]

/-- `‖p - q‖_TV := (1/2) ∑_y |p(y) - q(y)|`. -/
noncomputable def tvDist (p q : ι → ℝ) : ℝ := (∑ y, |p y - q y|) / 2

/-- `KL(p ‖ q) := ∑_y p(y) log(p(y)/q(y))`, terms with `p(y) = 0` being zero, and `+∞` when
`p(y) > 0 = q(y)` for some `y` (§8.5). -/
noncomputable def klDiv (p q : ι → ℝ) : EReal := by
  classical
  exact if ∃ y, 0 < p y ∧ q y = 0 then ⊤
    else ((∑ y, p y * Real.log (p y / q y) : ℝ) : EReal)

/-- `H_s(p) := ∑_{y ∈ A} p(y) log(s(y)/p(y))` on the finite set `A`, zero terms being zero (§8.5). -/
noncomputable def entropyOn {V : Type*} (A : Finset V) (s p : V → ℝ) : ℝ :=
  ∑ y ∈ A, p y * Real.log (s y / p y)

end FracColorLocal.KrFree


