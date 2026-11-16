-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Supplement_Approximation
-- name    : GaussProcSparsify_Optimal_Supplement_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:19:13.652609+00:00
-- url     : https://prove2.me/theorems/d732fea4-d9fb-44d0-8b10-4f456579a913
-- title:
--   Zero padding and normalized radial affine maxima
-- statement:
--   For $t\in\mathbb R^n$ and $m\ge n$, zero padding is the vector $(t,0_{m-n})\in\mathbb R^m$, with the first $n$ coordinates equal to $t$ and all remaining coordinates zero. For a nonempty finite indexed family of directions $u_j\in\mathbb R^n$ and intercepts $a_j\in\mathbb R$, define
--   $$h(g)=\max_{j<m}\left(a_j+\frac{\langle g,u_j\rangle}{\sqrt n}\right).$$
--   The maximum is used only with $m>0$ and $n>0$. These are the concrete objects in the centered clause of Corollary 14 and the radial lower bound of Lemma 20. The maximum is implemented by a real supremum of a nonempty finite range; it is never used on the empty range. Zero padding is used only with $n\le m$.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Corollary 14, PDF p. 22 (printed p. 21); Lemma 20, PDF p. 31 (printed p. 30), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Concatenate zeros, as in Corollary 14, PDF p. 22. Used with n ≤ m. -/
def zeroPad {n m : ℕ} (t : Vec n) : Vec m :=
  WithLp.toLp 2 (fun i : Fin m => if h : i.val < n then t ⟨i.val, h⟩ else 0)

/-- Affine maximum of Lemma 20, PDF p. 31. The statement requires m > 0. -/
noncomputable def radialAffineMax {n m : ℕ} (u : Fin m → Vec n)
    (a : Fin m → ℝ) (g : Vec n) : ℝ :=
  sSup (Set.range (fun j => a j + inner ℝ g (u j) / Real.sqrt n))

end GaussProcSparsify.Optimal.Supplement


