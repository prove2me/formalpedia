-- Prove2me | Definitions.Def_SteurerHDX_lambdaTwo
-- name    : SteurerHDX_lambdaTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:11.420642+00:00
-- url     : https://prove2.me/theorems/8febb9cf-1ba0-4180-9707-2056bb9e2af0
-- title:
--   The second eigenvalue $\lambda_2(P)$, counted with multiplicity
-- statement:
--   For a weighted graph with symmetric weights $W$ and positive degrees, the walk $P=D^{-1}W$ has real eigenvalues $1=\lambda_1\ge\lambda_2\ge\dots\ge\lambda_n$ listed **with multiplicity**. The **second eigenvalue** is $\lambda_2(P)$. If the eigenvalue $1$ has multiplicity at least two (e.g. a disconnected graph), then $\lambda_2(P)=1$.
--
--   **Formalization Note** $\lambda_2$ is the entry of index $1$ of the decreasingly sorted eigenvalue list `eigenvalues₀` of the symmetric matrix $D^{-1/2}WD^{-1/2}$. Outside the meaningful case (that matrix not symmetric, or fewer than two states) the value is a junk $0$; every theorem using $\lambda_2$ assumes a symmetric $W$ with positive degrees and at least two states.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1 and Lemma 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_symWalk

namespace SteurerHDX

/-- **The second eigenvalue λ₂(P).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1 and Lemma 2.1, p.3: "The largest
eigenvalue is 1 corresponding to the all-ones eigenfunction", "The second eigenvalue of P".

**Formalization Note.** λ₂(P) of P = D⁻¹W is the second largest eigenvalue *counted with
multiplicity*: the entry of index 1 of the antitone list `eigenvalues₀` of the symmetric matrix
`symWalk W` = D^{-1/2} W D^{-1/2}, which is similar to P. (If 1 has multiplicity ≥ 2, then
λ₂ = 1.) The value is a junk `0` when `symWalk W` is not symmetric or the state space has fewer
than two points; every theorem using it assumes a symmetric W with positive degrees and at least
two states. -/
noncomputable def lambdaTwo {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) : ℝ := by
  classical
  exact if h : (symWalk W).IsHermitian ∧ 2 ≤ Fintype.card ι then
    h.1.eigenvalues₀ ⟨1, h.2⟩ else 0

end SteurerHDX


