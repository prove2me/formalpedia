-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_OddWitness
-- name    : ExplicitTensorBarrier694_Explicit_Supplement_OddWitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:38:58.410332+00:00
-- url     : https://prove2.me/theorems/198dee64-61a8-48ac-97aa-ea51f9ca62b6
-- title:
--   The tensor $S_n$ of Definition 5.1 and the Vandermonde products $\Delta_S$
-- statement:
--   Let $n=2p+1$. Following Definition 5.1, let $A=\mathbb C^n$ with basis $a_1,\dots,a_n$, identify $B^*$ with the polynomials $\mathbb C[t]_{<n}$ of degree less than $n$, and put $C=\mathbb C^{p+1}\oplus\mathbb C^p$. For $v_q(t)=(1,t,\dots,t^{q-1})^T$ define
--
--   $$S_n=\sum_{i=1}^n a_i\otimes X_i,\qquad X_i(f)=f(i)\,v_{p+1}(i)\oplus f'(i)\,v_p(i),$$
--
--   where $X_i\in B\otimes C=\mathrm{Hom}(B^*,C)$. In coordinates, with the monomial basis $t^0,\dots,t^{n-1}$ of $B^*$ (and the dual basis of $B$), the entry of $S_n$ at $(a_i,t^u,w)$ is the $w$-th coordinate of $X_i(t^u)$: $i^{u}i^{w}$ for $w<p+1$ and $u\,i^{u-1}i^{w-p-1}$ for $p+1\le w<2p+1$. The evaluation points are $1,\dots,n$.
--
--   For a finite set $S$ of positive integers, $\Delta_S=\prod_{i<j,\ i,j\in S}(j-i)$, with the empty product equal to $1$.
--
--   $S_n$ is the tensor whose central Koszul flattening is invertible (Theorem 5.2); $\Delta_S$ enters Lemma 5.3.
--
--   **Formalization Note** The index $i\in\{0,\dots,n-1\}$ of `Fin n` stands for the point $i+1$; the first $p+1$ coordinates of $C$ form the summand $\mathbb C^{p+1}$. For $u=0$ the derivative coordinate is $0$.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Definition 5.1, equation (5.1), p.15, and the definition of Δ_S, p.15 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Definition 5.1, equation (5.1), p.15, with n = 2p+1. Coordinates: A = ℂⁿ with basis
a_1,…,a_n (index `i : Fin n` is the point i+1); B* = ℂ[t]_{<n} with the monomial basis
t^0,…,t^{n−1} (column index `u`, the dual basis of B); C = ℂ^{p+1} ⊕ ℂ^p (index `w`, the
first p+1 coordinates are the first summand). The entry (i,u,w) is the w-th coordinate of
X_i(t^u) = (t^u)(i) v_{p+1}(i) ⊕ (t^u)'(i) v_p(i), v_q(t) = (1,t,…,t^{q−1}). Evaluation
points are 1,…,n. For u = 0 the derivative coordinate is 0 (the factor u vanishes). -/
noncomputable def oddWitness (p : ℕ) : Tensor (2 * p + 1) (2 * p + 1) (2 * p + 1) :=
  fun i u w =>
    let x : ℂ := ((i : ℕ) : ℂ) + 1
    if (w : ℕ) < p + 1 then x ^ (u : ℕ) * x ^ (w : ℕ)
    else ((u : ℕ) : ℂ) * x ^ ((u : ℕ) - 1) * x ^ ((w : ℕ) - (p + 1))

/-- Δ_S = ∏_{i<j, i,j ∈ S} (j − i), p.15, for a finite set S of natural numbers (used for
S ⊆ [n] = {1,…,n}); the empty product is 1. -/
def vandermondeDelta (S : Finset ℕ) : ℂ :=
  ∏ i ∈ S, ∏ j ∈ S.filter (fun j => i < j), ((j : ℂ) - (i : ℂ))

end ExplicitTensorBarrier694.Explicit.Supplement


