-- Prove2me | Definitions.Def_burau_descent_word
-- name    : burau_descent_word
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T06:05:14.141977+00:00
-- url     : https://prove2.me/theorems/26718824-606e-4718-89f0-6e3db806ee72
-- title:
--   The Euclidean descent word of a unimodular 2x2 matrix
-- statement:
--   **The Euclidean descent of a unimodular $2\times2$ matrix, written as a word in the
--   generators.** Let $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and
--   $T^n=\left(\begin{smallmatrix}1&n\\0&1\end{smallmatrix}\right)$, and for $M\in\mathrm{SL}(2,\mathbb Z)$
--   iterate the Euclidean step $M\mapsto (M\cdot T^{-n})\cdot S$, $n=M_{01}/M_{00}$, recording at each
--   step the factor $S^{-1}T^{n}$; when $M_{00}$ reaches $0$ the two-element terminal word
--   $S^{\pm1}T^{k}$ closes the expansion. The node records that word, `BurauDescent.word M`, and the
--   statement proved here is
--   $$ \prod \mathtt{word}(M) = M . $$
--   This is the combinatorial engine behind the descent section $\rho$ of the reduced braid quotient:
--   it turns an arbitrary element of $\mathrm{SL}(2,\mathbb Z)$ into an explicit product of the two
--   generators, on which the multiplication rules for $\rho$ are checked generator by generator.
-- source:
--   Euclidean algorithm in SL(2,Z); J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. Math. Studies 82 (1974), §3.3.

import Mathlib

set_option autoImplicit false

open Matrix

namespace BurauDescent

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `S = !![0,-1;1,0]`. -/
def Sm : M2 := !![0, -1; 1, 0]

/-- `T^n = !![1,n;0,1]`. -/
def Tm (n : ℤ) : M2 := !![1, n; 0, 1]

/-- `S⁻¹ = S³`. -/
def Sinv : M2 := Sm * Sm * Sm

/-- Generator word for the terminal case `M 0 0 = 0`. -/
noncomputable def baseWord (M : M2) : List M2 :=
  if M 0 1 = -1 then [Sm, Tm (M 1 1)] else [Sm, Sm, Sm, Tm (-(M 1 1))]

/-- `k` steps of the Euclidean descent from `M`, followed by the terminal word. -/
noncomputable def iterWord : ℕ → M2 → List M2
  | 0, M => baseWord M
  | k + 1, M =>
      if M 0 0 = 0 then baseWord M
      else iterWord k ((M * Tm (-(M 0 1 / M 0 0))) * Sm) ++ [Sinv, Tm (M 0 1 / M 0 0)]

/-- The Euclidean descent word of `M`. -/
noncomputable def word (M : M2) : List M2 := iterWord (M 0 0).natAbs M

end BurauDescent


