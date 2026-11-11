-- Prove2me | Definitions.Def_RandDelMatroid_Indep_R10
-- name    : RandDelMatroid_Indep_R10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:27.951218+00:00
-- url     : https://prove2.me/theorems/8adfc9d9-28fc-4422-af43-5f5c78311662
-- title:
--   The matroid $R_{10}$ (Figure 1)
-- statement:
--   $R_{10}$ is the binary matroid on ten elements represented over $\mathbb F_2$ by the matrix of Figure 1:
--
--   $$A_{R_{10}}=\begin{pmatrix}1&1&0&0&1&1&0&0&0&0\\1&1&1&0&0&0&1&0&0&0\\0&1&1&1&0&0&0&1&0&0\\0&0&1&1&1&0&0&0&1&0\\1&0&0&1&1&0&0&0&0&1\end{pmatrix}.$$
--
--   A matroid $N$ is **isomorphic to $R_{10}$** if there is a bijection $f$ from the ten columns onto the ground set of $N$ such that a set $S$ of columns is linearly independent over $\mathbb F_2$ iff $f(S)$ is independent in $N$.
--
--   $R_{10}$ is the one exceptional building block of Seymour's decomposition besides graphic and cographic matroids.
--
--   **Formalization Note** The matrix is copied row by row from Figure 1 (p. 11). `IsR10 N` takes an injective `f : Fin 10 → β` with range `N.E`.
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 11, Figure 1

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

/-- Figure 1 (p. 11): the binary representation `A_{R10}` of `R10`, a `5 × 10` matrix over `𝔽₂`. -/
def matR10 : Matrix (Fin 5) (Fin 10) (ZMod 2) :=
  !![1, 1, 0, 0, 1, 1, 0, 0, 0, 0;
     1, 1, 1, 0, 0, 0, 1, 0, 0, 0;
     0, 1, 1, 1, 0, 0, 0, 1, 0, 0;
     0, 0, 1, 1, 1, 0, 0, 0, 1, 0;
     1, 0, 0, 1, 1, 0, 0, 0, 0, 1]

/-- `N` is isomorphic to `R10`, the binary matroid represented over `𝔽₂` by `A_{R10}` (Figure 1):
there is a bijection `f` from the ten columns onto `N.E` such that a set of columns `S` is linearly
independent over `𝔽₂` iff `f(S)` is independent in `N`. -/
def IsR10 {β : Type} (N : Matroid β) : Prop :=
  ∃ f : Fin 10 → β, Function.Injective f ∧ Set.range f = N.E ∧
    ∀ S : Set (Fin 10), N.Indep (f '' S) ↔ LinearIndepOn (ZMod 2) (fun j : Fin 10 => fun i => matR10 i j) S

end RandDelMatroid.Indep


