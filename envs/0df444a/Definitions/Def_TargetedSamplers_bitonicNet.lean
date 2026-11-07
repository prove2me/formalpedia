-- Prove2me | Definitions.Def_TargetedSamplers_bitonicNet
-- name    : TargetedSamplers_bitonicNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:06.96763+00:00
-- url     : https://prove2.me/theorems/0e6e4e4c-a020-4201-9acd-b05c7531b8a7
-- title:
--   The bitonic sorting layers $R_{i,k,j}$ (eq. (1), Algorithm 1)
-- statement:
--   For an array $A$ indexed by $\{0,\dots,2^L-1\}$ over a linearly ordered set, the layer $R_{k,j}$ of eq. (1) maps $A$ to the array whose entry $g$ is computed from $v_0=A_g$ and $v_1=A_{g\oplus 2^j}$:
--   $$\begin{cases}\min(v_0,v_1)& g\wedge 2^k=0,\ g<g\oplus 2^j\\ \max(v_0,v_1)& g\wedge 2^k=0,\ g>g\oplus 2^j\\ \max(v_0,v_1)& g\wedge 2^k\ne0,\ g<g\oplus 2^j\\ \min(v_0,v_1)& g\wedge 2^k\ne0,\ g>g\oplus 2^j\end{cases}$$
--   ($\oplus$, $\wedge$ bitwise). The **bitonic sorter** applies $R_{1,0}$, then $R_{k,k-1},\dots,R_{k,0}$ for $k=2,\dots,L$, in the order of the loops of Algorithm 1 and of the wiring on p.32. Its output is $R_{L,0}$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), eq. (1), p.32 (pdf p.34); Algorithm 1, p.34 (pdf p.36)

import Mathlib

namespace TargetedSamplers

variable {α : Type*} [LinearOrder α]

/-- The auxiliary layer `R_{·,k,j}` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, eq. (1), p.32): gate `g` reads gates `g` and `g ⊕ 2^j` of the
layer below, with values `v₀, v₁`, and outputs `min(v₀, v₁)` if `g ∧ 2^k = 0` and `g < g ⊕ 2^j`,
`max(v₀, v₁)` if `g ∧ 2^k = 0` and `g > g ⊕ 2^j`, `max(v₀, v₁)` if `g ∧ 2^k ≠ 0` and `g < g ⊕ 2^j`,
`min(v₀, v₁)` if `g ∧ 2^k ≠ 0` and `g > g ⊕ 2^j` (`⊕`, `∧` bitwise). Arrays are functions `ℕ → α`; only
the positions below `2^L` matter. -/
def bitonicLayer (k j : ℕ) (A : ℕ → α) : ℕ → α := fun g =>
  if g &&& 2 ^ k = 0 then
    (if g < g ^^^ 2 ^ j then min (A g) (A (g ^^^ 2 ^ j)) else max (A g) (A (g ^^^ 2 ^ j)))
  else
    (if g < g ^^^ 2 ^ j then max (A g) (A (g ^^^ 2 ^ j)) else min (A g) (A (g ^^^ 2 ^ j)))

/-- The layers `R_{·,k,k−1}, …, R_{·,k,0}` applied in this order. -/
def bitonicStage (k : ℕ) (A : ℕ → α) : ℕ → α :=
  (List.range k).reverse.foldl (fun B j => bitonicLayer k j B) A

/-- The bitonic sorter on arrays of length `2^L` (Algorithm 1, p.34, and the layer order of p.32:
`R_{·,1,0}`, then `R_{·,k,k−1}, …, R_{·,k,0}` for `k = 2, …, L`): its output is `R_{·,L,0}`. -/
def bitonicNet (L : ℕ) (A : ℕ → α) : ℕ → α :=
  (List.range' 1 L).foldl (fun B k => bitonicStage k B) A

end TargetedSamplers


