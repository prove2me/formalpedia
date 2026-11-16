-- Prove2me | Definitions.Def_GreedNorm_Supplement_pwlInitState
-- name    : GreedNorm_Supplement_pwlInitState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:50:35.042534+00:00
-- url     : https://prove2.me/theorems/12d60932-0a71-4a6e-b715-de5a8b58f3e1
-- title:
--   Input layout of a piecewise-linear GLB instance
-- statement:
--   The initial state of the base mission's oracle real RAM on an instance of GLB with piecewise-linear loads: $n$ jobs, $m$ machines, processing times $p_{ij}$, and the explicit data of $f_1,\dots,f_m$.
--
--   1. Integer memory: cell $0$ holds $n$, cell $1$ holds $m$, cell $-(1+i)$ holds the number $K_i$ of breakpoints of $f_i$; all other cells are $0$.
--   2. Real memory: $p_{ij}$ at address $in+j$; machine $i$ has a block starting at $o_i=mn+\sum_{i'<i}(3K_{i'}+2)$ holding its breakpoints, then its $K_i+1$ intercepts, then its $K_i+1$ slopes; all other addresses are $0$.
--
--   The blocks are disjoint, so every datum has its own address. The norm $g$ is not in memory; it is the machine's outer oracle.
--
--   **Formalization Note** Jobs and machines are $0$-based. This layout is the input of Theorem 1.4.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §4.1, p.11 (PDF 13); Theorem 1.4, p.2 (PDF 4)

import Mathlib
import Definitions.Def_GreedNorm_Machine
import Definitions.Def_GreedNorm_Supplement_PWL

namespace GreedNorm

/-- **The initial machine state on a piecewise-linear GLB instance** `(n, m, p, (f_i))`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), §4.1, p.11 (PDF 13), and Theorem 1.4, p.2 (PDF 4).

**Formalization Note** Input layout.
* Integer memory: cell `0` holds `n`, cell `1` holds `m`, cell `-(1 + i)` holds `K_i`
  (the number of breakpoints of machine `i`, `i < m`); every other cell is `0`.
* Real memory: `p i j` at address `i * n + j`, as in the published `glbInitState`. Machine `i`
  has a block starting at `off i = m * n + Σ_{i' < i} (3 K_{i'} + 2)`: `brk k` at `off i + k`
  (`k < K_i`), `icpt k` at `off i + K_i + k` and `slope k` at `off i + 2 K_i + 1 + k`
  (`k ≤ K_i`). The blocks are disjoint, so each address carries at most one datum; all other
  addresses hold `0`.
The monotone symmetric norm `g` is not in memory: it is the outer oracle of `GreedNorm.Machine`. -/
noncomputable def Supplement.pwlInitState {n m : ℕ} (p : Fin m → Fin n → ℝ)
    (D : Fin m → Supplement.PWL) : Machine.State :=
  let off : Fin m → ℤ := fun i =>
    (m : ℤ) * (n : ℤ) + ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => i' < i),
      (3 * ((D i').K : ℤ) + 2)
  Machine.init
    (fun a =>
      (∑ i : Fin m, ∑ j : Fin n, if a = (i : ℤ) * (n : ℤ) + (j : ℤ) then p i j else 0) +
      ∑ i : Fin m,
        ((∑ k ∈ Finset.range (D i).K, if a = off i + k then (D i).brk k else 0) +
         (∑ k ∈ Finset.range ((D i).K + 1),
            if a = off i + (D i).K + k then (D i).icpt k else 0) +
         (∑ k ∈ Finset.range ((D i).K + 1),
            if a = off i + 2 * (D i).K + 1 + k then (D i).slope k else 0)))
    (fun a => if a = 0 then (n : ℤ) else if a = 1 then (m : ℤ) else
      ∑ i : Fin m, if a = -(1 + (i : ℤ)) then ((D i).K : ℤ) else 0)

end GreedNorm


