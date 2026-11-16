-- Prove2me | Definitions.Def_GreedNorm_Supplement_pwlThreshInitState
-- name    : GreedNorm_Supplement_pwlThreshInitState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:51:20.47009+00:00
-- url     : https://prove2.me/theorems/b6e8198f-04a4-4e1c-a39c-a2f53b13f5a1
-- title:
--   Input layout of a piecewise-linear GLB instance with a threshold vector $t$
-- statement:
--   For a fixed $\epsilon>0$ and the index set $\mathrm{POS}=\mathrm{POS}_{m,\epsilon}\subseteq\{0,\dots,m\}$ of threshold vectors, this is the layout of the piecewise-linear GLB instance (as in the previous definition) together with a threshold vector $t$: for every $\ell\le m$, real cell $-(1+\ell)$ holds $t_\ell$ and integer cell $-(m+1+\ell)$ holds $1$ if $\ell\in\mathrm{POS}$ and $0$ otherwise.
--
--   The flags encode the index set of the $|\mathrm{POS}|$-dimensional vector $t$. The added cells are $0$ in the instance layout, so nothing is overwritten. It is the input of Theorem 4.6.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 4.6, p.12 (PDF 14); §2 Threshold vectors, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_POS
import Definitions.Def_GreedNorm_Supplement_pwlInitState

namespace GreedNorm

/-- **The initial machine state on a piecewise-linear GLB instance with a threshold vector `t`.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 4.6, p.12 (PDF 14): "Let t be a good threshold vector, then we can efficiently find
…"; threshold vectors are indexed by `POS = POS_{m,ϵ}` (§2, p.5, PDF 7).

**Formalization Note** The memory of `Supplement.pwlInitState p D`, plus the threshold vector:
for every `ℓ ≤ m`, real cell `-(1 + ℓ)` holds `t ℓ` and integer cell `-(m + 1 + ℓ)` holds `1`
if `ℓ ∈ POS m ε` and `0` otherwise. These cells are `0` in `pwlInitState` (its negative
integer cells are `-1, …, -m`), so nothing is overwritten. The flags encode the index set of
the `|POS|`-dimensional vector `t`; `POS m ε ⊆ {0, …, m}`. -/
noncomputable def Supplement.pwlThreshInitState {n m : ℕ} (ε : ℝ) (p : Fin m → Fin n → ℝ)
    (D : Fin m → Supplement.PWL) (t : ℕ → ℝ) : Machine.State :=
  let s := Supplement.pwlInitState p D
  { s with
    core := { s.core with
      mem := fun a => s.core.mem a +
        ∑ ℓ ∈ Finset.range (m + 1), if a = -(1 + (ℓ : ℤ)) then t ℓ else 0 }
    integerMemory := fun a => s.integerMemory a +
      ∑ ℓ ∈ Finset.range (m + 1),
        if a = -((m : ℤ) + 1 + (ℓ : ℤ)) then (if ℓ ∈ POS m ε then 1 else 0) else 0 }

end GreedNorm


