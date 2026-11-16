-- Prove2me | Definitions.Def_GreedNorm_Supplement_pwlNorm
-- name    : GreedNorm_Supplement_pwlNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:50:01.96951+00:00
-- url     : https://prove2.me/theorems/995ea44a-8eff-44c5-b2bb-045c0eef47fc
-- title:
--   Inner load $v\mapsto f_i(\sum_j v_j)$ of a piecewise-linear machine
-- statement:
--   Given explicit piecewise-linear data $f_1,\dots,f_m$, the inner load of machine $i$ on a vector $v\in\mathbb R^n$ is
--
--   $$
--   F_i(v)=f_i\Big(\sum_{j=1}^n v_j\Big).
--   $$
--
--   Applied to the processing-time vector $p_i[\sigma]$ (equal to $p_{ij}$ on the jobs assigned to $i$ and $0$ elsewhere), it gives $\mathrm{load}_i(\sigma)=f_i\big(\sum_{j:\sigma(j)=i}p_{ij}\big)$, the load of §4.1. Plugged into the base mission's load vector, cost and optimum, it yields the generalized activation cost $g(\mathrm{load}(\sigma))$ of GLB with piecewise-linear loads and its minimum.
--
--   **Formalization Note** It is also the inner oracle of the base machine in Theorems 1.4 and 4.6. Since the pieces are in the input memory, the oracle gives the program nothing it could not compute itself.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §4.1, p.11 (PDF 13)

import Mathlib
import Definitions.Def_GreedNorm_Supplement_PWL

namespace GreedNorm

/-- **The GLB inner load of a piecewise-linear machine**, `v ↦ f_i(Σ_j v_j)`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), §4.1, p.11 (PDF 13): "loadi(σ) = fi(Σ_{j∈J:σ(j)=i} pij)".

**Formalization Note** With this inner function the published `GreedNorm.glbLoad` gives
`glbLoad p (pwlNorm D) σ i = f_i(Σ_{j : σ j = i} p i j)`, because `glbVec p σ i` is `p i j` on
the jobs of machine `i` and `0` elsewhere; so `glbCost` and `OPT` are the generalized activation
cost `g(load(σ))` of §4.1 and its minimum. It is also the inner oracle of `GreedNorm.Machine`;
since the pieces are in the input memory, the oracle gives the program nothing it could not
compute. -/
noncomputable def Supplement.pwlNorm {n m : ℕ} (D : Fin m → Supplement.PWL) :
    Fin m → (Fin n → ℝ) → ℝ :=
  fun i v => (D i).eval (∑ j, v j)

end GreedNorm


