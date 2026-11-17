-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_tensorAsymptoticSubrank
-- name    : GraphTensorCP_Supplement_tensorAsymptoticSubrank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:23:50.29585+00:00
-- url     : https://prove2.me/theorems/1b366207-6882-4fc7-903a-433058b9eec7
-- title:
--   Tensor subrank $Q_{\mathbb F}(T)$ and asymptotic subrank $\widetilde Q_{\mathbb F}(T)$
-- statement:
--   For $d\ge2$, the **subrank** of an order-$d$ tensor $T$ over a field $\mathbb F$ is the largest integer $r$ for which the diagonal tensor $I_d(r)$ is a restriction of $T$:
--
--   $$
--   Q_{\mathbb F}(T)=\max\{r:I_d(r)\preceq T\}.
--   $$
--
--   Its **asymptotic subrank** is
--
--   $$
--   \widetilde Q_{\mathbb F}(T)=\sup_{N\ge1}Q_{\mathbb F}(T^{\otimes_K N})^{1/N}.
--   $$
--
--   Asymptotic subrank measures the largest diagonal resource obtainable per tensor copy and is the tensor parameter in the weighted minimum-cut equality.
--
--   **Formalization Note** The existing published MME rank module defines restriction and asymptotic rank but not asymptotic subrank. This supplement therefore defines the standard subrank locally for tensor order at least two, with the restriction orientation $I_r\preceq T$, and indexes powers by $N+1$ to exclude the zeroth power. The paper proves that the resulting supremum equals its defining limit.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definitions 2.12–2.13, pp.18–19

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

namespace Supplement

/-- The **tensor subrank** `Q_F(T)`: the largest `r` such that the diagonal tensor `I_r` is a
restriction of `T` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive
Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.12, p.18).

**Formalization Note.** `sSup` is taken in `ℕ`. For a finite-dimensional tensor object this set
is bounded and contains `0`, so it is the stated maximum. The restriction orientation is
`I_r ⪯ T`. The argument `hd` records the source's standing requirement that tensor subrank has
order at least two. -/
noncomputable def tensorSubrankObj {K : Type u} [Field K] {d : ℕ}
    (_hd : 2 ≤ d) (T : MME.TensorObj K d) : ℕ :=
  sSup {r : ℕ | MME.TensorObj.Restrict (MME.TensorObj.diagObj K d r) T}

/-- The **asymptotic subrank**
`Q̃_F(T) = sup_{N≥1} Q_F(T^{⊗_K N})^{1/N}` (Zhou,
arXiv:2610.34273 (version of 2026-11-03), Definition 2.13, pp.18–19).

**Formalization Note.** The index is written `N+1` so that the exponent is always positive,
exactly as the published rank module writes asymptotic rank. The rank module contains restriction
and asymptotic rank but no asymptotic-subrank declaration, so this paper-required parameter is
defined locally. The paper proves on p.19 that this supremum equals its defining limit. -/
noncomputable def tensorAsymptoticSubrank {K : Type u} [Field K] {d : ℕ}
    (hd : 2 ≤ d) (T : MME.TensorObj K d) : ℝ :=
  ⨆ N : ℕ, (tensorSubrankObj hd (MME.TensorObj.kronPow T (N + 1)) : ℝ) ^
    ((1 : ℝ) / (N + 1))

end Supplement

end GraphTensorCP


