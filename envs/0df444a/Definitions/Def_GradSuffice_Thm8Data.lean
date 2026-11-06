-- Prove2me | Definitions.Def_GradSuffice_Thm8Data
-- name    : GradSuffice_Thm8Data
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:06.679526+00:00
-- url     : https://prove2.me/theorems/6d6158cb-6eed-44ca-be72-5244ee90497b
-- title:
--   Data of the hard instance of Theorem 8
-- statement:
--   The hard instance in the proof of Theorem 8 is built from
--   1. a margin $\theta$, a session length $D$, a number of copies $\kappa$ and a noise level $\nu$;
--   2. a tree $\bar\xi$ of depth $DL$ labelled by dual vectors, $L$ the block length ("w.l.o.g. assume its depth is exactly $DL$");
--   3. branches $\sigma_1,\dots,\sigma_\kappa$ of that tree, sampled uniformly and independently in the paper;
--   4. points $w_{\sigma_1},\dots,w_{\sigma_\kappa}$, the witnesses of the sampled branches.
--
--   The conditions these data satisfy are collected in `Thm8Data.IsValid`.
--
--   **Formalization Note** Copies $k$ and tree positions are 0-based, so the paper's copy $k$ is copy $k-1$ here. The branches are fixed data; statements about the construction hold for every realization of them.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, pp.18–19

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_thm8L

namespace GradSuffice

/-- **Data of the hard instance of Theorem 8.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, pp.18–19: the margin `θ`, the session
length `D`, the number of copies `κ`, the noise level `ν`, a tree `ξ` of depth `DL` ("W.l.o.g. assume
its depth is exactly `DL`", p.19, with `L = thm8L θ D`), the sampled branches `σ₁, …, σ_κ`, and the
witnesses `w_{σ_k}`. The validity conditions are `Thm8Data.IsValid`.

**Formalization Note.** Copies `k` and tree positions are 0-based (`Fin κ`, `Fin (D L)`); the
paper's copy `k` is `k − 1` here. The branches are fixed data: every statement about the construction
is "for every realization of the branches". -/
structure Thm8Data (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  θ : ℝ
  D : ℕ
  κ : ℕ
  ν : ℝ
  /-- The tree of depth `D L` (its internal nodes `ξ i (σ<ᵢ)`). -/
  ξ : NondualOpt.Tree (StrongDual ℝ X) (D * thm8L θ D)
  /-- The sampled branches `σ_k`, `k < κ`. -/
  σ : Fin κ → Fin (D * thm8L θ D) → Bool
  /-- The witness points `w_{σ_k}`. -/
  wσ : Fin κ → X

end GradSuffice


