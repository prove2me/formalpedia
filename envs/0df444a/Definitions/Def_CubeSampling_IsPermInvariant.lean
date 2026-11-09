-- Prove2me | Definitions.Def_CubeSampling_IsPermInvariant
-- name    : CubeSampling_IsPermInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:44.928696+00:00
-- url     : https://prove2.me/theorems/f25691ef-6ad9-402c-bf92-3bc5e1de0060
-- title:
--   Permutation-invariant set of cube points
-- statement:
--   A set $E \subseteq \{-1,1\}^d$ is **permutation-invariant** if $x \in E \iff (x_{\pi(1)},\dots,x_{\pi(d)}) \in E$ for every permutation $\pi$ of $[d]$ and every $x$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.9, p.6

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- A set of cube points is permutation-invariant: invariant under every permutation of the
coordinates (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.9, p.6). -/
def IsPermInvariant {d : ℕ} (E : Set (Cube d)) : Prop :=
  ∀ (π : Equiv.Perm (Fin d)) (x : Cube d), x ∈ E ↔ x ∘ π ∈ E

end CubeSampling


