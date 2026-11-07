-- Prove2me | Definitions.Def_DoublingMST_IsCovering
-- name    : DoublingMST_IsCovering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:34.477982+00:00
-- url     : https://prove2.me/theorems/3c1d3cb5-fdff-4186-8ba8-2e68ac2efd82
-- title:
--   $\rho$-covering (Definition 2.3)
-- statement:
--   A set $S$ is **$\rho$-covering for** $A$ if every $x\in A$ has some $u\in S$ with $d(x,u)\le\rho$.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.3, p.12 (PDF p.14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **ρ-covering.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.3, p.12 (PDF p.14): "S is ρ-covering for X if for every x ∈ X, there exists
u ∈ S such that d(x, u) ≤ ρ."

`IsCovering d S A ρ`: `S` is ρ-covering for `A`. -/
def IsCovering {n : ℕ} (d : Fin n → Fin n → ℝ) (S A : Finset (Fin n)) (ρ : ℝ) : Prop :=
  ∀ x ∈ A, ∃ u ∈ S, d x u ≤ ρ

end DoublingMST


