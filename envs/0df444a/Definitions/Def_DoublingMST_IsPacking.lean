-- Prove2me | Definitions.Def_DoublingMST_IsPacking
-- name    : DoublingMST_IsPacking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:31.892587+00:00
-- url     : https://prove2.me/theorems/8aea7153-423f-4524-99c7-cfdf1953700b
-- title:
--   $\rho$-packing (Definition 2.3)
-- statement:
--   A set $S\subseteq X$ is **$\rho$-packing** if $d(u,v)\ge\rho$ for all distinct $u,v\in S$.
--
--   **Formalization Note** Statements add $\rho>0$, as Definition 2.3 does. "$S$ is $\rho$-packing for $A$" means $S\subseteq A$ and $S$ is $\rho$-packing.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.3, p.12 (PDF p.14)

import Mathlib
open scoped Classical

namespace DoublingMST

/-- **ρ-packing.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.3, p.12 (PDF p.14): "For ρ > 0, S is ρ-packing if for all distinct u, v ∈ S,
d(u, v) ≥ ρ."

**Formalization Note.** Defined for every real `ρ`; statements add `0 < ρ` where the page has it.
"S is ρ-packing for A" (Lemmas 2.7, 4.2) means `S ⊆ A` and `S` is ρ-packing. -/
def IsPacking {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (ρ : ℝ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ρ ≤ d u v

end DoublingMST


