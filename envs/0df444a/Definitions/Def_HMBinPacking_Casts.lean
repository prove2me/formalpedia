-- Prove2me | Definitions.Def_HMBinPacking_Casts
-- name    : HMBinPacking_Casts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:26.905199+00:00
-- url     : https://prove2.me/theorems/2854c698-9ce9-4ff3-911e-a2f5c3b9944b
-- title:
--   Inclusions $\mathbb Z^d\subseteq\mathbb R^d$ and $\mathbb Q^n\subseteq\mathbb R^n$
-- statement:
--   The coordinatewise inclusions of integer vectors $\mathbb Z^d\subseteq\mathbb R^d$ and rational vectors $\mathbb Q^n\subseteq\mathbb R^n$.
--
--   They let integer points of polytopes and rational queries to convex sets be stated inside real space, as the paper does.
--
--   **Formalization Note** Vectors are functions on `Fin d`; `zCast` and `qCast` cast each coordinate.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §2 pp.3–4 (integer points Z^d in R^d) and §3 p.5 (queries y ∈ Q^n)

import Mathlib

namespace HMBinPacking

/-- **The inclusion `ℤ^d ⊆ ℝ^d`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, pp.3–4 (integer points `Z^d` inside `R^d`).

**Formalization Note.** Vectors are functions on `Fin d`; the cast is coordinatewise. -/
def zCast {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (x i : ℝ)

/-- **The inclusion `ℚ^n ⊆ ℝ^n`.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5 (rational queries `y ∈ Q^n` to a set `Q ⊆ R^n`).

**Formalization Note.** Vectors are functions on `Fin n`; the cast is coordinatewise. -/
def qCast {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ :=
  fun i => (x i : ℝ)

end HMBinPacking


