-- Prove2me | Definitions.Def_RGGThreshold_eventF
-- name    : RGGThreshold_eventF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:58.260208+00:00
-- url     : https://prove2.me/theorems/7c458585-d279-41c1-8d77-fa3c03c326b4
-- title:
--   The truncation event $\mathcal T_s$, the projection event $\Pi_s$, and the vector event $\mathcal F$
-- statement:
--   Fix $0\le s\le n$ and let $v_1,\dots,v_n$ be the Gram–Schmidt coordinates of points of $\mathbb S^{d-1}$.
--
--   1. The **truncation event** $\mathcal T_s$: $|v_i(s)|\le 10\sqrt{\log d/d}$ for all $s<i\le n$.
--   2. The **projection event** $\Pi_s$: $\big|\|\pi_s(v_i)\|_2^2-s/d\big|\le 10\sqrt{n\log d}/d$ for all $s<i\le n$, and $|\langle\pi_s(v_i),\pi_s(v_j)\rangle|\le10\sqrt{n\log d}/d$ for all $s<i<j\le n$.
--
--   Finally $\mathcal F=\bigwedge_{s=1}^n(\mathcal T_s\wedge\Pi_s)$. The event $\Pi_s$ depends only on the coordinates $v_i(j)$ with $j\le s$. On $\mathcal F$ the points are almost orthogonal with small coordinates, which keeps the error terms of the vertex-exposure argument under control.
--
--   **Formalization Note** $\mathcal T_s$ and $\Pi_s$ are written for a coordinate matrix, so that they apply both to the Gram–Schmidt coordinates of a configuration and to revealed data in Setup (⋆); $s$ is the paper's 1-based index.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Definition 2.4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RGGThreshold_gsCoord

namespace RGGThreshold

/-- The truncation event `T_s` on a coordinate matrix (Hunter–Milojević–Sudakov,
arXiv:2607.22480, held version, sha256 1a398ef9…, Definition 2.4 (i), p.9 (PDF p.11)):
`|v_i(s)| ≤ 10 √(log d / d)` for all `s < i ≤ n`.

**Formalization Note** `s` is the paper's 1-based coordinate index; 0-based, the coordinate is
`j` with `j + 1 = s`, and the vertices are `i` with `s < i + 1`. -/
def truncW {n : ℕ} (d s : ℕ) (W : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val + 1 = s → s < i.val + 1 →
    |W i j| ≤ 10 * Real.sqrt (Real.log d / d)

/-- The projection event `Π_s` on a coordinate matrix (arXiv:2607.22480, held version,
Definition 2.4 (ii), p.9 (PDF p.11)): `|‖π_s(v_i)‖² - s/d| ≤ 10 √(n log d)/d` for all `s < i ≤ n`, and
`|⟨π_s(v_i), π_s(v_j)⟩| ≤ 10 √(n log d)/d` for all `s < i < j ≤ n`.

**Formalization Note** `s` is the paper's 1-based count of revealed coordinates, and the
vertices `s < i` are the 0-based `i` with `s < i + 1`. It depends only on the coordinates `j ≤ s`. -/
def projW {n : ℕ} (d s : ℕ) (W : Fin n → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, s < i.val + 1 →
    |ipUpTo s W i i - (s : ℝ) / d| ≤ 10 * Real.sqrt (n * Real.log d) / d) ∧
  (∀ i j : Fin n, s < i.val + 1 → i < j →
    |ipUpTo s W i j| ≤ 10 * Real.sqrt (n * Real.log d) / d)

/-- The vector event `𝓕 = ⋀_{s=1}^{n} (T_s ∧ Π_s)` on configurations, evaluated on the
Gram–Schmidt coordinates (arXiv:2607.22480, held version, Definition 2.4, p.9 (PDF p.11)). -/
def eventF (n d : ℕ) : Set (RGGDetect.Config n d) :=
  {x | ∀ s : ℕ, 1 ≤ s → s ≤ n → truncW d s (gsCoord x) ∧ projW d s (gsCoord x)}

end RGGThreshold


