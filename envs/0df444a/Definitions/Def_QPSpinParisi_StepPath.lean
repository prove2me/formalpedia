-- Prove2me | Definitions.Def_QPSpinParisi_StepPath
-- name    : QPSpinParisi_StepPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:54.473206+00:00
-- url     : https://prove2.me/theorems/8d71108d-908f-4aea-a002-025e62dace6d
-- title:
--   A step path in $\Pi$
-- statement:
--   A path $\pi:[0,1]\to\mathrm{Sym}_3^+$ taking finitely many values: jump points $m_0\le\dots\le m_k$ in $[0,1]$ and matrices $Q_0\preceq\dots\preceq Q_{k+1}$ with
--   $$\pi(u)=Q_\ell\text{ on }(m_{\ell-1},m_\ell],\qquad\pi(u)=Q_{k+1}\text{ on }(m_k,1],\qquad\pi(0)=Q_0,\qquad m_{-1}:=0.$$
--   These are the left-continuous increasing step maps of the set $\Pi$ in the paper.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.15 (PDF p.15)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- A step path in `Π` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.15, PDF p.15): the left-continuous path `π : [0,1] → Sym⁺₃` with `π(u) = Q_ℓ` on
`(m_{ℓ-1}, m_ℓ]` for `0 ≤ ℓ ≤ k`, `π(u) = Q_{k+1}` on `(m_k, 1]`, `π(0) = Q₀`, and `m_{-1} := 0`.

**Formalization Note** `m` and `Q` are indexed by `ℕ`, and only the indices `≤ k` and `≤ k + 1` are read. -/
structure StepPath where
  /-- The number of levels minus one. -/
  k : ℕ
  /-- The jump points `m₀ ≤ ⋯ ≤ m_k` in `[0,1]`. -/
  m : ℕ → ℝ
  /-- The values `Q₀ ⪯ ⋯ ⪯ Q_{k+1}`. -/
  Q : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  /-- Jump points lie in `[0,1]`. -/
  m_mem : ∀ l, l ≤ k → m l ∈ Icc (0 : ℝ) 1
  /-- Jump points increase. -/
  m_mono : ∀ l, l < k → m l ≤ m (l + 1)
  /-- Values are positive semidefinite. -/
  Q_psd : ∀ l, l ≤ k + 1 → (Q l).PosSemidef
  /-- Values increase in the Loewner order. -/
  Q_mono : ∀ l, l ≤ k → (Q (l + 1) - Q l).PosSemidef

end QPSpinParisi


