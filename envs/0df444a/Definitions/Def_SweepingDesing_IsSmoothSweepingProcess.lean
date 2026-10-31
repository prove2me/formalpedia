-- Prove2me | Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
-- name    : SweepingDesing_IsSmoothSweepingProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:21.408627+00:00
-- url     : https://prove2.me/theorems/36f2d448-9b51-4fcc-97ee-359e7cb62088
-- title:
--   Definition 10 — smooth sweeping process
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ have closed graph $\mathcal S\subset\mathbb R^{n+1}=\mathbb R\times\mathbb R^n$. Then $S$ is a **smooth sweeping process** if either
--
--   1. $\mathcal S$ is a closed connected $C^1$-smooth submanifold of $\mathbb R^{n+1}$ of dimension at most $n$; or
--   2. $\mathcal S$ is a connected smooth manifold of full dimension with boundary, and its boundary $\partial\mathcal S$ is a $C^1$-smooth manifold of dimension $n$.
--
--   The graph of the sublevel map $t\mapsto\{f\le t\}$ of a $C^1$ function with no critical points on the level sets, or the graph of $t\mapsto f^{-1}(t)$, are typical examples. This regularity replaces the o-minimality assumed in earlier work.
--
--   **Formalization Note** Submanifolds are given by local defining functions. Case 1: there is one $k\le n$ such that every point of $\mathcal S$ has an open neighbourhood $W$ and a $C^1$ map $g:W\to\mathbb R^{n+1-k}$ with surjective derivative on $W$ and $\mathcal S\cap W=g^{-1}(0)\cap W$. Case 2: every point of the topological boundary of $\mathcal S$ has an open neighbourhood $W$ and a $C^1$ function $g$ with nonvanishing derivative on $W$ and $\mathcal S\cap W=\{g\le0\}\cap W$. Closedness of $\mathcal S$ (the standing assumption of §3.1) is part of both cases.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1 and Definition 10, p.7

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1 and Definition 10, p.7: `S : ℝ ⇉ ℝⁿ` has closed graph `𝒮` and is a *smooth
sweeping process*, i.e. either
* `𝒮` is a closed connected `C¹`-smooth submanifold of `ℝⁿ⁺¹` of dimension at most `n`; or
* `𝒮` is a connected smooth manifold of full dimension with boundary and `∂𝒮` is a `C¹`-smooth
  manifold of dimension `n`.

**Formalization Note** `ℝⁿ⁺¹ = ℝ × ℝⁿ` (time first). Submanifolds are described by local
defining functions. Case 1: there is one `k ≤ n` (the dimension; `𝒮` is connected) such that
near every point of `𝒮` there are an open set `W` and a `C¹` map `g : W → ℝ^(n+1-k)` with
surjective derivative at every point of `W` and `𝒮 ∩ W = g⁻¹(0) ∩ W`. Case 2: near every
point of the topological boundary `∂𝒮 = frontier 𝒮` there are an open `W` and a `C¹` function
`g` with nonvanishing derivative on `W` and `𝒮 ∩ W = {g ≤ 0} ∩ W`; this says exactly that `𝒮`
is a full-dimensional manifold with `C¹` boundary `∂𝒮` of dimension `n` (points of `𝒮` off
`∂𝒮` are interior points). The closedness of `𝒮` is the standing assumption of §3.1 and is
stated in both cases. -/
def IsSmoothSweepingProcess {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (IsClosed (GenNewtonSubgrad.ProxReg.gph S) ∧ IsConnected (GenNewtonSubgrad.ProxReg.gph S) ∧
    ∃ k : ℕ, k ≤ n ∧ ∀ p ∈ GenNewtonSubgrad.ProxReg.gph S, ∃ W : Set (ℝ × EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ p ∈ W ∧
      ∃ g : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1 - k)),
        ContDiffOn ℝ 1 g W ∧ (∀ q ∈ W, Function.Surjective (fderiv ℝ g q)) ∧
        GenNewtonSubgrad.ProxReg.gph S ∩ W = W ∩ g ⁻¹' {0}) ∨
  (IsClosed (GenNewtonSubgrad.ProxReg.gph S) ∧ IsConnected (GenNewtonSubgrad.ProxReg.gph S) ∧
    ∀ p ∈ frontier (GenNewtonSubgrad.ProxReg.gph S), ∃ W : Set (ℝ × EuclideanSpace ℝ (Fin n)),
      IsOpen W ∧ p ∈ W ∧
      ∃ g : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiffOn ℝ 1 g W ∧ (∀ q ∈ W, fderiv ℝ g q ≠ 0) ∧
        GenNewtonSubgrad.ProxReg.gph S ∩ W = {q | q ∈ W ∧ g q ≤ 0})

end SweepingDesing


