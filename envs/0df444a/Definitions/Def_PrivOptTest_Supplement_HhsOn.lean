-- Prove2me | Definitions.Def_PrivOptTest_Supplement_HhsOn
-- name    : PrivOptTest_Supplement_HhsOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:45.612116+00:00
-- url     : https://prove2.me/theorems/8d3bc1ff-c302-43d8-948b-abf14e73365d
-- title:
--   Homogeneous halfspaces $\mathcal H_{\mathrm{hs}}$ on a finite domain $\mathcal X\subseteq\mathbb R^d$
-- statement:
--   For $w\in\mathbb R^d$ the **homogeneous halfspace** with normal $w$ is the classifier
--
--   $$h_w(x)=\operatorname{sign}(\langle w,x\rangle)\in\{\pm1\},\qquad \operatorname{sign}(0)=+1,$$
--
--   and the class is $\mathcal H_{\mathrm{hs}}=\{h_w : w\in\mathbb R^d\}$ (equation (10)). The normal ranges over all of $\mathbb R^d$, including $w=0$, which labels every point $+1$ and therefore makes exactly $n$ mistakes in the disjoint-label setting (p.32). For a public finite domain $\mathcal X\subseteq\mathbb R^d$, $\mathcal H_{\mathrm{hs}}|_{\mathcal X}$ is the set of restrictions of these classifiers to $\mathcal X$.
--
--   This class plays the role, for §4 of the paper, that thresholds play in the base mission: with Alice's records labelled $-1$ and Bob's $+1$, $\mathrm{opt}_{\mathcal H_{\mathrm{hs}}}(S_A,S_B)$ is the base mission's joint loss for this class.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; $+1$ is `true`. The normal is not normalised.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), equation (10), p.25; p.32

import Mathlib
import Definitions.Def_PrivOptTest_IsTester

namespace PrivOptTest

namespace Supplement

/-- The prediction of the homogeneous halfspace with normal `w` at `x`: `h_w(x) = sign(⟨w, x⟩)`, with
`true` for `+1` and `false` for `−1`, and `sign(0) = +1` (arXiv:2611.03599, manuscript sha256 4ac94dcf…,
(10), p.25; p.32: "classifier `w = 0` labels every point as positive"). -/
noncomputable def hs {d : ℕ} (w x : EuclideanSpace ℝ (Fin d)) : Bool :=
  decide (0 ≤ inner ℝ w x)

/-- **Homogeneous halfspaces, (10), p.25**: `H_hs = {h_w : ℝ^d → {±1} | ∃ w ∈ ℝ^d, h_w(x) = sign(⟨w, x⟩)}`.
The normal `w` ranges over all of `ℝ^d`, `w = 0` included. -/
def Hhs (d : ℕ) : Set (EuclideanSpace ℝ (Fin d) → Bool) :=
  {h | ∃ w : EuclideanSpace ℝ (Fin d), h = hs w}

/-- **The class `H_hs` restricted to a public finite domain `X ⊆ ℝ^d`** (§4, p.25). Only the values on
the data enter `opt`, as for the base mission's `HthrOn`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its standard inner product. The
normal is not normalised: `w = 0` is the all-positive classifier the paper uses on p.32. -/
def HhsOn {d : ℕ} (X : Finset (EuclideanSpace ℝ (Fin d))) : Set (↥X → Bool) :=
  (fun h x => h (x : EuclideanSpace ℝ (Fin d))) '' Hhs d

end Supplement

end PrivOptTest


