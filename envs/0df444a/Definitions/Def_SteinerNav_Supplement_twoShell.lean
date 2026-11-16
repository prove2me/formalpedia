-- Prove2me | Definitions.Def_SteinerNav_Supplement_twoShell
-- name    : SteinerNav_Supplement_twoShell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:12:01.366282+00:00
-- url     : https://prove2.me/theorems/de37ab36-9a57-4a0a-916b-cf70107a5c3e
-- title:
--   The two-shell instance $P=S\cup T$ and its law
-- statement:
--   Fix integers $m\ge1$, $d\ge1$ and a radius parameter $\gamma>0$.
--
--   1. The sample space is a pair $\omega=(u,w)$ of $m$-tuples of points of $\mathbb R^d$, and its law draws all $2m$ coordinates $u_1,\dots,u_m,w_1,\dots,w_m$ independently and uniformly from the unit sphere $\mathbb S^{d-1}\subset\mathbb R^d$.
--   2. The **targets** are $T=\{u_1,\dots,u_m\}$, $m$ random unit vectors.
--   3. The **sources** are $S=\{\tfrac{\gamma}{2}w_1,\dots,\tfrac{\gamma}{2}w_m\}$, $m$ random vectors of norm $\gamma/2$.
--   4. The **two-shell instance** is $P=S\cup T$: the targets lie on the unit sphere, the sources on the concentric sphere of radius $\gamma/2$, all in independent uniformly random directions.
--
--   With $n=2m$ and $\gamma=\alpha-1$ this is the hard instance of the paper's lower bounds: every $\alpha$-navigable graph with Steiner points on it must be dense.
--
--   **Formalization Note** The uniform law on the sphere is the published `RegretBandits.Nonlinear.uniformSphere d` (normalized surface measure), and the joint law is the product measure. $P$ is the finite set of the $2m$ sampled points, so coincident samples (an event of probability zero for $d\ge2$) would be merged.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee62135a42ef49d815773f6af7f50ba344b9460d6007d849529b707b183), §5.1 "The hard instance", p.10 (PDF p.10)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_SteinerNav_annularCandidates

namespace SteinerNav.Supplement

open MeasureTheory RegretBandits.Nonlinear

/-- The sample space of the two-shell instance with `m` targets and `m` sources in `ℝ^d`: a pair of
`m`-tuples of points, the first holding the target directions, the second the source directions
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §5.1 "The hard instance", p.10). -/
abbrev TwoShellSpace (m d : ℕ) : Type := (Fin m → Pt d) × (Fin m → Pt d)

/-- The law of the two-shell instance: all `2m` directions are independent and uniform on the unit
sphere `S^{d−1}` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §5.1, p.10).

**Formalization Note** Each coordinate has the published law `RegretBandits.Nonlinear.uniformSphere d`
(normalized surface measure, a probability measure for `d ≥ 1`); the joint law is the product. -/
noncomputable def twoShellLaw (m d : ℕ) : Measure (TwoShellSpace m d) :=
  (Measure.pi fun _ : Fin m => uniformSphere d).prod (Measure.pi fun _ : Fin m => uniformSphere d)

/-- The targets `T` of the two-shell instance: the `m` random unit vectors `ω.1 i`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §5.1, p.10). -/
noncomputable def twoShellTargets {m d : ℕ} (ω : TwoShellSpace m d) : Finset (Pt d) :=
  Finset.univ.image ω.1

/-- The sources `S` of the two-shell instance: the `m` random vectors of norm `γ/2`, that is
`(γ/2) • ω.2 i` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §5.1, p.10). -/
noncomputable def twoShellSources {m d : ℕ} (γ : ℝ) (ω : TwoShellSpace m d) : Finset (Pt d) :=
  Finset.univ.image fun i => (γ / 2) • ω.2 i

/-- The two-shell instance `P = S ∪ T` with inner radius `γ/2`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §5.1, p.10).

**Formalization Note** `P` is the `Finset` of the `2m` sampled points; coincident points (an event of
probability zero for `d ≥ 2`) would be merged. -/
noncomputable def twoShell {m d : ℕ} (γ : ℝ) (ω : TwoShellSpace m d) : Finset (Pt d) :=
  twoShellSources γ ω ∪ twoShellTargets ω

end SteinerNav.Supplement


