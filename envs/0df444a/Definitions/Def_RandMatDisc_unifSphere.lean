-- Prove2me | Definitions.Def_RandMatDisc_unifSphere
-- name    : RandMatDisc_unifSphere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:48.483229+00:00
-- url     : https://prove2.me/theorems/f929c958-2ad7-4616-a0c4-3b4b705b22eb
-- title:
--   Uniform law on $\mathbb S^{D-1}$ and rotational invariance
-- statement:
--   Let $D\ge1$ and $\mathbb S^{D-1}=\{v\in\mathbb R^D:\|v\|_2=1\}$. The **uniform law** on $\mathbb S^{D-1}$ is the normalized surface measure, viewed as a probability measure on $\mathbb R^D$. It is obtained from Lebesgue measure by the cone construction: a set $S\subseteq\mathbb S^{D-1}$ receives mass proportional to $D\cdot\mathrm{vol}(\{rx:0<r<1,\ x\in S\})$, normalized to total mass one.
--
--   A random vector $X$ in $\mathbb R^D$ is **rotationally invariant** when $QX$ has the same law as $X$ for every orthogonal map $Q\in O(D)$.
--
--   These two notions express the conclusion of Lemmas 3.10 and 4.6: the direction $X/\|X\|_2$ of a rotationally invariant vector is uniform on the sphere.
--
--   **Formalization Note** The ambient space is $\mathbb R^\iota$ for a finite index type $\iota$ with $D=|\iota|$. The construction uses Mathlib's `Measure.toSphere` of the Lebesgue measure. For $D=0$ the sphere is empty and the measure is zero; no statement uses that case. Orthogonal maps are the linear isometric equivalences of $\mathbb R^\iota$.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), Lemma 4.6, p.31 (PDF p.33); Lemma 3.10, p.23 (PDF p.25)

import Mathlib

open MeasureTheory

namespace RandMatDisc

/-- The **uniform law on the unit sphere** `S^{D−1} = {v ∈ ℝᴰ : ‖v‖₂ = 1}` (Kızıldağ, Li,
arXiv:2610.01591, held file sha256 889af7fc…, Lemma 4.6, p.31, and Lemma 3.10, p.23): the
normalized surface measure, as a probability measure on the ambient space `ℝ^ι`.

It is built from Lebesgue measure through Mathlib's `Measure.toSphere`, which gives a set `s` of
the sphere the mass `D · vol({r x : 0 < r < 1, x ∈ s})` (the cone construction of the surface
measure), divided by its total mass and pushed forward to `ℝ^ι`.

**Formalization Note.** The column index set is any finite type `ι` with `D = card ι`. For
`card ι ≥ 1` this is a probability measure. For `card ι = 0` the sphere is empty and the measure
is zero; no statement of the mission uses that case. -/
noncomputable def unifSphere (ι : Type) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  ((((volume : Measure (EuclideanSpace ℝ ι)).toSphere) Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ ι)).toSphere).map Subtype.val

/-- A random vector `X : Ω → ℝ^ι` under `P` is **rotationally invariant** (p.23, p.31) when
`QX` has the law of `X` for every orthogonal map `Q ∈ O(D)`, i.e. every linear isometry
equivalence of `ℝ^ι`. -/
def IsRotInvariant {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EuclideanSpace ℝ ι) : Prop :=
  ∀ Q : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι,
    Measure.map (fun ω => Q (X ω)) P = Measure.map X P

end RandMatDisc


