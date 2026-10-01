-- Prove2me | Definitions.Def_BCWCentralizer_Basic
-- name    : BCWCentralizer_Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:26:58.899068+00:00
-- url     : https://prove2.me/theorems/24f41c28-f1a1-4c54-8705-5629ebe7e5bb
-- title:
--   $\mathrm{Diff}^1(M)$, the $C^1$ topology, and trivial (Lipschitz) centralizers
-- statement:
--   Basic objects for the mission, for a smooth manifold $M$ modelled on $\mathbb R^d$.
--
--   1. $\mathrm{Diff}^1(M)$: the $C^1$ diffeomorphisms of $M$.
--   2. The $C^1$ topology on $\mathrm{Diff}^1(M)$: the coarsest topology making $f\mapsto Tf$ continuous, where $Tf:TM\to TM$ is the tangent map and continuous self-maps of $TM$ carry the compact-open topology.
--   3. $f^n$ for $n\in\mathbb Z$, as a bijection of $M$.
--   4. $f$ has *trivial centralizer* if every $g\in\mathrm{Diff}^1(M)$ with $f\circ g=g\circ f$ equals $f^n$ for some $n\in\mathbb Z$.
--   5. A self-map $h$ is *locally Lipschitz in charts* if around every point $x$ its local expression in the preferred charts at $x$ and $h(x)$ is Lipschitz on a neighbourhood of the chart image of $x$; a homeomorphism $g$ is *bi-Lipschitz* if $g$ and $g^{-1}$ both are.
--   6. $f$ has *trivial Lipschitz centralizer* $Z^{\mathrm{Lip}}(f)=\langle f\rangle$ if every bi-Lipschitz homeomorphism commuting with $f$ is an integer power of $f$.
--
--   These are the notions of Section 1.1 ($Z^r(f)$, trivial centralizer) and Section 2.5 ($\mathrm{Lip}(M)$, $Z^{\mathrm{Lip}}(f)$) of the paper.
--
--   **Formalization Note** On a compact manifold the compact-open topology on tangent maps agrees with the usual $C^1$ topology, and chart-local Lipschitz continuity agrees with Lipschitz continuity for any Riemannian distance. The topology is registered as a scoped instance in the namespace `BCWCentralizer`.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, Sections 1.1, 2.1, 2.2, 2.5

import Mathlib

open scoped Manifold ContDiff Topology

namespace BCWCentralizer

noncomputable section

/-- The group-like space `Diff¹(M)` of `C¹` diffeomorphisms of a smooth manifold `M` modelled on
`ℝ^d` (Euclidean model with corners, so `M` has no boundary). -/
abbrev Diff1 (d : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] : Type _ :=
  M ≃ₘ^1⟮𝓡 d, 𝓡 d⟯ M

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [IsManifold (𝓡 d) ∞ M]

/-- The tangent map `Tf : TM → TM` of a `C¹` diffeomorphism, as a continuous map. -/
def tangentMapCM (f : Diff1 d M) :
    C(TangentBundle (𝓡 d) M, TangentBundle (𝓡 d) M) :=
  ⟨tangentMap (𝓡 d) (𝓡 d) f, f.contMDiff.continuous_tangentMap le_rfl⟩

/-- The `C¹` topology on `Diff¹(M)`: the topology induced by `f ↦ Tf` from the compact-open
topology on continuous self-maps of the tangent bundle `TM`. -/
abbrev c1Topology : TopologicalSpace (Diff1 d M) :=
  TopologicalSpace.induced tangentMapCM ContinuousMap.compactOpen

scoped instance : TopologicalSpace (Diff1 d M) := c1Topology

/-- The `n`-th power (`n ∈ ℤ`) of a diffeomorphism, as a bijection of `M`. -/
def zpowPerm (f : Diff1 d M) (n : ℤ) : Equiv.Perm M :=
  (f.toEquiv : Equiv.Perm M) ^ n

/-- `f` has trivial `C¹` centralizer: every `C¹` diffeomorphism `g` with `f ∘ g = g ∘ f`
is an integer power of `f`. -/
def HasTrivialCentralizer (f : Diff1 d M) : Prop :=
  ∀ g : Diff1 d M, (⇑f ∘ ⇑g = ⇑g ∘ ⇑f) → ∃ n : ℤ, ⇑g = ⇑(zpowPerm f n)

/-- A self-map `h` of `M` is locally Lipschitz in charts: around every point `x`, the local
representative of `h` in the preferred charts at `x` and at `h x` is Lipschitz on some
neighbourhood of the image of `x`. On a compact manifold this is equivalent to `h` being
Lipschitz for (any) Riemannian distance. -/
def IsLocallyLipschitzInCharts (h : M → M) : Prop :=
  ∀ x : M, ∃ K : NNReal, ∃ s ∈ 𝓝 (extChartAt (𝓡 d) x x),
    LipschitzOnWith K (extChartAt (𝓡 d) (h x) ∘ h ∘ (extChartAt (𝓡 d) x).symm) s

/-- A homeomorphism `g` of `M` is bi-Lipschitz (a lipeomorphism) if `g` and `g⁻¹` are both
locally Lipschitz in charts. -/
def IsBiLipschitz (g : M ≃ₜ M) : Prop :=
  IsLocallyLipschitzInCharts (d := d) ⇑g ∧ IsLocallyLipschitzInCharts (d := d) ⇑g.symm

/-- `f` has trivial Lipschitz centralizer `Z^{Lip}(f)`: every bi-Lipschitz homeomorphism `g`
with `f ∘ g = g ∘ f` is an integer power of `f`. -/
def HasTrivialLipCentralizer (f : Diff1 d M) : Prop :=
  ∀ g : M ≃ₜ M, IsBiLipschitz (d := d) g → (⇑f ∘ ⇑g = ⇑g ∘ ⇑f) →
    ∃ n : ℤ, ⇑g = ⇑(zpowPerm f n)

end

end BCWCentralizer


