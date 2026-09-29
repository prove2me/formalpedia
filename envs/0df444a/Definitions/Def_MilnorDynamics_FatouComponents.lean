-- Prove2me | Definitions.Def_MilnorDynamics_FatouComponents
-- name    : MilnorDynamics_FatouComponents
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T12:06:00.814847+00:00
-- url     : https://prove2.me/theorems/280ded3c-447a-4d76-a159-c6df6ed12452
-- title:
--   Fatou components, immediate basins, Siegel disks and Herman rings
-- statement:
--   Notions from Milnor's §§4, 8, 11, 15 and 16 describing the components of the Fatou set of a self-map $g$ of the Riemann sphere $\hat{\mathbb C}=\mathbb C\cup\{\infty\}$ (for the Fatou set $F(g)$, the basin of attraction and holomorphy of maps into $\hat{\mathbb C}$ see the imported definitions `MilnorDynamics_RationalMaps` and `MilnorDynamics_NormalFamilies`).
--
--   1. A **Fatou component** of $g$ is a connected component of the Fatou set $F(g)$.
--   2. For a periodic point $p$, the **immediate basin** of $p$ is the connected component, containing $p$, of the basin of attraction of the orbit of $p$.
--   3. The **round annulus** of outer radius $r$ is $A_r=\{w\in\mathbb C: 1<|w|<r\}$.
--   4. A Fatou component $U$ is a **Siegel disk** if $g$ is conformally conjugate on $U$ to an irrational rotation of the unit disk $\mathbb D$: there are an irrational $\theta\in\mathbb R$ and an injective holomorphic map $h:\mathbb D\to\hat{\mathbb C}$ with $h(\mathbb D)=U$ and
--
--   $$g(h(w))=h\bigl(e^{2\pi i\theta}w\bigr)\qquad (w\in\mathbb D).$$
--
--   5. A Fatou component $U$ is a **Herman ring** if $g$ is conformally conjugate on $U$ to an irrational rotation of a round annulus: there are an irrational $\theta$, a radius $r>1$ and an injective holomorphic map $h:A_r\to\hat{\mathbb C}$ with $h(A_r)=U$ and $g(h(w))=h(e^{2\pi i\theta}w)$ for $w\in A_r$.
--
--   These are the objects appearing in the Sullivan classification of Fatou components (Theorem 16.1) and in the no wandering domains theorem (Theorem 16.4).
--
--   **Formalization Note** Holomorphy of $h$ is the chart-wise notion `IsHolomorphicOn` of the imported layer (continuity plus complex differentiability in the charts $z$ and $1/z$ of $\hat{\mathbb C}$). An injective holomorphic map onto $U$ is automatically a biholomorphism onto $U$, so the parametrisation $h$ encodes "conformally isomorphic". Milnor's definition of a Herman ring allows *some iterate* of $g$ to be an irrational rotation; for a component with $g(U)=U$ (the only case used in Theorem 16.1) this is equivalent to $g$ itself being one, because every automorphism of an annulus is a rotation or a rotation composed with the involution $w\mapsto r/w$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §4 p. 40 (Definition 4.2, Fatou set), §8 p. 79 (immediate basin), §11 p. 126 (Definition: Siegel disk), §15 p. 161 (Definition: Herman ring), §16 p. 167 (Fatou component)

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- `U` is a Fatou component of `g`: a connected component of the Fatou set of `g`. -/
def IsFatouComponent (g : OnePoint ℂ → OnePoint ℂ) (U : Set (OnePoint ℂ)) : Prop :=
  ∃ z ∈ fatouSet g, U = connectedComponentIn (fatouSet g) z

/-- The immediate basin of a periodic point `p`: the connected component containing `p` of the
basin of attraction of the orbit of `p`. -/
def immediateBasin (g : OnePoint ℂ → OnePoint ℂ) (p : OnePoint ℂ) : Set (OnePoint ℂ) :=
  connectedComponentIn (basin g p) p

/-- The round annulus `{w ∈ ℂ : 1 < |w| < r}`. -/
def roundAnnulus (r : ℝ) : Set ℂ := {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < r}

/-- `U` is a Siegel disk of `g`: a Fatou component on which `g` is conformally conjugate to an
irrational rotation of the unit disk. That is, there are an irrational `θ` and a holomorphic
injective `h` from the unit disk `𝔻` onto `U` with `g (h w) = h (e^{2πiθ} w)` for `w ∈ 𝔻`. -/
def IsSiegelDisk (g : OnePoint ℂ → OnePoint ℂ) (U : Set (OnePoint ℂ)) : Prop :=
  IsFatouComponent g U ∧ ∃ (θ : ℝ) (h : ℂ → OnePoint ℂ), Irrational θ ∧
    IsHolomorphicOn (Metric.ball 0 1) h ∧ InjOn h (Metric.ball 0 1) ∧
    h '' Metric.ball 0 1 = U ∧
    ∀ w ∈ Metric.ball (0 : ℂ) 1, g (h w) = h (Complex.exp (2 * Real.pi * Complex.I * θ) * w)

/-- `U` is a Herman ring of `g`: a Fatou component on which `g` is conformally conjugate to an
irrational rotation of a round annulus `{1 < |w| < r}` (`r > 1`). That is, there are an
irrational `θ`, a radius `r > 1` and a holomorphic injective `h` from the annulus onto `U` with
`g (h w) = h (e^{2πiθ} w)` on the annulus. -/
def IsHermanRing (g : OnePoint ℂ → OnePoint ℂ) (U : Set (OnePoint ℂ)) : Prop :=
  IsFatouComponent g U ∧ ∃ (θ r : ℝ) (h : ℂ → OnePoint ℂ), Irrational θ ∧ 1 < r ∧
    IsHolomorphicOn (roundAnnulus r) h ∧ InjOn h (roundAnnulus r) ∧
    h '' roundAnnulus r = U ∧
    ∀ w ∈ roundAnnulus r, g (h w) = h (Complex.exp (2 * Real.pi * Complex.I * θ) * w)

end MilnorDynamics


