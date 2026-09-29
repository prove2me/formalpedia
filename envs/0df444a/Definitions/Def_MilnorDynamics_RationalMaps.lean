-- Prove2me | Definitions.Def_MilnorDynamics_RationalMaps
-- name    : MilnorDynamics_RationalMaps
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T10:39:04.832329+00:00
-- url     : https://prove2.me/theorems/3ce00184-eb12-49c1-9d49-90339b2f9199
-- title:
--   Rational maps of the Riemann sphere, multipliers, Fatou and Julia sets (Milnor §4)
-- statement:
--   The objects of Milnor's §4 (*Fatou and Julia: Dynamics on the Riemann Sphere*), for rational self-maps of the Riemann sphere $\hat{\mathbb C}=\mathbb C\cup\{\infty\}$.
--
--   1. A **rational map** is a quotient $f(z)=p(z)/q(z)$ of two complex polynomials with no common root, $q\neq0$; its **degree** is $d=\max(\deg p,\deg q)$. As a self-map of $\hat{\mathbb C}$ it sends $z$ to $p(z)/q(z)$, a pole to $\infty$, and $\infty$ to $\lim_{z\to\infty}p(z)/q(z)$.
--   2. The **multiplier** of a periodic point $z_0$ of period $m$ is the derivative of $f^{\circ m}$ at $z_0$ computed in a local coordinate: $z$ near a finite point, $1/z$ near $\infty$. The orbit is **attracting**, **repelling** or **indifferent** according as $|\lambda|<1$, $|\lambda|>1$ or $|\lambda|=1$, and **superattracting** when $\lambda=0$.
--   3. The **Fatou set** of $f$ is the set of points having a neighbourhood on which the iterates $\{f^{\circ n}\}_{n\ge0}$ form a normal family; the **Julia set** $J(f)$ is its complement.
--   4. The **basin of attraction** of an attracting periodic orbit consists of the points whose orbits converge to the orbit.
--   5. The **grand orbit** of $z$ is $\{z' : f^{\circ m}(z)=f^{\circ n}(z')\text{ for some }m,n\ge0\}$; $z$ is **grand orbit finite (exceptional)** if its grand orbit is finite, and $\mathcal E(f)$ denotes the set of such points.
--
--   **Formalization Note** The sphere is `OnePoint ℂ`. A rational map is the data of two coprime polynomials, so the degree is available without a preimage-counting theorem. Normality near a point is tested in the standard coordinate of the sphere at that point (the identity at finite points, $w\mapsto1/w$ at $\infty$), using the notion of a normal family from the first mission of this series. The period used in the multiplier is the minimal period; derivatives use Mathlib's `deriv`, which returns $0$ at points of non-differentiability.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §4, pp. 39-47 (definition of the Fatou and Julia sets p. 40, rational maps p. 41, Definition 4.5 of multiplier pp. 44-45, basin of attraction p. 45, grand orbits p. 47)

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set Polynomial

namespace MilnorDynamics

/-- A rational map `z ↦ p(z)/q(z)` of the Riemann sphere, given by coprime complex
polynomials `p = num`, `q = den` with `q ≠ 0`. -/
structure RationalMap where
  num : ℂ[X]
  den : ℂ[X]
  den_ne_zero : den ≠ 0
  coprime : IsCoprime num den

namespace RationalMap

/-- The degree of `p/q`: the maximum of the degrees of `p` and `q`. -/
noncomputable def degree (f : RationalMap) : ℕ :=
  max f.num.natDegree f.den.natDegree

/-- The rational map as a self-map of the Riemann sphere `ℂ ∪ {∞}`: `z ↦ p(z)/q(z)` if
`q(z) ≠ 0`, `z ↦ ∞` if `q(z) = 0`, and `∞ ↦ lim_{z → ∞} p(z)/q(z)`. -/
noncomputable def toFun (f : RationalMap) : OnePoint ℂ → OnePoint ℂ
  | some z => if f.den.eval z = 0 then ∞ else ((f.num.eval z / f.den.eval z : ℂ) : OnePoint ℂ)
  | none =>
    if f.den.natDegree < f.num.natDegree then ∞
    else ((f.num.coeff f.den.natDegree / f.den.leadingCoeff : ℂ) : OnePoint ℂ)

end RationalMap

/-- The coordinate `w ↦ 1/w` from `ℂ` to the Riemann sphere, sending `0 ↦ ∞`
(a chart of the sphere around `∞`). -/
noncomputable def invChart (w : ℂ) : OnePoint ℂ :=
  if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ)

/-- The derivative of a self-map `g` of the Riemann sphere at a fixed point `p = g p`,
computed in the standard coordinate around `p` (`z` if `p` is finite, `1/z` if `p = ∞`). -/
noncomputable def derivAtFixedPoint (g : OnePoint ℂ → OnePoint ℂ) : OnePoint ℂ → ℂ
  | some z => deriv (fun w : ℂ => chartFinite (g (w : OnePoint ℂ))) z
  | none => deriv (fun w : ℂ => chartInfinite (g (invChart w))) 0

/-- The multiplier of a periodic point `p` of `g`: the derivative of `g^{∘m}` at `p`, where
`m` is the (minimal) period of `p`. -/
noncomputable def multiplier (g : OnePoint ℂ → OnePoint ℂ) (p : OnePoint ℂ) : ℂ :=
  derivAtFixedPoint (g^[Function.minimalPeriod g p]) p

/-- A family `𝓕` of self-maps of the Riemann sphere is normal on some neighbourhood of `p`
(read in the standard coordinate around `p`). -/
def IsNormalNear (𝓕 : Set (OnePoint ℂ → OnePoint ℂ)) : OnePoint ℂ → Prop
  | some z => ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧
      IsNormalFamily V ((fun g : OnePoint ℂ → OnePoint ℂ => fun w : ℂ => g (w : OnePoint ℂ)) '' 𝓕)
  | none => ∃ V : Set ℂ, IsOpen V ∧ (0 : ℂ) ∈ V ∧
      IsNormalFamily V ((fun g : OnePoint ℂ → OnePoint ℂ => fun w : ℂ => g (invChart w)) '' 𝓕)

/-- The Fatou set of a self-map `g` of the Riemann sphere: the points having a neighbourhood
on which the iterates `{g^{∘n} : n ≥ 0}` form a normal family. -/
def fatouSet (g : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {p | IsNormalNear (Set.range fun n : ℕ => g^[n]) p}

/-- The Julia set: the complement of the Fatou set. -/
def juliaSet (g : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  (fatouSet g)ᶜ

/-- The grand orbit of `z` under `g`: all `z'` with `g^{∘m} z = g^{∘n} z'` for some `m, n ≥ 0`. -/
def grandOrbit (g : OnePoint ℂ → OnePoint ℂ) (z : OnePoint ℂ) : Set (OnePoint ℂ) :=
  {z' | ∃ m n : ℕ, g^[m] z = g^[n] z'}

/-- The exceptional set `𝓔(g)`: the points whose grand orbit is finite. -/
def exceptionalSet (g : OnePoint ℂ → OnePoint ℂ) : Set (OnePoint ℂ) :=
  {z | (grandOrbit g z).Finite}

/-- The basin of attraction of the periodic orbit of `p` (of period `m`): all points `z`
whose iterates `g^{∘ m k}(z)` converge, as `k → ∞`, to some point of the orbit of `p`. -/
def basin (g : OnePoint ℂ → OnePoint ℂ) (p : OnePoint ℂ) : Set (OnePoint ℂ) :=
  {z | ∃ j : ℕ, Tendsto (fun k : ℕ => g^[Function.minimalPeriod g p * k] z) atTop
      (nhds (g^[j] p))}

end MilnorDynamics


