-- Prove2me | Definitions.Def_BorderD4_Psi
-- name    : BorderD4_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:10.758461+00:00
-- url     : https://prove2.me/theorems/effe67a4-d7da-4bec-8d67-dab546adf1c7
-- title:
--   The scaling homomorphism $\Psi$
-- statement:
--   $\Psi:F[[\varepsilon]][x]\to F[[\varepsilon]][u][[z]]$ is the $F[[\varepsilon]]$-algebra homomorphism with
--   $$\Psi(x_i)=z\cdot x_i\ (i\in T),\qquad \Psi(x_a)=\varphi_a(\varepsilon,z\cdot u)\ (a\notin T).$$
--   The helper `scale` is $g(\varepsilon,u)\mapsto g(\varepsilon,zu)$, whose coefficient of $z^d$ is the part of $g$ of degree $d$ in $u$. `PsiF` is $\Psi$ followed by the inclusion into the fraction field.
--
--   **Formalization Note** The page works in $K=L((\varepsilon))$ with $L=F(u)((z))$, which contains this fraction field (p.65).
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64

import Mathlib
import Definitions.Def_BorderD4_IsEpsUnit
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The ring `F[[ε]][u][[z]]`. -/
abbrev ZRing (F τ : Type*) [Field F] := PowerSeries (MvPolynomial τ F⟦X⟧)

/-- The fraction field of `F[[ε]][u][[z]]`.

**Formalization Note** The page works in the field `K = L((ε))`, `L = F(u)((z))`, which contains this fraction
field by the injection on p.65. Inverses of nonzero elements and the quotient rule agree in the two fields. -/
abbrev ZFrac (F τ : Type*) [Field F] := FractionRing (ZRing F τ)

section

variable {F σ : Type*} [Field F] [DecidableEq σ]

/-- The substitution `g(ε, u) ↦ g(ε, zu)`, from `F[[ε, u]]` to `F[[ε]][u][[z]]`: the coefficient of `z^d` is the
component of `g` of degree `d` in `u`, a polynomial in `u` over `F[[ε]]`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64. -/
noncomputable def scale {τ : Type*} [Fintype τ] [DecidableEq τ] (g : EpsSeries F τ) : ZRing F τ :=
  PowerSeries.mk fun d => ∑ m ∈ Finset.finsuppAntidiag Finset.univ d,
    monomial m (PowerSeries.mk fun v => MvPowerSeries.coeff m (PowerSeries.coeff v g))

/-- The `F[[ε]]`-algebra homomorphism `Ψ : F[[ε]][x] → F[[ε]][u][[z]]` with `Ψ(x_i) = z · x_i` for `i ∈ T` and
`Ψ(x_a) = φ_a(ε, z · u)` for `a ∉ T`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64. -/
noncomputable def Psi (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T) :
    MvPolynomial σ F⟦X⟧ →+* ZRing F T :=
  eval₂Hom ((PowerSeries.C).comp MvPolynomial.C) fun i =>
    if h : i ∈ T then PowerSeries.X * PowerSeries.C (MvPolynomial.X (⟨i, h⟩ : T))
    else scale (φ ⟨i, h⟩)

/-- `Ψ(p)` as an element of the fraction field. -/
noncomputable def PsiF (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T) (p : MvPolynomial σ F⟦X⟧) :
    ZFrac F T :=
  algebraMap (ZRing F T) (ZFrac F T) (Psi T φ p)

end

end BorderD4


