-- Prove2me | Definitions.Def_ContactTopology_TwoArcJetDisk
-- name    : ContactTopology_TwoArcJetDisk
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T05:32:42.894992+00:00
-- url     : https://prove2.me/theorems/2b9309ce-40a4-4a5a-8990-f93cd1f863ee
-- title:
--   Polynomial disk and Hamiltonian field formulas for the two-arc contact model
-- statement:
--   Explicit formulas in standard contact three-space $\alpha=dZ-P\,dQ$: the polynomial $f(u,v)=u^2-v^2-(1+(u^2+v^2)^2)/4$, its disk one-form $\beta=(f_v-2fv,-f_u+2fu)$, the polynomial primitive $Z=\int_0^v\beta_1(u,s)\,ds$, momentum $P=Z_u-\beta_0$, and disk map $j=(u,P,Z)$. The interface also defines the standard contact Hamiltonian field $X_H=(-H_P,H_Q+PH_Z,H-PH_P)$ and the two explicit candidate arcs $j(\pm\sqrt{2-t^2-\sqrt{3-8t^2}},t)$. These are coordinate formulas only. Embedding, regularity, contactness, transversality and exact dividing-set claims are proved separately.
-- source:
--   Explicit derived local construction toward the bypass preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Theorem 2.2 and Proposition 3.3. These sources motivate the need for a convex Legendrian-boundary disk with multiple dividing arcs; the polynomial invariant form, its explicit embedded realization in standard contact three-space, the compact Hamiltonian extension and the complete two-arc description are auxiliary constructions supplied here, not statements quoted from Min. No bypass attachment, tightness classification, placement relative to the mission comparison knots, or Legendrian core classification is asserted.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function
noncomputable section
abbrev Space := Fin 3 → ℝ
def radiusSq (x : Plane) : ℝ := x 0^2+x 1^2
def dividing (x : Plane) : ℝ := x 0^2-x 1^2-(1+radiusSq x^2)/4
def beta (x : Plane) : Plane :=
  ![-2*x 1-x 1*radiusSq x-2*dividing x*x 1,
    -2*x 0+x 0*radiusSq x+2*dividing x*x 0]

def arcRadicand (t : ℝ) : ℝ := 2-t^2-Real.sqrt (3-8*t^2)
def arc (σ t : ℝ) : Plane := ![σ*Real.sqrt (arcRadicand t),t]


def jetHeight (x : Plane) : ℝ :=
  -x 0*x 1*(15*x 0^4+10*x 0^2*x 1^2-90*x 0^2+3*x 1^4+10*x 1^2+75)/30
def jetMomentum (x : Plane) : ℝ :=
  -x 1*(45*x 0^4+30*x 0^2*x 1^2-180*x 0^2+9*x 1^4+20*x 1^2+15)/15
def momentumU (x : Plane) : ℝ := -12*x 0^3*x 1-4*x 0*x 1^3+24*x 0*x 1
def momentumV (x : Plane) : ℝ := -3*radiusSq x^2+12*x 0^2-4*x 1^2-1
def jetDisk (x : Plane) : Space := ![x 0,jetMomentum x,jetHeight x]
def jetForm (p v : Space) : ℝ := v 2-p 1*v 0


def jetCoefficients (y : Space) : Space := ![-y 1,0,1]
def jetContactField (H : Space → ℝ) (y : Space) : Space :=
  ![-fderiv ℝ H y (Pi.single 1 1),
    fderiv ℝ H y (Pi.single 0 1)+y 1*fderiv ℝ H y (Pi.single 2 1),
    H y-y 1*fderiv ℝ H y (Pi.single 1 1)]


def jetDividingArc (σ : ℝ) (t : Icc (-1/2:ℝ) (1/2)) : Space := jetDisk (arc σ t.val)


end
end ContactTopology.TwoArcDisk


