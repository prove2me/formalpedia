-- Prove2me | Definitions.Def_ContactTopology_RetrogradeMovie
-- name    : ContactTopology_RetrogradeMovie
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:27:35.26879+00:00
-- url     : https://prove2.me/theorems/3eba9316-b076-4b24-8746-c058f6022575
-- title:
--   An explicit retrograde contact movie and its dividing arcs
-- statement:
--   In standard contact space with coordinates $(Q,P,Z)$ and contact form $\alpha=dZ-P\,dQ$, define
--   $$S_t(x,y)=(x,xy-t,xt+(1-x^2)y),\qquad E(Q,P,Z)=(0,P,Z).$$
--   The characteristic vector field in the parameter plane is $X_t=(1-x^2,3xy-2t)$. The observation rectangle is $B=[-2,2]\times[-1,1]$.
--
--   For $0<t<1$, put
--   $$a_t=\frac{\sqrt{t^2+4}-t}{2},\qquad b_t=\frac{\sqrt{t^2+4}+t}{2}.$$
--   The three dividing arcs are the images under $S_t$ of $(x,-tx/(1-x^2))$ on the intervals $[-2,-b_t]$, $[-a_t,a_t]$, and $[b_t,2]$. Reflection $(Q,P,Z)\mapsto(Q,-P,-Z)$ describes the negative-parameter arcs. The complete-flow formula is $\Phi_s(Q,P,Z)=(Q,e^sP,e^sZ)$.
--
--   This file contains only coordinate data. Contactness, transversality, the exceptional-slice obstruction, and the geometry of all three physical arcs are proved in the associated theorem.
-- source:
--   Original explicit polynomial realization of a retrograde saddle connection and its three-arc dividing switch in standard contact space. Context and event description: Ko Honda, Gluing tight contact structures, https://arxiv.org/pdf/math/0102029, Section 2.2.3, Lemma 2.10 proof, printed pp. 17-18 (published Duke Mathematical Journal 115(3), 435-478, 2002, Section 3.2.3, Lemma 3.10). Also Hyunki Min, https://arxiv.org/html/2207.03590v2, Theorem 2.5 and Theorem 2.6. The coordinate formulas and their proofs are supplied here as a separate auxiliary construction; this is not a genericity theorem, a local-normal-form uniqueness theorem, or a proof of bypass attachment.

import Definitions.Def_ContactTopology_TwoArcJetDisk
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function
noncomputable section
def model (t : ℝ) (u : Plane) : Space :=
  ![u 0,u 0*u 1-t,u 0*t+(1-u 0^2)*u 1]

def euler (p : Space) : Space := ![0,p 1,p 2]

def characteristic (t : ℝ) (u : Plane) : Plane := ![1-u 0^2,3*u 0*u 1-2*t]

def dividing (t : ℝ) (u : Plane) : ℝ := u 0*t+(1-u 0^2)*u 1


def inner (t : ℝ) : ℝ := (Real.sqrt (t^2+4)-t)/2

def outer (t : ℝ) : ℝ := (Real.sqrt (t^2+4)+t)/2

def box : Set Plane := {u | |u 0|≤2 ∧ |u 1|≤1}

def graph (t x : ℝ) : Plane := ![x,-t*x/(1-x^2)]

def interval (t : ℝ) (j : Fin 3) : Set ℝ :=
  ![Icc (-2) (-outer t),Icc (-inner t) (inner t),Icc (outer t) 2] j

def bounds (t : ℝ) (j : Fin 3) : ℝ × ℝ :=
  ![(-2,-outer t),(-inner t,inner t),(outer t,2)] j

def physicalArc (t : ℝ) (j : Fin 3) (x : Icc (bounds t j).1 (bounds t j).2) : Space :=
  model t (graph t x.val)


def leftEnd (t : ℝ) (j : Fin 3) : Plane :=
  ![![-2,-2*t/3],![-inner t,1],![outer t,1]] j

def rightEnd (t : ℝ) (j : Fin 3) : Plane :=
  ![![-outer t,-1],![inner t,-1],![2,2*t/3]] j


def reflect (p : Space) : Space := ![p 0,-p 1,-p 2]

def mirror (u : Plane) : Plane := ![u 0,-u 1]

def physicalZero (t : ℝ) : Set Space :=
  {p | ∃ u ∈ box, model t u=p ∧ jetForm p (euler p)=0}


def boxBoundary : Set Plane := {u | u ∈ box ∧ (|u 0|=2 ∨ |u 1|=1)}


def connection (x : ℝ) : Plane := ![x,0]


def flow (s : ℝ) (p : Space) : Space := ![p 0,Real.exp s*p 1,Real.exp s*p 2]


end
end ContactTopology.RetrogradeMovie


