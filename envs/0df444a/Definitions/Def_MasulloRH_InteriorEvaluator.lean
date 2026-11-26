-- Prove2me | Definitions.Def_MasulloRH_InteriorEvaluator
-- name    : MasulloRH_InteriorEvaluator
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T14:05:33.654182+00:00
-- url     : https://prove2.me/theorems/56288084-20c7-4a74-8ace-7f6e0e9ebe9f
-- title:
--   An executable rational checker for the six-term Masullo height-two curvature budgets
-- statement:
--   This function evaluates both signed endpoints, the second derivative on an entire cell, the geometric tail, and the right endpoint weight for the published eleven-translate height-two witness. Each call to passes uses only integer or rational arithmetic and returns a Boolean. The exponentials and integer powers use outward interval arithmetic.
-- source:
--   The Masullo height-two certificate https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its central curvature-row theorem https://prove2.me/theorems/b0533253-e9c5-595e-be4f-d607f9549942.

import Definitions.Def_MasulloRH_CentralInterval
import Definitions.Def_MasulloRH_HeightTwoCurvature

open MasulloRH.CentralInterval MasulloRH.HeightTwoCurvature

namespace MasulloRH.InteriorEvaluator

abbrev Index := Fin 6 × Fin 3

def scaleNat (t : Fin 3) : ℕ := ![1,2,4] t
def powerIndex (i : Index) : ℕ := ((i.1.val+1)*scaleNat i.2)^2
def signQ (i : Index) : ℚ := ![1,-3,2] i.2

def piB : Box := (3141592653589793/1000000000000000,3141592653589794/1000000000000000)
def pulseFactor : Box := (1692568750643/1000000000000,1692568750644/1000000000000)

structure Params where
  u : Box
  q : Box
  pref : Box

def params (b : Bool) (z : Box) : Params :=
  let u := mulB (if b then mulB piB (point (1/16)) else piB)
    (expB (mulB (point (if b then -2 else 2)) z))
  ⟨u,expB (negB u),if b then expB (negB z) else point 2⟩

def curvaturePoly (b : Bool) (u : Box) : Box :=
  subB (mulB (point 4) (sqB (subB u (point (if b then 1 else 1/2)))))
    (point (if b then 3 else 1))

def term (d : Params) (i : Index) := mulB d.pref (powB d.q (powerIndex i))
def thetaV (d : Params) : Box := ∑ i, mulB (point (signQ i)) (term d i)
def thetaD (b : Bool) (d : Params) : Box :=
  ∑ i, mulB (point (signQ i))
    (mulB (curvaturePoly b (mulB (point (powerIndex i)) d.u)) (term d i))

def tailDen (d : Params) := 1 - (powB d.q 15).2
def tailU (d : Params) : ℚ := 6 * d.pref.2 * (powB d.q 49).2 / tailDen d

def pulseV (z : Box) := mulB pulseFactor (expB (mulB (point (-9)) (sqB z)))
def pulseD (z : Box) := mulB (subB (mulB (point 324) (sqB z)) (point 18)) (pulseV z)

def shifted (j : ℕ) (i : Fin 11) (x : Box) :=
  params (reflected j i) (subB x (point (HeightTwoWitness.shiftsQ i)))
def surrogateV (j : ℕ) (x : Box) : Box :=
  subB (pulseV x) (∑ i, mulB (point (HeightTwoWitness.coeffsQ i)) (thetaV (shifted j i x)))
def surrogateD (j : ℕ) (x : Box) : Box :=
  subB (pulseD x) (∑ i, mulB (point (HeightTwoWitness.coeffsQ i))
    (thetaD (reflected j i) (shifted j i x)))
def tailSum (j : ℕ) (x : Box) := ∑ i, |HeightTwoWitness.coeffsQ i| * tailU (shifted j i x)
def cell (j : ℕ) : Box := (edgeQ j,edgeQ (j+1))
def endBound (j : ℕ) := max (mag (surrogateV j (point (edgeQ j)))) (mag (surrogateV j (point (edgeQ (j+1)))))
def curvBound (j : ℕ) := mag (surrogateD j (cell j))
def weightCap (j : ℕ) := (expPoint (3/2*edgeQ (j+1) + 11/24*|edgeQ (j+1)|)).2
def energyCap (j : ℕ) :=
  weightCap j * (endBound j + curvBound j/131072 + tailSum j (cell j))^2
def passes (j : ℕ) : Bool :=
  decide ((∀ i : Fin 11, 0 < tailDen (shifted j i (cell j))) ∧
    0 ≤ curvBound j ∧ energyCap j ≤ (cap j : ℚ)/1000000)

end MasulloRH.InteriorEvaluator


