-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_continuation
-- name    : XinMartingaleInventory_Minimax_continuation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:58:14.411493+00:00
-- url     : https://prove2.me/theorems/551ad39e-57f6-4278-91e4-40a2d516211a
-- title:
--   Continuation polynomials and affine majorants
-- statement:
--   The barred functions are the explicit polynomials and affine functions on pp.21–23. The crossing z_x^n is the infimum of d∈[0,U] such that β_d^n≥x−d. The barred continuation uses its printed piecewise polynomial formula, including the special zero-demand endpoints, independently of the minimizing-objective identity. For n≥2, f^n is the one-period cost plus the barred continuation at horizon n−1. The thresholds α, ζ, script A and aleph use the respective Γ, crossing and Υ indices of p.22. K is the line through (0,nx) and (aleph,f(aleph)); L_j is the chord through consecutive A breakpoints. A general chord and real two-atom law are supplied for the literal real-endpoint Lemma 10; realAtoms embeds rational atom masses into real atom masses.
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.21 (PDF p.21)

import Definitions.Def_XinMartingaleInventory_Minimax_thresholds

noncomputable section

namespace XinMartingaleInventory.Minimax

def barredF (U b : ℚ) (n : ℕ) (j : ℤ) (x d : ℝ) : ℝ :=
  (n : ℝ)*x + (((b : ℝ)-1)*n-(b : ℝ)*j-((b : ℝ)+n)/(A U b n j : ℝ)*x)*d +
    ((b : ℝ)+n)/(A U b n j : ℝ)*d^2

def barredG (U b : ℚ) (n : ℕ) (j : ℤ) (d : ℝ) : ℝ :=
  (n : ℝ)*(B U b n (j+1) : ℝ) +
    ((n : ℝ)*b-((b : ℝ)+1)*((j : ℝ)+1))*d

def crossing (U b : ℚ) (n : ℕ) (x : ℝ) : ℝ :=
  sInf {d : ℝ | d ∈ Set.Icc 0 (U : ℝ) ∧ x-d ≤ (beta U b n d : ℝ)}

/-- Independently specified piecewise polynomials, not defined using Lemma 7. -/
def continuation (U b : ℚ) (n : ℕ) (x d : ℝ) : ℝ :=
  if d = 0 ∧ x = 0 then barredG U b n (-1) 0 else
  if d = 0 ∧ x = (U : ℝ) then barredF U b n ((n : ℤ)-1) x 0 else
  if d < crossing U b n x then barredF U b n (upsilon U b (n-1) (x-d)) x d
  else barredG U b n (gamma U b n d - 1) d

def nextObjective (U b : ℚ) (n : ℕ) (x d : ℝ) : ℝ :=
  cost b x d + continuation U b (n-1) x d

def alpha (U b : ℚ) (n : ℕ) (x : ℝ) : ℝ := A U b n (gamma U b (n-1) x)
def zeta (U b : ℚ) (n : ℕ) (x : ℝ) : ℤ := gamma U b n (crossing U b n x)
def geomA (U b : ℚ) (n : ℕ) (x : ℝ) : ℝ := A U b n (zeta U b (n-1) x)
def aleph (U b : ℚ) (n : ℕ) (x : ℝ) : ℝ := A U b n (upsilon U b (n-1) x)

/-- The line through (L,f(L)) and (R,f(R)). -/
def chord (f : ℝ → ℝ) (L R d : ℝ) : ℝ :=
  (f R-f L)/(R-L)*d + (R*f L-L*f R)/(R-L)

def majorantK (U b : ℚ) (n : ℕ) (x d : ℝ) : ℝ :=
  (nextObjective U b n x (aleph U b n x)-(n : ℝ)*x)/(aleph U b n x)*d+(n : ℝ)*x

def majorantL (U b : ℚ) (n : ℕ) (j : ℤ) (x d : ℝ) : ℝ :=
  chord (nextObjective U b n x) (A U b n j) (A U b n (j+1)) d

/-- Atomic masses on real endpoints, to preserve the literal endpoint scope of Lemma 10. -/
def realTwoPoint (L R m : ℝ) (d : ℝ) : ℝ :=
  (if d = L then (R-m)/(R-L) else 0) + (if d = R then (m-L)/(R-L) else 0)

/-- Embed a rationally supported law in real atomic masses. -/
def realAtoms (q : DemandLaw) (d : ℝ) : ℝ :=
  ∑' r : ℚ, if (r : ℝ) = d then q r else 0

end XinMartingaleInventory.Minimax


