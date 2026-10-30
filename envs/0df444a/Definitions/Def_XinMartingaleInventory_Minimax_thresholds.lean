-- Prove2me | Definitions.Def_XinMartingaleInventory_Minimax_thresholds
-- name    : XinMartingaleInventory_Minimax_thresholds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:57:25.807987+00:00
-- url     : https://prove2.me/theorems/dd7c44fe-29c9-45e2-b4ff-2d9085b8b0d2
-- title:
--   Explicit thresholds, objective and two-point demand law
-- statement:
--   For n≥1 and integer −1≤j≤n, A_j^n is U times the product of k/(b+k) from k=j+1 to n−1, except A_n^n=(b+n)U/n; B_j^n=j A_j^n/(b+n). Empty products are one. Γ_m^n selects j+1 when A_j^(n+1)<m≤A_(j+1)^(n+1), and is zero at m=0. Υ_x^n selects j∈{0,…,n} with B_j^(n+1)≤x<B_(j+1)^(n+1), including the final interval [B_n^(n+1),U), with Υ_U^n=n. Both zero-horizon index selectors are zero. β_m^n=B_(Γ_m^n)^n. G_j^n=(n−(b+n)m/A_j^n)x+(n−j)bm, F_j^n=−bx+(b+n)B_(j+1)^n+(nb−(b+1)(j+1))m. The explicit objective uses the piecewise formula on p.20. The proposed law has the two adjacent A atoms when x<B_(j+1)^n, otherwise atoms 0 and A_k^n; m=0 or x=U uses atoms 0 and U. Atom weights interpolate to mean m, and coincident atoms have their contributions added. The explicit value is G_(Γ_m^n)^n(β_m^n,m).
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, §§2.1–3 and §7.2, p.12 (PDF p.12)

import Definitions.Def_XinMartingaleInventory_Minimax_inventoryModel

noncomputable section

namespace XinMartingaleInventory.Minimax

/-- Integer indexing preserves the genuine index -1. -/
def A (U b : ℚ) (n : ℕ) (j : ℤ) : ℚ :=
  if j = (n : ℤ) then (b+n) / n * U
  else U * ∏ k ∈ Finset.Icc (j+1) ((n : ℤ)-1), (k : ℚ) / (b+k)

def B (U b : ℚ) (n : ℕ) (j : ℤ) : ℚ := (j : ℚ) / (b+n) * A U b n j

/-- The unique right-closed A interval; the sum is an explicit finite selector. -/
def gamma (U b : ℚ) (n : ℕ) (m : ℝ) : ℤ :=
  if n = 0 ∨ m = 0 then 0 else
  ∑ k ∈ Finset.range (n+1),
    if (A U b (n+1) ((k : ℤ)-1) : ℝ) < m ∧ m ≤ (A U b (n+1) k : ℝ)
    then (k : ℤ) else 0

def upsilon (U b : ℚ) (n : ℕ) (x : ℝ) : ℤ :=
  if n = 0 then 0 else if x = (U : ℝ) then (n : ℤ) else
  ∑ k ∈ Finset.range (n+1),
    if (B U b (n+1) k : ℝ) ≤ x ∧ x < (B U b (n+1) (k+1) : ℝ)
    then (k : ℤ) else 0

def beta (U b : ℚ) (n : ℕ) (m : ℝ) : ℚ := B U b n (gamma U b n m)

def G (U b : ℚ) (n : ℕ) (j : ℤ) (x m : ℝ) : ℝ :=
  ((n : ℝ) - ((b : ℝ)+n) / (A U b n j : ℝ) * m) * x +
    ((n : ℝ)-j) * (b : ℝ) * m

def F (U b : ℚ) (n : ℕ) (j : ℤ) (x m : ℝ) : ℝ :=
  -(b : ℝ)*x + ((b : ℝ)+n)*(B U b n (j+1) : ℝ) +
    ((n : ℝ)*b-((b : ℝ)+1)*((j : ℝ)+1))*m

/-- The explicit objective, using the equivalent formula printed on p.20. -/
def explicitG (U b : ℚ) (n : ℕ) (x m : ℝ) : ℝ :=
  if x = (U : ℝ) then G U b n n x m else
  if x < (B U b n (gamma U b (n-1) m) : ℝ)
  then F U b n (gamma U b (n-1) m - 1) x m
  else G U b n (upsilon U b (n-1) x) x m

def explicitValue (U b : ℚ) (n : ℕ) (m : ℚ) : ℝ :=
  G U b n (gamma U b n m) (beta U b n m) m

/-- Two-atom mass; when endpoints coincide their contributions add. -/
def twoPoint (L R : ℚ) (p : ℝ) : DemandLaw :=
  fun d => (if d = L then 1-p else 0) + (if d = R then p else 0)

def endpointLaw (U m : ℚ) : DemandLaw := twoPoint 0 U ((m : ℝ)/U)

/-- Equation (2.7), including m=0 and x=U before the interval branches. -/
def explicitLaw (U b : ℚ) (n : ℕ) (x m : ℚ) : DemandLaw :=
  if m = 0 ∨ x = U then endpointLaw U m else
  let j := gamma U b (n-1) m - 1
  if x < B U b n (j+1) then
    twoPoint (A U b n j) (A U b n (j+1))
      (((m : ℝ)-(A U b n j : ℝ)) / ((A U b n (j+1) : ℝ)-(A U b n j : ℝ)))
  else twoPoint 0 (A U b n (upsilon U b (n-1) x))
    ((m : ℝ)/(A U b n (upsilon U b (n-1) x) : ℝ))

end XinMartingaleInventory.Minimax


