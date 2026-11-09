-- Prove2me | Definitions.Def_FourBlockIP350_Main_Penalty
-- name    : FourBlockIP350_Main_Penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:26.66023+00:00
-- url     : https://prove2.me/theorems/21b746ce-8d16-4a9b-9cc2-cf2e242e9e17
-- title:
--   Exact penalized value and residue classes
-- statement:
--   For a nonempty finite product box, put
--   $$W=\sum_j|c_j|(u_j-\ell_j),\quad K=W+1,\quad s=b-Zx-Ey,$$
--   $$F(x)=\min_{\ell^{(1:n)}\le y\le u^{(1:n)}}\{c^\top(x,y)+K\|s\|_1\}.$$
--   This definition is used at every integer $x$, including outside the global box. Attains includes local-box membership and equality of the candidate cost to $F(x)$. Residual slacks are uniquely determined and are eliminated from the minimum. Real projections of $F$ are used only in statements whose standing finite-box assumptions guarantee finiteness, which Lemma 3.1 establishes.
--
--   Set $H_r(v)=F(r+Nv)$ and $M=kN$, $F_q(v)=F(q+Mv)$. The residue box has endpoints
--   $$\alpha_q=\lceil(\ell^{(0)}-q)/M\rceil,\qquad\beta_q=\lfloor(u^{(0)}-q)/M\rfloor.$$
--   Integer Euclidean division computes these roundings for positive $M$. An empty residue box means no global point in that residue class, even though the residual-penalty problem is always defined.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 6–8, 13, Eqs. (3.1), (3.2), (4.1), (5.1), Corollary 4.3

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BlockData
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

def variation {k n : ℕ} (I : FourBlock k n) : ℤ :=
  ∑ j, |I.c j| * (hi I j - lo I j)

def penaltyCoefficient {k n : ℕ} (I : FourBlock k n) : ℤ := variation I + 1

def residual {k n : ℕ} (I : FourBlock k n) (x : ZVec k) (y : LocalCol k n → ℤ) : BlockRow k n → ℤ :=
  I.b - I.Z.mulVec x - I.localPart.matrix.mulVec y

def penalized {k n : ℕ} (I : FourBlock k n) (x : ZVec k) (y : LocalCol k n → ℤ) : ℤ :=
  Objective I.program (joinPoint x y) + penaltyCoefficient I * ∑ r, |residual I x y r|

/-- Equation (3.2); residual slacks are eliminated by their unique equality.
An empty local box gives +infinity, so no default real infimum is used. -/
noncomputable def F {k n : ℕ} (I : FourBlock k n) (x : ZVec k) : EReal :=
  sInf {v | ∃ y, LocalBox I y ∧ v = ((penalized I x y : ℝ) : EReal)}

noncomputable def realF {k n : ℕ} (I : FourBlock k n) (x : ZVec k) : ℝ := (F I x).toReal

def Attains {k n : ℕ} (I : FourBlock k n) (x : ZVec k) (y : LocalCol k n → ℤ) : Prop :=
  LocalBox I y ∧ F I x = ((penalized I x y : ℝ) : EReal)

noncomputable def H {k n : ℕ} (I : FourBlock k n) (N : ℕ) (r : ZVec k) (v : ZVec k) : ℝ :=
  realF I (r + (N : ℤ) • v)

def period (k N : ℕ) : ℕ := k * N

noncomputable def Fq {k n : ℕ} (I : FourBlock k n) (N : ℕ) (q v : ZVec k) : ℝ :=
  realF I (q + (period k N : ℤ) • v)

def IsResidue {k : ℕ} (M : ℕ) (q : ZVec k) : Prop := ∀ j, 0 ≤ q j ∧ q j < (M : ℤ)

def alpha {k n : ℕ} (I : FourBlock k n) (N : ℕ) (q : ZVec k) : ZVec k :=
  fun j => - ((-(lo I (none,j) - q j)) / (period k N : ℤ))

def beta {k n : ℕ} (I : FourBlock k n) (N : ℕ) (q : ZVec k) : ZVec k :=
  fun j => (hi I (none,j) - q j) / (period k N : ℤ)

def ResidueBox {k n : ℕ} (I : FourBlock k n) (N : ℕ) (q v : ZVec k) : Prop :=
  ∀ j, alpha I N q j ≤ v j ∧ v j ≤ beta I N q j

end FourBlockIP350.Main


