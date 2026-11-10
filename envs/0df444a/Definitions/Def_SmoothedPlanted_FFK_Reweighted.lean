-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Reweighted
-- name    : SmoothedPlanted_FFK_Reweighted
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:40.325423+00:00
-- url     : https://prove2.me/theorems/a165bb84-c302-4d93-8ef3-2822e3eff525
-- title:
--   Definition 47 — reweighted matrices Q, P and B
-- statement:
--   The matrix $A$ is the adjacency matrix of $H'$. On distinct-variable entries with $\rho_{ij}[a,b]>0$, set $Q_{ia,jb}=\Pi[a,b](A_{ia,jb}/\rho_{ij}[a,b]-1)$ and $P_{ia,jb}=A_{ia,jb}(1-\Pi[a,b]/\rho_{ij}[a,b])$. Both matrices vanish when the probability is zero and on same-variable blocks. Put $B_{ia,jb}=\Pi[a,b]$ for $i\ne j$ and zero otherwise, equivalently $(J_m-I_m)\otimes\Pi$. Probabilities in either orientation refer to the same unordered pair distribution.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Definition 47 — reweighted matrices Q, P and B, printed p. 31 (PDF p. 33), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_OutsideLaw
import Definitions.Def_SmoothedPlanted_FFK_Dual
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def rhoMatrix {V : Type} [LinearOrder V] {q : ℕ}
    (D : Pair V → PMF (Relation q)) : Matrix (V × Fin q) (V × Fin q) ℝ :=
  fun x y => if h : x.1 < y.1 then rho (D ⟨(x.1,y.1),h⟩) x.2 y.2
    else if h : y.1 < x.1 then rho (D ⟨(y.1,x.1),h⟩) y.2 x.2 else 0
def biasedMatrix {V : Type} [DecidableEq V] {q : ℕ}
    (Pi : Matrix (Fin q) (Fin q) ℝ) : Matrix (V × Fin q) (V × Fin q) ℝ :=
  fun x y => if x.1 = y.1 then 0 else Pi x.2 y.2
def reweightedQ {V : Type} [LinearOrder V] {q : ℕ}
    (D : Pair V → PMF (Relation q)) (Pi : Matrix (Fin q) (Fin q) ℝ)
    (Y : CSP V q) : Matrix (V × Fin q) (V × Fin q) ℝ := by
  classical
  exact fun x y => if x.1 ≠ y.1 ∧ 0 < rhoMatrix D x y then
    Pi x.2 y.2 * (adjacency (incompatibilityPrime Y) x y / rhoMatrix D x y - 1) else 0
def reweightedP {V : Type} [LinearOrder V] {q : ℕ}
    (D : Pair V → PMF (Relation q)) (Pi : Matrix (Fin q) (Fin q) ℝ)
    (Y : CSP V q) : Matrix (V × Fin q) (V × Fin q) ℝ := by
  classical
  exact fun x y => if x.1 ≠ y.1 ∧ 0 < rhoMatrix D x y then
    adjacency (incompatibilityPrime Y) x y * (1 - Pi x.2 y.2 / rhoMatrix D x y) else 0

end SmoothedPlanted.FFK


