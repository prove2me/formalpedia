-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Elimination
-- name    : LocalProbeMIS871_Greedy_Elimination
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T01:52:03.938349+00:00
-- url     : https://prove2.me/theorems/66a7e4da-f264-4582-b52d-54659b61b556
-- title:
--   §3.1 — Greedy acceptance, strict residual queries and elimination moments
-- statement:
--   For a finite simple labeled graph $G$ and real ranks $r$, let $I_G(r)$ be the greedy independent set computed by recursion on the same lexicographic keys as the query algorithm. The elimination time is the real rank of the earliest accepted vertex in the closed neighborhood:
--
--   $$\tau(u)=\min\{r(z):z\in I_G(r)\cap(N_G(u)\cup\{u\})\}.$$
--
--   The reused definition takes the minimum key in a structurally proved nonempty set, then projects to its real coordinate. Set $H_a=G[\{u:\tau(u)>a\}]$ and $P_a=R_G(v,r)\cap V(H_a)$. A residual query runs the same recursion on the induced subtype and has empty evaluated set when $v$ is absent. For a real exponent $s$, define
--
--   $$M_s=\sum_{u\in R_G(v,r)}\tau(u)^s,\qquad X=\sum_{u\in R_G(v,r)\setminus\{v\}}\tau(u)^s,$$
--   $$D=\sum_{u\in R_G(v,r)\setminus\{v\}}\tau(u)^s\ln\frac{r(u)}{\tau(u)},\qquad c_s=\ln(s-1)-1.$$
--
--   These computed quantities supply the moments and weighted residual sets used throughout the upper bound. The root contributes its actual elimination time, which can be below $1$ even when its rank is $1$.
--
--   **Formalization Note** Powers are real powers. Real logarithms and quotients are totalized off the good-rank domain; their arguments are positive on that probability-one domain. The strict residual boundary is separate from the referenced definition's closed `ActiveAt` predicate.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 12, PDF p. 14, §3.1, Eq.(6), definition of M_s; §3.3.2, Eq.(18) (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Model
import Definitions.Def_RGMISFast_tau

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Greedy acceptance computed by lower-key recursion, on exactly the execution's keys. -/
def I {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => RGMISFast.inMIS G (key r) u = true)

/-- Minimum accepted key in the closed neighborhood, projected to real time (§3.1). -/
def tau {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) : ℝ :=
  (ofLex (RGMISFast.tau G (key r) u)).1

/-- Strict residual vertex set, after all eliminations through a. -/
def H {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (a : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => a < tau G r u)

def P {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) (a : ℝ) : Finset (Fin n) :=
  R G v r ∩ H G r a

/-- Run on the induced residual subtype, mapped back to original labels; absent root gives ∅. -/
def residualR {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ)
    (a : ℝ) : Finset (Fin n) :=
  if hv : v ∈ H G r a then
    let G' := G.induce (↑(H G r a) : Set (Fin n))
    let result := RGMISFast.run G' (fun u => key r u.val) ⟨v, hv⟩
    (((result.2.trace.filter (fun e => e.fresh)).map (fun e => e.callee.val))).toFinset
  else ∅

def M {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ u ∈ R G v r, (tau G r u) ^ s

def X {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ u ∈ (R G v r).erase v, (tau G r u) ^ s

def D {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ u ∈ (R G v r).erase v, (tau G r u) ^ s * Real.log (r u / tau G r u)

def c (s : ℝ) : ℝ := Real.log (s - 1) - 1

end LocalProbeMIS871.Greedy


