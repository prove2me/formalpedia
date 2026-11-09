-- Prove2me | Definitions.Def_HarmonicKServer_Competitive_Electrical
-- name    : HarmonicKServer_Competitive_Electrical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:31.748452+00:00
-- url     : https://prove2.me/theorems/ebb25fee-284c-4767-820f-6edd68776772
-- title:
--   §4 — Electrical energy and the corrected assignment potential
-- statement:
--   Let $k$ be the number of labelled servers in a metric space $(V,d)$. A signed flow is a real matrix $F$ with zero diagonal, $F_{ij}=-F_{ji}$, and divergence $\sum_jF_{ij}=a_i$. For a real zero-sum vector $a$, the electrical energy and the corrected occupancy potential are
--   $$
--   E_Y(a)=\inf_{F\text{ feasible for }a}\sum_{i<j}d(y_i,y_j)F_{ij}^2,\qquad
--   c_i=E_Y(e_i-\mathbf1/k),\qquad
--   U_Y(q)=\frac{k^2}{2}\left(E_Y(q-\mathbf1)+\sum_iq_ic_i\right).
--   $$
--   An assignment $f:[k]\to[k]$ is any function, with counts $q_{f,i}=|f^{-1}(i)|$. Define
--   $$\Phi(X,Y)=\min_f\left(U_Y(q_f)+k^3\sum_\ell d(x_\ell,y_{f(\ell)})\right).$$
--   The common excess for serving label $s$ is $q+e_s-(1+1/k)\mathbf1$. This layer supplies the exact objects shared by the electrical and competitive statements.
--
--   **Formalization Note** Flows and supplies are real, while occupancies are natural counts summing to $k$. The energy uses a real infimum; attainment is a separate theorem. On a nonzero-total excess the feasible set is empty and Lean's real infimum is zero; such vectors are outside every energy theorem's domain. Feasible energies are nonnegative, and every zero-sum vector admits a finite-energy flow. The assignment range is finite and nonempty (the identity assignment exists), so its infimum is a minimum. Distinct adversary locations and $k\ge2$ belong to the analysis theorems, not to these data definitions or to the goal. The factor $k^2/2$ multiplies the entire parenthesis.
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 5, §4 definitions, continuing on p. 6 (PDF pp. 6–7) (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Mathlib
import Definitions.Def_KServer_model

namespace HarmonicKServer.Competitive
open scoped BigOperators

abbrev Vector (k : ℕ) := Fin k → ℝ
abbrev Flow (k : ℕ) := Fin k → Fin k → ℝ

def ZeroSum {k : ℕ} (a : Vector k) : Prop := ∑ i, a i = 0

def Feasible {k : ℕ} (a : Vector k) (F : Flow k) : Prop :=
  (∀ i, F i i = 0) ∧ (∀ i j, F i j = -F j i) ∧ (∀ i, ∑ j, F i j = a i)

noncomputable def flowEnergy {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (F : Flow k) : ℝ :=
  ∑ i, ∑ j, if i < j then dist (Y i) (Y j) * (F i j)^2 else 0

noncomputable def energy {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (a : Vector k) : ℝ :=
  sInf {c : ℝ | ∃ F : Flow k, Feasible a F ∧ flowEnergy Y F = c}

def Minimizing {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (a : Vector k) (F : Flow k) : Prop :=
  Feasible a F ∧ flowEnergy Y F = energy Y a

def Ohm {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (F : Flow k) (h : Vector k) : Prop :=
  ∀ i j, i ≠ j → dist (Y i) (Y j) * F i j = h i - h j

def unit {k : ℕ} (i : Fin k) : Vector k := fun j => if j = i then 1 else 0

noncomputable def supply {k : ℕ} (a : Vector k) : ℝ := ∑ i, max (a i) 0

/-- Natural counts are the nonnegative integer occupancies of the source. -/
def Occupancy {k : ℕ} (q : Fin k → ℕ) : Prop := ∑ i, q i = k

def transfer {k : ℕ} (q : Fin k → ℕ) (i s : Fin k) : Fin k → ℕ :=
  fun j => q j - (if j = i then 1 else 0) + (if j = s then 1 else 0)

noncomputable def commonExcess {k : ℕ} (q : Fin k → ℕ) (s : Fin k) : Vector k :=
  fun j => (q j : ℝ) + unit s j - (1 + 1 / (k : ℝ))

noncomputable def spreadingEnergy {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (i : Fin k) : ℝ :=
  energy Y (fun j => unit i j - 1 / (k : ℝ))

noncomputable def corrected {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (q : Fin k → ℕ) : ℝ :=
  (k : ℝ)^2 / 2 * (energy Y (fun j => (q j : ℝ) - 1) +
    ∑ i, (q i : ℝ) * spreadingEnergy Y i)

noncomputable def counts {k : ℕ} (f : Fin k → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun j => f j = i)).card

noncomputable def assignmentValue {k : ℕ} {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (f : Fin k → Fin k) : ℝ :=
  corrected Y (counts f) + (k : ℝ)^3 * ∑ j, dist (X j) (Y (f j))

noncomputable def potential {k : ℕ} {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) : ℝ :=
  sInf (Set.range (assignmentValue X Y))

end HarmonicKServer.Competitive


