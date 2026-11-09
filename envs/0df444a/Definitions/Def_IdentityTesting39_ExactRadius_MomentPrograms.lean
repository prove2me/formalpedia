-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms
-- name    : IdentityTesting39_ExactRadius_MomentPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:55.563749+00:00
-- url     : https://prove2.me/theorems/38faef6a-18b8-45e5-991b-beef434b85f3
-- title:
--   The three moment programs and their real sample root
-- statement:
--   Let $q$ be a probability vector and let $n>0$ be real. Each coordinate of a moment family records $(r_i,w_i,e_i,d_i)$. The all-coordinate branch uses every coordinate, requires $\sum_i r_i=1$ and $\sum_i d_i\ge\varepsilon$, and minimizes
--
--   $$\max\left\{n\sum_i\frac{(r_i-q_i)^2}{r_i+q_i},\ n^2\sum_i\frac{w_i^2}{q_i^2+w_i}\right\}.$$
--
--   A head-deleted branch retains scalar laws only off a designated head, normalizes the full mean, and uses only tail coordinates in the second cost. The excess branch requires tail excess at least $\varepsilon$; the deficit branch requires tail deficit at least $\varepsilon$. Unused head slots are zero, so the head has only a mean. The allowed regimes are the diffuse reference and a largest head of mass in $[1/8,1)$.
--
--   Write $F_n=A_n$ in the diffuse case and $F_n=J_n^+$ otherwise. The root is
--
--   $$R(q,\varepsilon,i_0)=\inf\{n\ge1/\varepsilon:F_n\ge1\},$$
--
--   with $R=1/\varepsilon$ for a point mass. The infima are real and their attainment is a theorem, not part of the definition. No statistical sample-complexity quantity occurs in these formulas. Deterministic tuples are computed directly from a probability vector.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.3, §2.1–2.2 and display (1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_StatisticalModel
import Definitions.Def_IdentityTesting39_ExactRadius_ScalarMoments

open scoped BigOperators

noncomputable section

namespace IdentityTesting39.ExactRadius

inductive Branch (ι : Type) where
  | all
  | excess (head : ι)
  | deficit (head : ι)
  deriving DecidableEq

/-- A coordinate has r,w,e,d in slots 0,1,2,3. Unused head slots are fixed to zero. -/
abbrev MomentFamily (ι : Type) := ι → Fin 4 → ℝ

noncomputable def quadraticCoords {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Branch ι) : Finset ι :=
  match B with
  | .all => Finset.univ
  | .excess i₀ | .deficit i₀ => Finset.univ.erase i₀

/-- §2.1/2.2: the three closed feasible moment sets; the head has only a mean. -/
def feasibleMoments {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε : ℝ) (B : Branch ι) : Set (MomentFamily ι) :=
  {x | (∀ i ∈ quadraticCoords B, ScalarMoments (q i) (x i 0) (x i 1) (x i 2) (x i 3)) ∧
    (∀ i, 0 ≤ x i 0) ∧ (∑ i, x i 0) = 1 ∧
    (∀ i, i ∉ quadraticCoords B → x i 1 = 0 ∧ x i 2 = 0 ∧ x i 3 = 0) ∧
    (match B with
    | .excess _ => ε ≤ ∑ i ∈ quadraticCoords B, x i 2
    | _ => ε ≤ ∑ i ∈ quadraticCoords B, x i 3)}

def triangularCost (q r : ℝ) : ℝ := (r-q)^2/(r+q)
def collisionCost (q w : ℝ) : ℝ := w^2/(q^2+w)

noncomputable def meanCost {ι : Type} [Fintype ι]
    (q : ι → ℝ) (x : MomentFamily ι) : ℝ := ∑ i, triangularCost (q i) (x i 0)
noncomputable def quadraticCost {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (B : Branch ι) (x : MomentFamily ι) : ℝ :=
  ∑ i ∈ quadraticCoords B, collisionCost (q i) (x i 1)
noncomputable def objective {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (B : Branch ι) (n : ℝ) (x : MomentFamily ι) : ℝ :=
  max (n * meanCost q x) (n^2 * quadraticCost q B x)

/-- Minima are represented by infima; attainment is asserted in the theorems. -/
noncomputable def programValue {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n : ℝ) (B : Branch ι) : ℝ :=
  sInf (objective q B n '' feasibleMoments q ε B)

noncomputable def functional {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n : ℝ) (i₀ : ι) : ℝ :=
  if q i₀ < 1/8 then programValue q ε n .all else programValue q ε n (.excess i₀)

noncomputable def rootSet {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε : ℝ) (i₀ : ι) : Set ℝ :=
  {n | 1/ε ≤ n ∧ 1 ≤ functional q ε n i₀}

/-- (1): an infimum over real n, with an independent point-mass definition. -/
noncomputable def sampleRoot {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε : ℝ) (i₀ : ι) : ℝ :=
  if q i₀ = 1 then 1/ε else sInf (rootSet q ε i₀)

/-- The branches for the theorem's SOC clause, including the feasible deficit endpoint. -/
def Applicable {ι : Type} (q : ι → ℝ) (ε : ℝ) (i₀ : ι) (B : Branch ι) : Prop :=
  match B with
  | .all => q i₀ < 1/8
  | .excess h => h = i₀ ∧ 1/8 ≤ q i₀ ∧ q i₀ < 1
  | .deficit h => h = i₀ ∧ 1/8 ≤ q i₀ ∧ q i₀ < 1 ∧ ε ≤ 1-q i₀

/-- The domains in §2.1 and §2.2 on which the named programs are used. -/
def InRegime {ι : Type} (q : ι → ℝ) (B : Branch ι) : Prop :=
  match B with
  | .all => ∀ i, q i < 1/8
  | .excess h | .deficit h => Largest q h ∧ 1/8 ≤ q h ∧ q h < 1

/-- Deterministic coordinates, with the unused head moments zeroed out. -/
noncomputable def deterministicTuple {ι : Type} [Fintype ι] [DecidableEq ι]
    (q p : ι → ℝ) (B : Branch ι) : MomentFamily ι := by
  classical
  exact fun i => ![p i, if i ∈ quadraticCoords B then (p i-q i)^2 else 0,
    if i ∈ quadraticCoords B then max (p i-q i) 0 else 0,
    if i ∈ quadraticCoords B then max (q i-p i) 0 else 0]

end IdentityTesting39.ExactRadius


