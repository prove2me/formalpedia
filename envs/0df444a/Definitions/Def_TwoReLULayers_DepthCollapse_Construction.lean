-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Construction
-- name    : TwoReLULayers_DepthCollapse_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:34:21.740447+00:00
-- url     : https://prove2.me/theorems/3483423b-1931-4c93-acf9-cf28fa47e859
-- title:
--   The simplex sign regions and explicit thermostat paramids
-- statement:
--   Let $n\ge2$, $[n]=\{1,\ldots,n\}$, $e_i$ the standard basis vectors, and $\Delta_S=\operatorname{conv}\{e_i:i\in S\}$. Put $\Delta=\Delta_{[n]}$, $H_0=\{y:\sum_i y_i=0\}$, and $\widetilde\Delta=\{y\in H_0:y_i\ge-1\}$. For a nonempty proper subset $A$ of $[n]$, let
--   $$P_A=\{y\in\widetilde\Delta:y_i\ge0\ (i\in A),\ y_j\le0\ (j\notin A)\}.$$
--   For $v\in[n]$, an ordering $\pi$ of $[n]\setminus\{v\}$ is a bijection. A marked set $M$ consists of positions $2,\ldots,n-1$. With $u_i=\sum_{j<i}y_{\pi_j}$, define
--   $$K_{v,\pi,M}=\{y\in H_0:-1\le y_v\le0,\ 0\le u_i\le-y_v\ (i\in M),\ y_v\le y_{\pi_i}\le0\ (i\notin M,\ 2\le i\le n-1)\}.$$
--   There is no condition on position one besides the hyperplane equation. The module packages the signed indicator sums and signed support sums, with coefficient $(-1)^{s-1}s!(n-1-s)!$, and the generic locus excluding zero coordinates, coinciding coordinates, $y_v=-1$ and the partial-sum boundary hyperplanes.
--
--   These are explicit geometric sets, independent of the network class, used throughout the eight numbered milestones.
--
--   **Formalization Note** Source label and position $i+1$ use `Fin` value $i`; marked positions are precisely those with positive value. Nonzero factorial branches have $1\le s\le n-1$. At $n=2$ the marked-position range is empty.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 21, Sections 6.1 and 7.1, Eq. (4), pp. 21–22

import Definitions.Def_TwoReLULayers_DepthCollapse_Geometry

namespace TwoReLULayers.DepthCollapse

noncomputable section

/-- Zero-based Fin labels correspond to source labels 1,...,n by i ↦ i+1. -/
def basisVector {n : ℕ} (i : Fin n) : E n := WithLp.toLp 2 (Pi.single i 1)

def simplexFace {n : ℕ} (S : Finset (Fin n)) : Set (E n) :=
  convexHull ℝ (basisVector '' (S : Set (Fin n)))

def simplex (n : ℕ) : Set (E n) := simplexFace (Finset.univ : Finset (Fin n))

def zeroHyperplane (n : ℕ) : AffineSubspace ℝ (E n) where
  carrier := {y | ∑ i, y i = 0}
  smul_vsub_vadd_mem' := by
    intro c p₁ p₂ p₃ h₁ h₂ h₃
    simp only [Set.mem_ofPred_eq] at *
    change (∑ i, (c * (p₁ i - p₂ i) + p₃ i)) = 0
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, h₁, h₂, h₃]
    ring

def dilatedSimplex (n : ℕ) : Set (E n) :=
  {y | y ∈ zeroHyperplane n ∧ ∀ i, -1 ≤ y i}

def signRegion {n : ℕ} (A : Finset (Fin n)) : Set (E n) :=
  {y | y ∈ dilatedSimplex n ∧ (∀ i ∈ A, 0 ≤ y i) ∧ ∀ i, i ∉ A → y i ≤ 0}

def properSigns (n : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.powerset.filter (fun A => A.Nonempty ∧ A ≠ Finset.univ)

/-- Bijective orderings, not arbitrary sequences with repetitions. -/
abbrev Order {n : ℕ} (v : Fin n) := Fin (n - 1) ≃ {i : Fin n // i ≠ v}

def markedPositions (n : ℕ) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun i => 0 < i.val)

def partialSum {n : ℕ} {v : Fin n} (π : Order v) (i : Fin (n - 1)) (y : E n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => j.val < i.val), y (π j).val

/-- Position zero (source position one) has no marked or unmarked inequality. -/
def paramidK {n : ℕ} (v : Fin n) (π : Order v) (M : Finset (Fin (n - 1))) : Set (E n) :=
  {y | y ∈ zeroHyperplane n ∧ -1 ≤ y v ∧ y v ≤ 0 ∧
    ∀ i ∈ markedPositions n,
      if i ∈ M then 0 ≤ partialSum π i y ∧ partialSum π i y ≤ -y v
      else y v ≤ y (π i).val ∧ y (π i).val ≤ 0}

def positiveCount {n : ℕ} (y : E n) : ℕ := (Finset.univ.filter (fun i => 0 < y i)).card

/-- The coefficient is used only for 1 ≤ s ≤ n-1 on the generic nonzero branch. -/
def countCoefficient (n s : ℕ) : ℝ :=
  (-1 : ℝ) ^ (s - 1) * (Nat.factorial s : ℝ) * (Nat.factorial (n - 1 - s) : ℝ)

def thermostatValue {n : ℕ} (v : Fin n) (y : E n) : ℝ := by
  classical
  exact if (-1 < y v ∧ ∀ i, y v ≤ y i) then countCoefficient n (positiveCount y) else 0

def signedKIndicators {n : ℕ} (v : Fin n) (y : E n) : ℝ :=
  ∑ π : Order v, ∑ M ∈ (markedPositions n).powerset,
    (-1 : ℝ) ^ M.card * indicator (paramidK v π M) y

def signedKSupports (n : ℕ) : E n → ℝ := fun x =>
  ∑ v : Fin n, ∑ π : Order v, ∑ M ∈ (markedPositions n).powerset,
    (-1 : ℝ) ^ M.card * support (paramidK v π M) x

def signedRegionIndicators {n : ℕ} (y : E n) : ℝ :=
  ∑ A ∈ properSigns n, countCoefficient n A.card * indicator (signRegion A) y

def signedRegionSupports (n : ℕ) : E n → ℝ := fun x =>
  ∑ A ∈ properSigns n, countCoefficient n A.card * support (signRegion A) x

/-- Explicit generic locus from the proof of Lemma 20. -/
def Generic {n : ℕ} (v : Fin n) (y : E n) : Prop :=
  (∀ i, y i ≠ 0) ∧ (∀ i j, i ≠ j → y i ≠ y j) ∧ y v ≠ -1 ∧
    ∀ π : Order v, ∀ i ∈ markedPositions n,
      partialSum π i y ≠ 0 ∧ partialSum π i y ≠ -y v

end
end TwoReLULayers.DepthCollapse


