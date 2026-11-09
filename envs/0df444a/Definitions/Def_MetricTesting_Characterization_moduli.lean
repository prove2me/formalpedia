-- Prove2me | Definitions.Def_MetricTesting_Characterization_moduli
-- name    : MetricTesting_Characterization_moduli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:37.0226+00:00
-- url     : https://prove2.me/theorems/0c547f4a-6634-41d5-bc00-2aeba57147c1
-- title:
--   Removal, packing amplification and completion stability moduli
-- statement:
--   In the local matrix framework, write $d(D,\mathcal P_n)$ for normalized repair distance, $\operatorname{viol}(D)$ for violation density and $\nu(D)$ for the maximum edge-disjoint violation packing. Define the order-uniform moduli
--   $$\rho(\epsilon)=\inf_{n\ge k,\ d(D,\mathcal P_n)>\epsilon}\operatorname{viol}(D),\qquad
--   \Delta(\alpha)=\inf_{n\ge k,\ \nu(D)\ge\alpha n^2}\operatorname{viol}(D).$$
--   Empty infima are $+\infty$. Removability means $\rho(\epsilon)>0$ for every $\epsilon>0$, and packing amplification means $\Delta(\alpha)>0$ for every $\alpha>0$.
--
--   A partial array $A$ specifies only some edges. Its holes are $H(A)$. Local consistency requires $\Phi$ only on fully specified $k$-subsets. A completion fills holes while preserving specified values and need not be valid. Its completion repair distance instead allows changes to specified entries, minimizing over valid target arrays:
--   $$\operatorname{cdist}(A)=\frac2{n^2}\min_{B\in\mathcal P_n}|\{e\notin H(A):B_e\ne A_e\}|,\qquad
--   \Gamma(\theta)=\sup_{n\ge k,\ A\text{ locally consistent},\ |H(A)|\le\theta n^2}\operatorname{cdist}(A).$$
--   Completion stability means $\Gamma(\theta)\to0$ as $\theta\downarrow0$, equivalently for every $\eta>0$ some $\theta>0$ satisfies $\Gamma(\theta)\le\eta$. The real supremum is bounded by 1 and is nonempty for nonnegative $\theta$ under the standing nonempty-target assumption. This supplies independent deterministic notions for the characterization.
--
--   The forward query bound is $\binom k2\lceil\log(3)/\rho(\epsilon)\rceil$ when $\rho(\epsilon)$ is finite and zero when it is $+\infty$. The infinite branch is handled before conversion to real numbers. Natural minima have a zero fallback only outside the nonempty-target domain, which is excluded in every theorem using them.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), pp. 10–11, Definitions 3.3, 3.5, 3.6 and Theorem 3.4 (PDF pp. 11–12)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_arrays

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Empty infima are +infinity, as required when no far inputs exist. -/
def removalModulus (F : LocalData) (ε : ℝ) : ENNReal :=
  ⨅ (n : ℕ) (_ : F.k ≤ n) (D : Array F.values n)
    (_ : ε < repairDistance F D), ENNReal.ofReal (violationDensity F D)

def Removable (F : LocalData) : Prop :=
  ∀ ε : ℝ, 0 < ε → 0 < removalModulus F ε

def packingModulus (F : LocalData) (α : ℝ) : ENNReal :=
  ⨅ (n : ℕ) (_ : F.k ≤ n) (D : Array F.values n)
    (_ : α * (n : ℝ)^2 ≤ (packingNumber F D : ℝ)),
      ENNReal.ofReal (violationDensity F D)

def PackingAmplification (F : LocalData) : Prop :=
  ∀ α : ℝ, 0 < α → 0 < packingModulus F α

abbrev PartialArray (Λ : Set NNReal) (n : ℕ) := Edge n → Option Λ

def Holes {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n) : Finset (Edge n) :=
  Finset.univ.filter fun e => A e = none

/-- A completion only fills holes, without asserting validity. -/
def Completes {Λ : Set NNReal} {n : ℕ} (A : PartialArray Λ n)
    (D : Array Λ n) : Prop := ∀ e v, A e = some v → D e = v

def LocallyConsistent (F : LocalData) {n : ℕ}
    (A : PartialArray F.values n) : Prop :=
  ∀ f : Fin F.k ↪ Fin n, ∀ B : Array F.values F.k,
    (∀ e, A (edgeMap f e) = some (B e)) → B ∈ F.predicate

/-- Only changes to specified entries are counted. -/
def specifiedDiscrepancy {Λ : Set NNReal} {n : ℕ}
    (A : PartialArray Λ n) (B : Array Λ n) : ℕ :=
  (Finset.univ.filter fun e => ∃ v, A e = some v ∧ B e ≠ v).card

def minimumCompletionEdits (F : LocalData) {n : ℕ}
    (A : PartialArray F.values n) : ℕ :=
  if h : ∃ m : ℕ, ∃ B : Array F.values n,
      Valid F B ∧ specifiedDiscrepancy A B = m
  then Nat.find h else 0

def completionDistance (F : LocalData) {n : ℕ}
    (A : PartialArray F.values n) : ℝ :=
  2 * minimumCompletionEdits F A / (n : ℝ)^2

/-- This real supremum is bounded by 1 and nonempty for theta ≥ 0 under
TargetsNonempty: a valid total matrix supplies a zero-hole member. -/
def completionModulus (F : LocalData) (θ : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, F.k ≤ n ∧ ∃ A : PartialArray F.values n,
    LocallyConsistent F A ∧ (Holes A).card ≤ θ * (n : ℝ)^2 ∧
      x = completionDistance F A}

/-- Equivalent epsilon-delta form of Γ(theta) → 0 from the right;
Γ is nonnegative and nondecreasing on theta ≥ 0. -/
def CompletionStable (F : LocalData) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ completionModulus F θ ≤ η

/-- Explicit +infinity branch precedes conversion to the reals. -/
def removalQueryBound (F : LocalData) (ε : ℝ) : ℕ :=
  if removalModulus F ε = ⊤ then 0
  else Nat.choose F.k 2 * ⌈Real.log 3 / (removalModulus F ε).toReal⌉₊

end MetricTesting.Characterization


