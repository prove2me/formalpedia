-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Laws
-- name    : ZLIPPadding_Padding_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:01.610275+00:00
-- url     : https://prove2.me/theorems/042be4ae-5fba-4219-b2cb-392300ad0345
-- title:
--   Discrete probability laws, Gram-only oracles and ideal randomization
-- statement:
--   For a probability mass function $\mu$, define event mass by summation and probability as its real value. Total variation at most $\varepsilon$ means
--   $$|\mu(E)-\nu(E)|\leq\varepsilon\quad\text{for every event }E.$$
--   An ideal Gram randomization law is supported on pairs $(H,U)$ with $U$ unimodular and $H=U^TGU$ and is invariant under $(H,U)\mapsto(H,VU)$ for every $V^TGV=G$.
--
--   An oracle is a family of probability kernels indexed only by dimension and the queried Gram matrix. Correctness for a length guarantee $\Gamma$ requires every supported answer to be a nonzero integer vector $q$ with $q^THq\leq\Gamma(n)^2$ on every promised input. Binding the randomizer law to this kernel models independent private oracle coins. Mapped-back laws, Gram-stabilizer orbits, signed invariance and independent repeated experiments are defined directly. No invariant output conclusion is assumed.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 8–10, 28–29 (PDF pp. 9–11, 29–30), §2.3 and (7.3), (7.7)–(7.8)

import Definitions.Def_ZLIPPadding_Padding_GramModel

namespace ZLIPPadding.Padding
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def mass {α : Type} (μ : PMF α) (E : Set α) : ℝ≥0∞ :=
  ∑' x, if x ∈ E then μ x else 0

def prob {α : Type} (μ : PMF α) (E : Set α) : ℝ := (mass μ E).toReal

/-- Eventwise TV definition avoids a real supremum's empty/unbounded defaults. -/
def TVClose {α : Type} (μ ν : PMF α) (ε : ℝ) : Prop :=
  ∀ E : Set α, |prob μ E - prob ν E| ≤ ε

def iid {α : Type} (μ : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | t + 1 => μ.bind fun x => (iid μ t).map (x :: ·)

def Stabilizes {n : ℕ} (G V : ZMat n) : Prop :=
  Unimodular V ∧ V.transpose * G * V = G

def equivGram {n : ℕ} (G H : ZMat n) : Prop :=
  ∃ U : ZMat n, Unimodular U ∧ H = U.transpose * G * U

def gramOrbit {n : ℕ} (G : ZMat n) (a : ZVec n) : Set (ZVec n) :=
  {z | ∃ V : ZMat n, Stabilizes G V ∧ z = V.mulVec a}

/-- Correct joint randomization law, before any vector oracle is used. -/
def IdealRandomization {n : ℕ} (G : ZMat n) (μ : PMF (ZMat n × ZMat n)) : Prop :=
  (∀ hu, μ hu ≠ 0 → Unimodular hu.2 ∧ hu.1 = hu.2.transpose * G * hu.2) ∧
  ∀ V : ZMat n, Stabilizes G V → μ.map (fun hu => (hu.1, V * hu.2)) = μ

abbrev Oracle := ∀ n : ℕ, ZMat n → PMF (ZVec n)

def CorrectOracle (Γ : ℕ → ℝ) (A : Oracle) : Prop :=
  ∀ n H, ValidGram H → ∀ q, A n H q ≠ 0 → q ≠ 0 ∧ (qnorm H q : ℝ) ≤ Γ n ^ 2

def mappedLaw {n : ℕ} (μ : PMF (ZMat n × ZMat n))
    (A : ZMat n → PMF (ZVec n)) : PMF (ZVec n) :=
  μ.bind fun hu => (A hu.1).map hu.2.mulVec

/-- Explicit product experiment: fresh randomizer and fresh private oracle coins. -/
def repeatedMapped {n : ℕ} (μ : PMF (ZMat n × ZMat n))
    (A : ZMat n → PMF (ZVec n)) (t : ℕ) : PMF (List (ZVec n)) :=
  (iid (μ.bind fun hu => (A hu.1).map fun q => (hu, q)) t).map
    (List.map fun w => w.1.2.mulVec w.2)

def SignedInvariant {n : ℕ} (μ : PMF (ZVec n)) : Prop :=
  ∀ p s, μ.map (signedAction p s) = μ

end
end ZLIPPadding.Padding


