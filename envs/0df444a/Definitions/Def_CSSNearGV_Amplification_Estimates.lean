-- Prove2me | Definitions.Def_CSSNearGV_Amplification_Estimates
-- name    : CSSNearGV_Amplification_Estimates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:17:25.945447+00:00
-- url     : https://prove2.me/theorems/5698fd26-07c0-423b-b82c-89d972502925
-- title:
--   Uniform asymptotic bounds and nonzero trajectory counts
-- statement:
--   For fixed block size and round parameters, constants and thresholds precede the blocklength and all weight indices. A soft polynomial estimate means
--   $$F(n)\le C n^a(1+\log n)^q$$
--   for all sufficiently large admissible $n=sb$, with $C>0$ and $q\in\mathbb N$. Negligibility means a bound for every inverse polynomial. Define $T=(\log n)^2$, $\tau=T/n$, and $B_T=([1,T)\cup(n-T,n])\cap\mathbb Z$.
--
--   Boundary counts retain weight $n$ and omit zero. Low-weight counts explicitly omit zero. Middle counts count actual nonzero initial parity words, with the intermediate and final weights obtained by the same permutation tuple. The two classical orientations and their distinct exponents remain separate.
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Sections 3.1 and 5, printed pp.8–9,15–23 / PDF 10–11,17–25

import Definitions.Def_CSSNearGV_Amplification_Ensemble
import Definitions.Def_CSSNearGV_Amplification_Spectral

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification
attribute [local instance] Classical.propDecidable

/-- Constants precede blocklength; s and the fixed function's parameters may be dependencies. -/
def SoftBound (s : ℕ) (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q N : ℕ, ∀ b : ℕ, 1 ≤ b → N ≤ s * b →
    f b ≤ C * (s * b : ℝ) ^ a * (1 + Real.log (s * b)) ^ q

def Negligible (s : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ b : ℕ, 1 ≤ b → N ≤ s * b →
    f b ≤ C * (s * b : ℝ) ^ (-(p : ℝ))

def T (n : ℕ) : ℝ := (Real.log n) ^ 2
def tau (n : ℕ) : ℝ := T n / n

def Boundary (n c : ℕ) : Prop :=
  1 ≤ c ∧ c ≤ n ∧ ((c : ℝ) < T n ∨ (n : ℝ) - T n < c)

def boundaryCount (s b m : ℕ) (ad : Bool) : ℝ :=
  ∑ c ∈ (Finset.range (s * b + 1)).filter (Boundary (s * b)), enumerator s b m ad c

def lowCount (s b m : ℕ) (ad : Bool) (d : ℝ) : ℝ :=
  ∑ c ∈ (Finset.range (s * b + 1)).filter (fun c : ℕ => 0 < c ∧ (c : ℝ) ≤ d * (s * b)),
    enumerator s b m ad c

def prefixPerms {n m : ℕ} (π : Perms n m) (r : ℕ) : Perms n r :=
  fun i => if h : i.val < 2 * m then π ⟨i.val, h⟩ else Equiv.refl _

/-- Count trajectories of the actual ensemble, excluding the zero initial word. -/
def middleCount (s b m : ℕ) (ad : Bool) (ε : ℝ) : ℝ :=
  average fun π : Perms (s * b) m =>
    ((Finset.univ.filter fun x : Word (s * b) =>
      x ∈ parity s b ∧ x ≠ 0 ∧
      let w := (weight ((amplifier ad (prefixPerms π (m - 1))).mulVec x) : ℝ)
      let v := (weight ((amplifier ad π).mulVec x) : ℝ)
      T (s * b) ≤ w ∧ w ≤ (s * b : ℝ) - T (s * b) ∧
      (v ≤ (delta s m - ε) * (s * b) ∨ (1 - delta s m + ε) * (s * b) ≤ v)).card : ℝ)

/-- The two classical orientations retain their different failure exponents. -/
def DistanceTail (s m : ℕ) (ad : Bool) (ε a : ℝ) : Prop :=
  SoftBound s (fun b => lowCount s b m ad (delta s m - ε)) a ∧
  SoftBound s (fun b => probability fun π : Perms (s * b) m =>
    ¬ distanceGreater (classicalCode s b m ad π) ((delta s m - ε) * (s * b))) a

def ClassicalTail (s m : ℕ) (ad : Bool) (ε a : ℝ) : Prop :=
  (∀ b : ℕ, 1 ≤ b → ∀ π : Perms (s * b) m,
    Module.finrank Bit (classicalCode s b m ad π) = (s - 1) * b) ∧
  SoftBound s (fun b => probability fun π : Perms (s * b) m =>
    ¬ distanceAtLeast (classicalCode s b m ad π) ((delta s m - ε) * (s * b))) a

end CSSNearGV.Amplification


