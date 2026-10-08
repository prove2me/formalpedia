-- Prove2me | Definitions.Def_TotientAsymptotic
-- name    : TotientAsymptotic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.927557+00:00
-- url     : https://prove2.me/theorems/190919ec-02e1-43d4-a95c-4efaf85d375a
-- statement:
--   This block sets up the machinery for counting Euler totient values and their least preimages. IsTotient(v) means v=φ(n) for some positive integer n; V(x) counts totient values in [1,⌊x⌋], and ell(v) is the least positive n with φ(n)=v (zero if v is not a totient). The coefficients are a(j)=(j+1)log(j+1) − j log j − 1. RenewalRootSet is the set of z in (0,1) with Σ_{j≥0} a(j+1) z^{j+1}=1 (tsum); rho is its infimum, lam=log(1/rho), and gamma is the reciprocal of Σ_{j≥0}(j+1)a(j+1)rho^{j+1}. The sequence g is defined recursively by g(0)=1 and g(n+1)=Σ_{d=0}^{n} a(d+1) g(n−d). With B(x)=log log x, psi(b)=(log b − log log b)/lam, m(x)=⌊psi(B(x))⌋ and theta(x)=psi(B(x))−m(x), the weight G(x,j)=B(x)^j/(j!·∏_{i=1}^{j} g(i)). Further, P(H)=⌊log log H⌋, alpha(s)=lam·e^{lam s}, and largestPrimeFactor(n) is the maximum of 1 and the largest prime divisor of n. A TailDatum of length H consists of H natural numbers Q(0..H−1) and a cofactor; tailPrime reads Q(h) (and gives 1 beyond range) and tailLog is log log of it. IsWitness(H,s,η) requires Q(h)=1 for h<P(H), a positive cofactor, and for each h in [P(H),H) that Q(h) is prime with 0.9·alpha(s)·h·rho^{−h} ≤ tailLog(h) ≤ 1.1·alpha(s)·h·rho^{−h} and Σ_{l=P(H)}^{h−1} a(h−l) tailLog(l) ≤ (1+10^{−4}e^{−h/40}) tailLog(h); it also requires the cofactor's largest prime factor to be at most Q(P(H)) and log(cofactor) ≤ exp(2·alpha(s)·P(H)·rho^{−P(H)}). The product w(η) is the cofactor times the product of the Q(h) for h in [P(H),H), and witnesses(H,s,d) are witness data with φ(w(η))=d. D(h,η)=Σ_{l=P(H)}^{H−1} a(h−l) tailLog(l), and maxD takes the maximum of D(h,·) over a nonempty finite set of data (zero if empty). AH(H,f,s) is an inclusion-exclusion expression: rho^{H(H−1)/2}(gamma/alpha(s))^H times a sum over totients d of f(ell(d)/d)/d times a sum over nonempty finite sets T of witnesses for d of (−1)^{|T|−1} exp(−(gamma/alpha(s))·Σ_{n≥0} rho^{H+n} maxD(H+n,T)), using finsum and tsum conventions. A(f,s) is the limit of AH(H,f,s) as H→∞ (limUnder), and mainTerm(x)=(x/log x)·G(x,m(x))·A(1,theta(x)). Finally N(k,x) counts totients v≤x with kx<ell(v)≤(k+1)x, fk(k,r)=min(1,(k+1)/r)−min(1,k/r), and normalizedCount(F,x) and tupleNormalization(x) divide by or equal (x/log x)·G(x,m(x)). These are definitions only, with no asymptotic result asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TotientAsymptotic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TotientAsymptotic.lean; bytes 16..3911
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Totient counting and least-preimage asymptotics. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

def V (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter IsTotient).card : ℝ)

def ell (v : ℕ) : ℕ := by
  classical
  exact if h : IsTotient v then Nat.find h else 0

def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j+1) * z^(j+1)) = 1}

def rho : ℝ := sInf RenewalRootSet

def lam : ℝ := Real.log (1 / rho)

def gamma : ℝ := (∑' j : ℕ, (j+1 : ℝ) * a (j+1) * rho^(j+1))⁻¹

def g : ℕ → ℝ
  | 0 => 1
  | n+1 => ∑ d ∈ Finset.range (n+1), a (d+1) * g (n-d)
termination_by n => n

def B (x : ℝ) : ℝ := Real.log (Real.log x)
def psi (b : ℝ) : ℝ := (Real.log b - Real.log (Real.log b)) / lam

def m (x : ℝ) : ℕ := ⌊psi (B x)⌋₊
def theta (x : ℝ) : ℝ := psi (B x) - m x

def G (x : ℝ) (j : ℕ) : ℝ :=
  (B x)^j / ((Nat.factorial j : ℝ) * ∏ i ∈ Finset.Icc 1 j, g i)

def P (H : ℕ) : ℕ := ⌊Real.log (Real.log (H : ℝ))⌋₊
def alpha (s : ℝ) : ℝ := lam * Real.exp (lam * s)

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

structure TailDatum (H : ℕ) where
  Q : Fin H → ℕ
  cofactor : ℕ

def tailPrime {H : ℕ} (η : TailDatum H) (h : ℕ) : ℕ :=
  if hH : h < H then η.Q ⟨h, hH⟩ else 1

def tailLog {H : ℕ} (η : TailDatum H) (h : ℕ) : ℝ :=
  Real.log (Real.log (tailPrime η h : ℝ))

def IsWitness (H : ℕ) (s : ℝ) (η : TailDatum H) : Prop :=
  (∀ h : Fin H, h.val < P H → η.Q h = 1) ∧
  0 < η.cofactor ∧
  (∀ h ∈ Finset.Ico (P H) H, (tailPrime η h).Prime ∧
    (9 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ≤ tailLog η h ∧
    tailLog η h ≤ (11 / 10 : ℝ) * alpha s * h * (rho^h)⁻¹ ∧
    (∑ l ∈ Finset.Ico (P H) h, a (h-l) * tailLog η l) ≤
      (1 + (1 / 10000 : ℝ) * Real.exp (-(h : ℝ) / 40)) * tailLog η h) ∧
  largestPrimeFactor η.cofactor ≤ tailPrime η (P H) ∧
  Real.log (η.cofactor : ℝ) ≤
    Real.exp (2 * alpha s * (P H : ℝ) * (rho^(P H))⁻¹)

def w {H : ℕ} (η : TailDatum H) : ℕ :=
  η.cofactor * ∏ h ∈ Finset.Ico (P H) H, tailPrime η h

def witnesses (H : ℕ) (s : ℝ) (d : ℕ) : Set (TailDatum H) :=
  {η | IsWitness H s η ∧ (w η).totient = d}

def D {H : ℕ} (h : ℕ) (η : TailDatum H) : ℝ :=
  ∑ l ∈ Finset.Ico (P H) H, a (h-l) * tailLog η l

def maxD {H : ℕ} (h : ℕ) (T : Finset (TailDatum H)) : ℝ := by
  classical
  exact if ht : T.Nonempty then T.sup' ht (D h) else 0

def AH (H : ℕ) (f : ℝ → ℝ) (s : ℝ) : ℝ := by
  classical
  exact rho^(H*(H-1)/2) * (gamma / alpha s)^H *
    ∑ᶠ d : ℕ,
      if IsTotient d then
        f ((ell d : ℝ) / d) / d *
          ∑ᶠ T : Finset (TailDatum H),
            if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
              (-1 : ℝ)^(T.card-1) *
               Real.exp (-(gamma / alpha s) *
                 ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
            else 0
      else 0

def A (f : ℝ → ℝ) (s : ℝ) : ℝ := limUnder atTop (fun H : ℕ => AH H f s)

def mainTerm (x : ℝ) : ℝ := x / Real.log x * G x (m x) * A (fun _ => 1) (theta x)

def N (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x).card : ℝ)

def fk (k : ℕ) (r : ℝ) : ℝ := min 1 ((k+1 : ℝ) / r) - min 1 ((k : ℝ) / r)

def normalizedCount (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x / (x / Real.log x * G x (m x))

def tupleNormalization (x : ℝ) : ℝ := x / Real.log x * G x (m x)



end TotientAsymptotic
end
end OAI


