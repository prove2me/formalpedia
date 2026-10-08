-- Prove2me | Definitions.Def_TotientCompanionZero
-- name    : TotientCompanionZero
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:33.137981+00:00
-- url     : https://prove2.me/theorems/de79d123-f22a-4db6-b8e1-0d67f04ec942
-- statement:
--   This block sets up the definitions for a weighted totient companion statement without a seed. IsTotient(v) means v=φ(n) for some positive n, and ell(v) is the least such n (zero if v is not a totient value). The sequence a(j)=(j+1)log(j+1) − j log j − 1 defines RenewalRootSet, the set of z with 0<z<1 and ∑_{j≥0} a(j+1) z^{j+1} = 1; rho is its infimum, lam=log(1/rho), gamma is the reciprocal of ∑_{j≥0}(j+1)a(j+1)rho^{j+1}, alpha(s)=lam·e^{lam s}, and P(H)=⌊log log H⌋. largestPrimeFactor(n) is the maximum of 1 and the prime factors of n. A TailDatum of length H consists of a function Q from Fin H to ℕ and a natural-number cofactor; tailPrime reads Q(h) for h<H and gives 1 otherwise, and tailLog is log log of that value. IsWitness(H,s,η) requires Q(h)=1 for h<P(H), a positive cofactor, and for every h with P(H)≤h<H that Q(h) is prime, that tailLog(h) lies between 9/10 and 11/10 times alpha(s)·h·rho^{−h}, and that ∑_{P(H)≤l<h} a(h−l)·tailLog(l) ≤ (1+e^{−h/40}/10000)·tailLog(h); it also requires the cofactor's largestPrimeFactor to be at most Q(P(H)) and log(cofactor) ≤ exp(2·alpha(s)·P(H)·rho^{−P(H)}). The weight w(η) is the cofactor times the product of Q(h) over P(H)≤h<H, and witnesses(H,s,d) is the set of witnesses with φ(w(η))=d. D(h,η)=∑_{P(H)≤l<H} a(h−l)·tailLog(l), and maxD(h,T) is the maximum of D(h,·) over a finite set T of data (zero if T is empty). AH(H,f,s) is rho^{H(H−1)/2}(gamma/alpha(s))^H times a finsum over totient values d of f(ell(d)/d)/d times a finsum over nonempty finite sets T of data all of which are witnesses for d, of (−1)^{|T|−1}·exp(−(gamma/alpha(s))·∑_{n≥0} rho^{H+n}·maxD(H+n,T)); non-totient d and other T contribute zero. A(f,s) is the limit of AH(H,f,s) as H→∞, taken via limUnder. N(k,x) counts totient values v≤x with kx<ell(v)≤(k+1)x, and fk(k,r)=min(1,(k+1)/r) − min(1,k/r). No theorem is stated in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TotientCompanionZero.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TotientCompanionZero.lean; bytes 16..3143
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! The no-seed alternative of the weighted totient companion theorem. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def IsTotient (v : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ n.totient = v

def ell (v : ℕ) : ℕ := by
  classical
  exact if h : IsTotient v then Nat.find h else 0

def a (j : ℕ) : ℝ := (j + 1 : ℝ) * Real.log (j + 1) - j * Real.log j - 1

def RenewalRootSet : Set ℝ :=
  {z | 0 < z ∧ z < 1 ∧ (∑' j : ℕ, a (j+1) * z^(j+1)) = 1}

def rho : ℝ := sInf RenewalRootSet

def lam : ℝ := Real.log (1 / rho)

def gamma : ℝ := (∑' j : ℕ, (j+1 : ℝ) * a (j+1) * rho^(j+1))⁻¹

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

def N (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (((Finset.Icc 1 ⌊x⌋₊).filter fun v =>
    IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x).card : ℝ)

def fk (k : ℕ) (r : ℝ) : ℝ := min 1 ((k+1 : ℝ) / r) - min 1 ((k : ℝ) / r)



end TotientAsymptotic
end
end OAI


