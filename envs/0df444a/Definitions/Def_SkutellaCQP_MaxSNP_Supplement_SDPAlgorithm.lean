-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDPAlgorithm
-- name    : SkutellaCQP_MaxSNP_Supplement_SDPAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:48:13.157627+00:00
-- url     : https://prove2.me/theorems/2775ddea-8226-4695-9fba-2e161958d3b1
-- title:
--   Finite implementations of the ideal SDP rounding laws
-- statement:
--   The computational two-machine input contains arbitrary positive rational processing times and nonnegative rational weights. A finite SDP output encodes rational unit vectors and a rational objective, with antipodal machine vectors. Shape conditions protect every table lookup.
--
--   One uniform finite-alphabet machine computes the SDP output. Another receives the instance, a requested accuracy $k$ in unary, and $N=q(|I|+k+1)$ fair random bits; it returns one machine bit per job. Its joint law is the actual finite fair-coin average. A finite implementation of a specified ideal rounding law requires a feasible SDP output within half the prescribed sufficient tolerance, and
--   $$d_{\rm TV}(\mu_{I,k},\mu_{\rm ideal})\le2^{-k}.$$
--   The half tolerance reserves numerical slack for implementing continuous sphere sampling with finite coins. Approximation guarantees are separate theorem conclusions, not built into this implementation predicate. All machines and polynomial bounds are uniform across instances and accuracies. The zero-weight instance is included.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 3, 24–29; approximation algorithms in Theorems 5.4–5.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Encoding
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Hyperplane

namespace SkutellaCQP.MaxSNP.Supplement

open Finset

/-- Finite binary input to the two-machine algorithm. All rational data are retained. -/
structure TwoInput where
  n : ℕ
  p : Two → Fin n → ℚ
  w : Fin n → ℚ
  p_pos : ∀ i j, 0 < p i j
  w_nonneg : ∀ j, 0 ≤ w j

def TwoInput.code (I : TwoInput) : List Bool :=
  natCode I.n ++
  listCode ratCode ((List.finRange 2).flatMap fun i => (List.finRange I.n).map (I.p i)) ++
  listCode ratCode ((List.finRange I.n).map I.w)

def TwoInput.pr (I : TwoInput) (i : Two) (j : Fin I.n) : ℝ := I.p i j

def TwoInput.wr (I : TwoInput) (j : Fin I.n) : ℝ := I.w j

/-- A finite rational vector solution, not an unspecified real-number oracle.
The second machine vector is the negative of the first. -/
structure SDPOutput where
  machineZero : List ℚ
  jobs : List (List ℚ)
  Z : ℚ

def SDPOutput.code (o : SDPOutput) : List Bool :=
  listCode ratCode o.machineZero ++ listCode (listCode ratCode) o.jobs ++ ratCode o.Z

def SDPOutput.Shape (I : TwoInput) (o : SDPOutput) : Prop :=
  o.machineZero.length = I.n + 1 ∧ o.jobs.length = I.n ∧
  ∀ j : Fin I.n, (o.jobs[j.val]?.getD []).length = I.n + 1

/-- The real vectors represented by an output code. Shape is always asserted by the pipeline. -/
def SDPOutput.vectors (I : TwoInput) (o : SDPOutput) : Vectors I.n :=
  let u : Vec I.n := WithLp.toLp 2 (fun k => ((o.machineZero[k.val]?.getD 0 : ℚ) : ℝ))
  { machine := fun i => if i = 0 then u else -u
    job := fun j => WithLp.toLp 2
      (fun k => (((o.jobs[j.val]?.getD [])[k.val]?.getD 0 : ℚ) : ℝ)) }

/-- Decode one output bit per job as one of the two machines. -/
def bitAssignment (n : ℕ) (s : List Bool) (j : Fin n) : Two :=
  if s[j.val]?.getD false then 1 else 0

/-- Sampling input: encoded instance, unary precision, then fair random bits.
Unary precision means polynomial dependence on the number of accuracy bits. -/
def sampleInput (I : TwoInput) (k : ℕ) (bits : List Bool) : List Bool :=
  wordPair (wordPair I.code (List.replicate k true)) bits

/-- The joint law of an actual finite fair-coin program. There are `q(|I|+k+1)` coins;
`B` is one uniform Turing-computable function on bit strings. -/
noncomputable def coinLaw (q : Polynomial ℕ) (B : List Bool → List Bool)
    (I : TwoInput) (k : ℕ) (σ : Fin I.n → Two) : ℝ :=
  let N := q.eval (I.code.length + k + 1)
  ∑ b : Fin N → Bool,
    if bitAssignment I.n (B (sampleInput I k (List.ofFn b))) = σ
    then (1 / 2 : ℝ) ^ N else 0

/-- Total variation distance of finite assignment laws. -/
noncomputable def lawDistance {n : ℕ} (μ ν : (Fin n → Two) → ℝ) : ℝ :=
  (∑ σ, |μ σ - ν σ|) / 2

/-- A uniform finite implementation of a specified rounding law. It computes a feasible
near-optimal SDP solution, and approximates that solution's specified joint rounding law
at every requested precision. Performance guarantees are separate theorem conclusions.

The factor 1/2 in the solver accuracy reserves slack for implementing the ideal continuous
hyperplane sample with finite fair coins; no exact irrational coin probabilities are assumed. -/
def SDPImplementation
    (tol : {n : ℕ} → (Two → Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (law : {n : ℕ} → (Two → Fin n → ℝ) → (Fin n → ℝ) → Vectors n → ℝ →
      ((Fin n → Two) → ℝ))
    (A : TwoInput → SDPOutput) (q : Polynomial ℕ) (B : List Bool → List Bool) : Prop :=
  PolyMap TwoInput.code SDPOutput.code A ∧ Grunbaum2003.ContainmentPolyTime B ∧
  (∀ I, (A I).Shape I ∧ AlmostOptimal I.pr I.wr ((A I).vectors I) (A I).Z
    (tol I.pr I.wr / 2)) ∧
  (∀ I k, lawDistance (coinLaw q B I k)
    (law I.pr I.wr ((A I).vectors I) (A I).Z) ≤ (1 / 2 : ℝ) ^ k) ∧
  (∀ I k (b : Fin (q.eval (I.code.length + k + 1)) → Bool),
    (B (sampleInput I k (List.ofFn b))).length = I.n)

end SkutellaCQP.MaxSNP.Supplement


