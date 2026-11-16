-- Prove2me | Definitions.Def_FairKMeans_Supplement_Hardness
-- name    : FairKMeans_Supplement_Hardness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:01:36.476193+00:00
-- url     : https://prove2.me/theorems/90dce311-bc3a-48f6-9460-6f6f71b1116a
-- title:
--   Rational one-dimensional fair $k$-means instances, their bit encoding, and valid $(3-\delta)$-approximate outputs
-- statement:
--   On a Turing machine the input of fair $k$-means is a finite string, so the instances of Theorem 7 are rational: $n$ points of the line $\mathbb Q$, $m$ possibly overlapping groups $P^{(i)}$, an integer $k\ge1$, and bounds $\alpha_i,\beta_i\in[0,1]\cap\mathbb Q$. Such an instance is cast into a real instance of fair $k$-means in dimension $d=1$. An instance is **restricted** if $\beta_i=1/2$ and $\alpha_i\in\{1/2,1\}$ for every group.
--
--   Instances and outputs are encoded as bit strings by self-delimiting binary codes of natural numbers and rationals: $n,m,k$, the points, the membership bits of the groups, $\alpha$ and $\beta$. An output is a rational solution: a number $s$ of centers, $s$ centers on the line and an $n\times s$ matrix. It is **valid with parameter $\delta$** if $s\le k$ and the matrix is an $(\alpha,\beta)$-fair fractional assignment with
--
--   $$\mathrm{Cost}(P,S,\phi_S)\le(3-\delta)\,\mathrm{OPT},$$
--
--   where $\mathrm{OPT}$ is the optimal cost of the integral version of the instance.
--
--   **Formalization Note** The encodings reuse `encodeNat` and `encodeRat` of the published `KMedianThreshold`; the real instance, fairness, cost and $\mathrm{OPT}$ are the published ones of `FairKMeans.Model`.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 7, p.5 (PDF p.7), footnote 1 (PDF p.7); proof of Theorem 7, Section 7.6, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_KMedianThreshold

namespace FairKMeans.Supplement

/-!
# Rational one-dimensional fair k-means instances, their bit encoding, and valid outputs

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 7, p.5 (PDF 7),
with footnote 1 ("Theorem 7, like every NP-hardness result, concerns polynomial time on a Turing
machine"); proof of Theorem 7, Section 7.6, p.46 (PDF 48).

**Formalization Note.** On a Turing machine an instance is a finite string, so the instances are
rational: `n` points of the line `ℚ`, `m` groups (possibly overlapping), `k ≥ 1`, and bounds
`α, β ∈ [0,1] ∩ ℚ`. `toInstance` casts such an instance into the published real instance
`FairKMeans.Instance 1 n m` (a point `x` becomes the vector `(x) ∈ ℝ¹`). The encoding is an
explicit, injective bit string built from the published self-delimiting `OAI.MetricKMedian.encodeNat`
and `encodeRat` (`KMedianThreshold`): `n, m, k`, the `n` points, the `m·n` membership bits of the
groups, the `m` upper and the `m` lower bounds. An output is a rational solution (number `s` of
centers, centers on the line, an `n × s` matrix), encoded the same way; it is valid with
parameter `δ` if it has at most `k` centers and its cast is an `(α, β)`-fair fractional
assignment of cost at most `(3 − δ)·OPT` (published `IsAssignment`, `IsFair`, `cost`, `OPT`).
-/

open FairKMeans

/-- A rational instance of fair k-means on the line. -/
structure RatInst where
  /-- Number of points. -/
  n : ℕ
  /-- Number of groups. -/
  m : ℕ
  /-- Number of centers. -/
  k : ℕ
  one_le_k : 1 ≤ k
  /-- The points, on the line. -/
  pts : Fin n → ℚ
  /-- The groups. -/
  grp : Fin m → Finset (Fin n)
  /-- Upper bounds `α`. -/
  α : Fin m → ℚ
  /-- Lower bounds `β`. -/
  β : Fin m → ℚ
  α_mem : ∀ i, 0 ≤ α i ∧ α i ≤ 1
  β_mem : ∀ i, 0 ≤ β i ∧ β i ≤ 1

/-- The restricted class of Theorem 7: `β_i = 1/2` and `α_i ∈ {1/2, 1}` for every group. -/
def RatInst.Restricted (J : RatInst) : Prop :=
  ∀ i, J.β i = 1 / 2 ∧ (J.α i = 1 / 2 ∨ J.α i = 1)

/-- A rational number of the line as a point of `ℝ¹`. -/
noncomputable def linePt (x : ℚ) : E 1 := EuclideanSpace.single (0 : Fin 1) (x : ℝ)

/-- The real instance `FairKMeans.Instance 1 n m` of a rational instance. -/
noncomputable def RatInst.toInstance (J : RatInst) : Instance 1 J.n J.m where
  pts := fun p => linePt (J.pts p)
  grp := J.grp
  k := J.k
  one_le_k := J.one_le_k
  α := fun i => (J.α i : ℝ)
  β := fun i => (J.β i : ℝ)
  α_mem := fun i => ⟨by exact_mod_cast (J.α_mem i).1, by exact_mod_cast (J.α_mem i).2⟩
  β_mem := fun i => ⟨by exact_mod_cast (J.β_mem i).1, by exact_mod_cast (J.β_mem i).2⟩

/-- The bit encoding of a rational instance. -/
def encodeRatInst (J : RatInst) : List Bool :=
  OAI.MetricKMedian.encodeNat J.n ++ OAI.MetricKMedian.encodeNat J.m ++
    OAI.MetricKMedian.encodeNat J.k ++
    (List.ofFn (fun p : Fin J.n => OAI.MetricKMedian.encodeRat (J.pts p))).flatten ++
    (List.ofFn (fun i : Fin J.m => List.ofFn (fun p : Fin J.n => decide (p ∈ J.grp i)))).flatten ++
    (List.ofFn (fun i : Fin J.m => OAI.MetricKMedian.encodeRat (J.α i))).flatten ++
    (List.ofFn (fun i : Fin J.m => OAI.MetricKMedian.encodeRat (J.β i))).flatten

/-- A rational solution for an instance with `n` points: `s` centers on the line and an
`n × s` matrix. -/
structure RatSol (n : ℕ) where
  /-- Number of centers. -/
  s : ℕ
  /-- The centers. -/
  centers : Fin s → ℚ
  /-- The assignment matrix. -/
  assign : Fin n → Fin s → ℚ

/-- The bit encoding of a rational solution. -/
def encodeRatSol {n : ℕ} (sol : RatSol n) : List Bool :=
  OAI.MetricKMedian.encodeNat sol.s ++
    (List.ofFn (fun t : Fin sol.s => OAI.MetricKMedian.encodeRat (sol.centers t))).flatten ++
    (List.ofFn (fun p : Fin n =>
      (List.ofFn (fun t : Fin sol.s => OAI.MetricKMedian.encodeRat (sol.assign p t))).flatten)).flatten

/-- The centers of a rational solution, as points of `ℝ¹`. -/
noncomputable def RatSol.realCenters {n : ℕ} (sol : RatSol n) : Fin sol.s → E 1 :=
  fun t => linePt (sol.centers t)

/-- The matrix of a rational solution, cast to `ℝ`. -/
def RatSol.realAssign {n : ℕ} (sol : RatSol n) : Fin n → Fin sol.s → ℝ :=
  fun p t => (sol.assign p t : ℝ)

/-- A valid output with parameter `δ` (Theorem 7): at most `k` centers `S` and an
`(α, β)`-fair fractional assignment `φ_S` with `Cost(P, S, φ_S) ≤ (3 − δ) OPT`. -/
def Valid (δ : ℝ) (J : RatInst) (sol : RatSol J.n) : Prop :=
  sol.s ≤ J.k ∧ IsAssignment sol.realAssign ∧ IsFair J.toInstance sol.realAssign ∧
    cost J.toInstance sol.realCenters sol.realAssign ≤ (3 - δ) * OPT J.toInstance

end FairKMeans.Supplement


