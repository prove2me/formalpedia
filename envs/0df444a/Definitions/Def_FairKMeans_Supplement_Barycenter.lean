-- Prove2me | Definitions.Def_FairKMeans_Supplement_Barycenter
-- name    : FairKMeans_Supplement_Barycenter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:01:06.544578+00:00
-- url     : https://prove2.me/theorems/2f218bf8-2e5c-44ae-b072-a3771366366c
-- title:
--   $k$-sparse Wasserstein barycenters: transport plans, $W_2$, $\mathrm{Cost}_{WB}$, $\mathrm{OPT}_{WB}$, the associated instance and the barycenter algorithm
-- statement:
--   The input consists of $m\ge1$ discrete probability distributions $P^{(1)},\dots,P^{(m)}$ on $\mathbb R^d$ with $n$ atoms in total: every atom $q$ has a location, belongs to one distribution and carries a mass $w(q)>0$, and the masses of each distribution sum to $1$; $P=P^{(1)}\uplus\dots\uplus P^{(m)}$; and an integer $k\ge1$. A finitely supported distribution $B$ has atoms $s$ with masses $b_s$.
--
--   A **transport plan** from $P^{(i)}$ to $B$ is a nonnegative $F_i$ on $P^{(i)}\times\operatorname{supp}(B)$ with
--
--   $$\sum_{s}F_i(q,s)=w(q)\ (q\in P^{(i)}),\qquad \sum_{q\in P^{(i)}}F_i(q,s)=b_s. \tag{51}$$
--
--   The squared Wasserstein distance is $W_2(P^{(i)},B)=\min_{F_i}\sum_{q}\sum_{s}F_i(q,s)\|q-s\|^2$, and
--
--   $$\mathrm{Cost}_{WB}(B)=\frac1m\sum_{i=1}^mW_2(P^{(i)},B),$$
--
--   with $\mathrm{OPT}_{WB}$ the infimum of $\mathrm{Cost}_{WB}(B)$ over probability distributions supported on at most $k$ points of $\mathbb R^d$ (Definition 2).
--
--   The **associated instance** has the points of $P$ with weights $w(q)$, the same $k$, and for each $i$ the two constraints $\sum_p w(p)(\mathbf 1[p\in P^{(i)}]-\tfrac1m)\phi(p,s)\ge0$ and $\sum_p w(p)(\tfrac1m-\mathbf 1[p\in P^{(i)}])\phi(p,s)\ge0$ (Remark 31 with $\alpha_i=\beta_i=1/m$). The **barycenter algorithm** runs the weighted Algorithm 1 on it and returns the distribution on the output centers with masses $w(s)/m=\frac1m\sum_q w(q)\phi(q,s)$ (Lemma 43, part 1).
--
--   **Formalization Note** $W_2$ denotes the squared distance, as in the paper. A distribution is a family of atoms with masses; zero masses and repeated atoms are allowed, which changes no transport cost, so "supported on at most $k$ points" is "at most $k$ atoms". $W_2$ is written as an infimum over plans, which is attained for a probability distribution.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), squared Wasserstein distance and Definition 2, p.2 (PDF p.4); Section 8 notation, (51) and the associated fair instance, p.47 (PDF p.49); Remark 31, p.37 (PDF p.39); Lemma 43 and proof of Theorem 4, pp.47–48 (PDF pp.49–50)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1
import Definitions.Def_FairKMeans_Supplement_Constrained
import Definitions.Def_FairKMeans_Supplement_ConstrainedAlgorithm

namespace FairKMeans.Supplement

/-!
# k-sparse Wasserstein barycenters: instances, transport plans, `W₂`, `CostWB`, `OPTWB`,
# the associated instance and the barycenter algorithm

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…): squared Wasserstein
distance and Definition 2, p.2 (PDF 4); Section 8 notation and (51), "The associated fair
instance", p.47 (PDF 49); Remark 31, p.37 (PDF 39); proof of Theorem 4, p.48 (PDF 50).

**Formalization Note.** The `m` input distributions are given by `n` atoms with locations
`pts`, an owner `owner q ∈ [m]` (so `P = P⁽¹⁾ ⊎ ⋯ ⊎ P⁽ᵐ⁾` is an indexed disjoint union and atoms
of different distributions may coincide in location) and masses `mass q > 0` summing to `1` over
each distribution; `m ≥ 1` (the paper's `1/m`). A finitely supported distribution `B` is a family
of `s` atoms with masses `b`; zero masses and repeated atoms are allowed (they change no transport
cost: a zero-mass atom receives nothing, and plans to repeated atoms merge), so "supported on at
most `k` points" is `s ≤ k`. `W2sq` is the paper's `W₂(P′, B)`, the **squared** distance (the
minimum of `∑ F(q,s)‖q − s‖²`, no square root), written as an infimum over transport plans (51);
for a probability distribution `B` the set of plans is nonempty (the product plan) and compact,
so the infimum is the paper's minimum. A plan is a function on all atoms; only the rows of
`P⁽ⁱ⁾` enter. The associated instance (p.47) is written with the `2m` homogeneous constraints of
Remark 31 for `α_i = β_i = 1/m`, which have the same feasible matrices as the fairness
constraints (12).
-/

open FairKMeans

/-- `m` discrete probability distributions on `ℝ^d` with `n` atoms in total, and `k ≥ 1`
(Definition 2; Section 8 notation). -/
structure BaryInstance (d n m : ℕ) where
  /-- Locations of the atoms. -/
  pts : Fin n → E d
  /-- The distribution `P⁽ⁱ⁾` that each atom belongs to. -/
  owner : Fin n → Fin m
  /-- The mass `w(q) > 0` of each atom. -/
  mass : Fin n → ℝ
  mass_pos : ∀ q, 0 < mass q
  /-- The masses of each distribution sum to `1`. -/
  mass_sum : ∀ i, ∑ q ∈ Finset.univ.filter (fun q => owner q = i), mass q = 1
  one_le_m : 1 ≤ m
  /-- The support bound. -/
  k : ℕ
  one_le_k : 1 ≤ k

/-- A finitely supported measure on `ℝ^d`: `s` atoms with masses. -/
structure FinDist (d : ℕ) where
  /-- Number of atoms. -/
  s : ℕ
  /-- Locations of the atoms. -/
  atoms : Fin s → E d
  /-- Masses `b_s`. -/
  mass : Fin s → ℝ

/-- `B` is a probability distribution: nonnegative masses summing to `1`. -/
def FinDist.IsProb {d : ℕ} (B : FinDist d) : Prop :=
  (∀ t, 0 ≤ B.mass t) ∧ ∑ t, B.mass t = 1

variable {d n m : ℕ}

/-- `F` is a transport plan from `P⁽ⁱ⁾` to `B` ((51), p.47): nonnegative on the rows of `P⁽ⁱ⁾`,
with marginals `w` and `b`. -/
def IsPlan (I : BaryInstance d n m) (i : Fin m) (B : FinDist d) (F : Fin n → Fin B.s → ℝ) :
    Prop :=
  (∀ q, I.owner q = i → ∀ t, 0 ≤ F q t) ∧
    (∀ q, I.owner q = i → ∑ t, F q t = I.mass q) ∧
    ∀ t, ∑ q ∈ Finset.univ.filter (fun q => I.owner q = i), F q t = B.mass t

/-- The squared Wasserstein distance `W₂(P⁽ⁱ⁾, B) = min_F ∑_q ∑_s F(q,s)‖q − s‖²` (p.2). -/
noncomputable def W2sq (I : BaryInstance d n m) (i : Fin m) (B : FinDist d) : ℝ :=
  sInf {c : ℝ | ∃ F : Fin n → Fin B.s → ℝ, IsPlan I i B F ∧
    ∑ q ∈ Finset.univ.filter (fun q => I.owner q = i), ∑ t, F q t * ‖I.pts q - B.atoms t‖ ^ 2
      = c}

/-- `CostWB(B) = (1/m) ∑_i W₂(P⁽ⁱ⁾, B)` (Definition 2). -/
noncomputable def CostWB (I : BaryInstance d n m) (B : FinDist d) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, W2sq I i B

/-- `OPTWB`: the infimum of `CostWB(B)` over probability distributions supported on at most `k`
points anywhere in `ℝ^d` (Definition 2). -/
noncomputable def OPTWB (I : BaryInstance d n m) : ℝ :=
  sInf {c : ℝ | ∃ B : FinDist d, B.s ≤ I.k ∧ B.IsProb ∧ CostWB I B = c}

/-- The associated instance (p.47) with the constraints of Remark 31 for `α_i = β_i = 1/m`:
points `P` weighted by their masses, the same `k`, and for each distribution `i` the lower bound
`∑_p w(p)(1[p ∈ P⁽ⁱ⁾] − 1/m) φ(p,s) ≥ 0` (index `i` in the first block) and the upper bound
`∑_p w(p)(1/m − 1[p ∈ P⁽ⁱ⁾]) φ(p,s) ≥ 0` (index `i` in the second block). -/
noncomputable def assoc (I : BaryInstance d n m) : HInstance d n (m + m) where
  pts := I.pts
  w := I.mass
  w_pos := I.mass_pos
  k := I.k
  one_le_k := I.one_le_k
  a := Fin.append
    (fun i p => I.mass p * ((if I.owner p = i then (1 : ℝ) else 0) - 1 / (m : ℝ)))
    (fun i p => I.mass p * (1 / (m : ℝ) - (if I.owner p = i then (1 : ℝ) else 0)))

/-- The output of the barycenter algorithm: the distribution, the run of the weighted
Algorithm 1 on the associated instance, and the total operation count. -/
structure BaryResult (d n : ℕ) where
  /-- The returned distribution `B`. -/
  dist : FinDist d
  /-- The run of the weighted Algorithm 1 on the associated instance. -/
  run : Alg1Result d n
  /-- Real-RAM operations outside the oracles, including the computation of `B`. -/
  arithOps : ℕ

/-- The algorithm of the proof of Theorem 4 (p.48): run the weighted Algorithm 1 on the
associated instance, obtaining `S` and `φ*_S`, and return the distribution with atoms `S` and
masses `b_s = w(s)/m = (1/m) ∑_q w(q) φ*_S(q,s)` (Lemma 43, part 1), charging `n·|S| + |S|`
operations for this step ("in `O(n|S|)` time"). -/
noncomputable def baryAlg (ρ ε : ℝ) (I : BaryInstance d n m) (hLP : FairLPOracle d n)
    (lp29 : LP29Oracle d n) (KM : KMOracle d) : BaryResult d n :=
  let R := alg1H ρ ε (assoc I) hLP lp29 KM
  { dist := { s := R.s, atoms := R.centers,
              mass := fun t => (1 / (m : ℝ)) * ∑ q, I.mass q * R.assign q t }
    run := R
    arithOps := R.arithOps + n * R.s + R.s }

end FairKMeans.Supplement


