-- Prove2me | Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Tolerant
-- name    : FullyDynamicCorrelation_VertexUpdates_Tolerant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:50:14.818935+00:00
-- url     : https://prove2.me/theorems/ea8aa32c-4f17-474c-a281-257de23c2181
-- title:
--   Definition 6: partially correct tolerant sparse-dense decomposition
-- statement:
--   Definition 6 (p. 20) with the degree levels of Table 1 (p. 19), for a vertex bound $n$ and a singleton set $S$.
--
--   - **Level $i$** (`bucket`): the vertices of $S$ with $\deg(v)\in[2^i,2^{i+1})$ for $i=0,\dots,\lfloor\log_2 n\rfloor$; every other integer index, in particular every negative one, is an empty bucket.
--   - **Correct / incorrect** (`correctAt`, `incorrectAt`): the $\varepsilon_s$-sparse vertices of a level and the rest of it; `correctWindow3` is the union over levels $i-1,i,i+1$; `correctDegMass` is the total degree of the correct vertices of all levels.
--   - **Singleton condition** (`SingletonCondition`): for each level $i\le\lfloor\log_2n\rfloor$, either $\bigl|\bigcup_{j\in\{i-1,i,i+1\}}\mathrm{correct}(j)\bigr|\ge\frac1{100}|S(i)|$, or $\sum_{v\in\mathrm{incorrect}(i)}\deg v\le\frac{1}{C_0\log_2 n}\sum_j\sum_{v\in\mathrm{correct}(j)}\deg v$.
--   - **$K_v$** (`agreeSet θ v`): the vertices of $N[v]$ in $\theta$-agreement with $v$, $v$ included.
--   - **Tolerant cluster** (`IsTolerant S ετ Ct ηd K`): $K=\{v\}$ with $N(v)=\emptyset$, or every $v\in K$ has at most $\varepsilon_\tau|K|$ non-neighbours in $K$ other than itself and is $\eta_d\varepsilon_\tau$-sparse or has at least an $\varepsilon_\tau$-fraction of $K_v\setminus K$ in $S$ ($K_v$ with parameter $C_t\varepsilon_\tau$).
--   - **Isolated cluster** (`IsIsolated`): not tolerant, and every $v\in K$ is $\eta_l\varepsilon_l$-sparse with $\deg v\ge|K|/2$, or has an $\varepsilon_l$-fraction of $K_v\setminus K$ in $S$ and $|K_v\setminus K|\ge\varepsilon_l|K|$ ($K_v$ with parameter $C_l\varepsilon_l$).
--   - **Decomposition** (`IsPCTD`): $S$, the tolerant clusters $T$ and the isolated clusters $I$ partition $V$ (`IsPartition`: nonempty, pairwise disjoint, covering), with the singleton condition and the two cluster conditions. `decompRel T I` is the clustering of Theorem 2: each cluster of $T\cup I$ together, every other vertex alone.
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Definition 6 (p. 20), Table 1 (p. 19)

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Graph

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-!
# Definition 6: partially correct tolerant sparse-dense decomposition

Braverman et al. (2026), supplied manuscript sha256 07ee1c8f…aab2, Definition 6 (p. 20),
with the degree levels of Table 1 (p. 19).

`n` is the known upper bound on the number of vertices; `log n` is `lg n = log₂ n`.
-/

namespace SGraph

variable (H : SGraph)

/-- Degree level `i` of a vertex set `S` (Definition 6 i): the vertices of `S` with
`deg(v) ∈ [2^i, 2^{i+1})`, for `i = 0, …, ⌊log₂ n⌋`; every other integer index (in particular
every negative one) denotes an empty bucket. -/
noncomputable def bucket (n : ℕ) (S : Finset ℕ) (i : ℤ) : Finset ℕ :=
  if 0 ≤ i ∧ i ≤ (Nat.log 2 n : ℤ) then
    S.filter (fun v => 2 ^ i.toNat ≤ H.deg v ∧ H.deg v < 2 ^ (i.toNat + 1))
  else ∅

/-- `Ṽ_{singleton, correct}(i)`: the `θ`-sparse vertices of level `i`. -/
noncomputable def correctAt (n : ℕ) (θ : ℝ) (S : Finset ℕ) (i : ℤ) : Finset ℕ :=
  (H.bucket n S i).filter (fun v => H.Sparse θ v)

/-- `Ṽ_{singleton, incorrect}(i) = Ṽ_{singleton}(i) \ Ṽ_{singleton, correct}(i)`. -/
noncomputable def incorrectAt (n : ℕ) (θ : ℝ) (S : Finset ℕ) (i : ℤ) : Finset ℕ :=
  H.bucket n S i \ H.correctAt n θ S i

/-- Union of the correct parts of the three levels `i − 1, i, i + 1` (`S_i(3)`). -/
noncomputable def correctWindow3 (n : ℕ) (θ : ℝ) (S : Finset ℕ) (i : ℤ) : Finset ℕ :=
  H.correctAt n θ S (i - 1) ∪ H.correctAt n θ S i ∪ H.correctAt n θ S (i + 1)

/-- Total degree of the correct singleton vertices over all levels `0, …, ⌊log₂ n⌋`. -/
noncomputable def correctDegMass (n : ℕ) (θ : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 n + 1), ∑ v ∈ H.correctAt n θ S (j : ℤ), (H.deg v : ℝ)

/-- Definition 6, singleton conditions iii): for each level `i = 0, …, ⌊log₂ n⌋`, either the
correct vertices of levels `i − 1, i, i + 1` number at least `|Ṽ_singleton(i)| / 100`, or the
incorrect vertices of level `i` have total degree at most `1/(C₀ log n)` times the total degree
of all correct singleton vertices. -/
def SingletonCondition (n : ℕ) (εs C0 : ℝ) (S : Finset ℕ) : Prop :=
  ∀ i : ℕ, i ≤ Nat.log 2 n →
    (1 / 100 : ℝ) * ((H.bucket n S i).card : ℝ) ≤ ((H.correctWindow3 n εs S i).card : ℝ) ∨
    ∑ v ∈ H.incorrectAt n εs S i, (H.deg v : ℝ) ≤
      1 / (C0 * lg n) * H.correctDegMass n εs S

/-- `K_v`: the vertices of `N[v]` in `θ`-agreement with `v`, including `v` itself. -/
noncomputable def agreeSet (θ : ℝ) (v : ℕ) : Finset ℕ :=
  (H.cnbr v).filter (fun u => H.Agree θ u v)

/-- Definition 6, tolerant cluster with parameter `ετ` and constants `Ct, ηd`, relative to the
singleton set `S`: either `K = {v}` with `N(v) = ∅`, or every `v ∈ K` has at most `ετ|K|`
non-neighbours inside `K` (not counting `v`) and is `ηd ετ`-sparse or has at least an
`ετ`-fraction of `K_v \ K` in `S` (`K_v` taken with agreement parameter `Ct ετ`). -/
def IsTolerant (S : Finset ℕ) (ετ Ct ηd : ℝ) (K : Finset ℕ) : Prop :=
  (∃ v, K = {v} ∧ H.deg v = 0) ∨
    ∀ v ∈ K,
      (((K \ H.cnbr v).card : ℕ) : ℝ) ≤ ετ * (K.card : ℝ) ∧
      (H.Sparse (ηd * ετ) v ∨
        ετ * (((H.agreeSet (Ct * ετ) v \ K).card : ℕ) : ℝ) ≤
          ((((H.agreeSet (Ct * ετ) v \ K) ∩ S).card : ℕ) : ℝ))

/-- Definition 6, isolated cluster: not a tolerant cluster, and every `v ∈ K` is `ηl εl`-sparse
with `deg(v) ≥ |K|/2`, or has at least an `εl`-fraction of `K_v \ K` in `S` together with
`|K_v \ K| ≥ εl |K|` (`K_v` taken with agreement parameter `Cl εl`). -/
def IsIsolated (S : Finset ℕ) (ετ Ct ηd εl Cl ηl : ℝ) (K : Finset ℕ) : Prop :=
  ¬ H.IsTolerant S ετ Ct ηd K ∧
    ∀ v ∈ K,
      (H.Sparse (ηl * εl) v ∧ (K.card : ℝ) / 2 ≤ (H.deg v : ℝ)) ∨
      (εl * (((H.agreeSet (Cl * εl) v \ K).card : ℕ) : ℝ) ≤
          ((((H.agreeSet (Cl * εl) v \ K) ∩ S).card : ℕ) : ℝ) ∧
        εl * (K.card : ℝ) ≤ (((H.agreeSet (Cl * εl) v \ K).card : ℕ) : ℝ))

/-- `{S, T, I}` partitions `V`: the clusters in `T ∪ I` are nonempty subsets of `V`, pairwise
disjoint and disjoint from `S`, and together with `S` they cover `V`. -/
def IsPartition (S : Finset ℕ) (T I : Finset (Finset ℕ)) : Prop :=
  S ⊆ H.V ∧ Disjoint T I ∧
    (∀ K ∈ T ∪ I, K.Nonempty ∧ K ⊆ H.V ∧ Disjoint S K) ∧
    (∀ K ∈ T ∪ I, ∀ K' ∈ T ∪ I, K ≠ K' → Disjoint K K') ∧
    (∀ v ∈ H.V, v ∈ S ∨ ∃ K ∈ T ∪ I, v ∈ K)

/-- Definition 6 (p. 20): `{S, T, I}` is a partially correct tolerant `(εs, ετ, εl)`
sparse-dense decomposition with constants `Ct, Cl, ηd, ηl, C₀`, for the vertex bound `n`. -/
def IsPCTD (n : ℕ) (εs ετ εl Ct Cl ηd ηl C0 : ℝ)
    (S : Finset ℕ) (T I : Finset (Finset ℕ)) : Prop :=
  H.IsPartition S T I ∧ H.SingletonCondition n εs C0 S ∧
    (∀ K ∈ T, H.IsTolerant S ετ Ct ηd K) ∧
    (∀ K ∈ I, H.IsIsolated S ετ Ct ηd εl Cl ηl K)

end SGraph

/-- The clustering of Theorem 2: every cluster of `T ∪ I` is one cluster and every other
vertex is a singleton cluster. -/
def decompRel (T I : Finset (Finset ℕ)) (u v : ℕ) : Prop :=
  u = v ∨ ∃ K ∈ T ∪ I, u ∈ K ∧ v ∈ K

end FullyDynamicCorrelation.VertexUpdates


