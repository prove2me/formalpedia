-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_lowCrossing
-- name    : DenseLanguageGeneration_PatientScope_Supplement_lowCrossing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:59:33.067474+00:00
-- url     : https://prove2.me/theorems/ce9df30c-4ddc-4480-8603-0d4123b65e18
-- title:
--   Balanced finite partitions and crossing numbers
-- statement:
--   Let $s,m$ be positive integers with $s\mid m$. A balanced partition of $[m]=\{1,\ldots,m\}$ is a list of $m/s$ groups $G_1,\ldots,G_{m/s}$, each containing exactly $s$ elements, pairwise disjoint and covering $[m]$. For a permutation $\sigma$ read as a sequence, $[n]_\sigma$ is its first $n$ entries. Define
--
--   $$\operatorname{Crossed}(S,G)\ \Longleftrightarrow\ G\cap S\ne\varnothing\ \text{ and }\ G\setminus S\ne\varnothing,\qquad
--   c_\sigma(n)=\bigl|\{j:G_j\text{ is crossed by }([n]_\sigma,[m]\setminus[n]_\sigma)\}\bigr|.$$
--
--   The crossing number counts groups, without multiplicity from their elements. The balanced partition is the published QCollLB bucket-map object: a total label map whose fibres all have cardinality s. Coverage and disjointness follow from being fibres. Only the permutation prefixes, crossing predicate and crossing count are introduced here, with no crossing estimate in the partition predicate.
--
--   **Formalization Note** Elements and group labels use zero-based finite types; adding one recovers the source labels. For arbitrary raw parameters the group count is natural division; Theorem 2.5 restricts to positive divisible parameters. Prefixes are empty at $n=0$ and equal the whole ground set at $n\ge m$.
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), §2.1, low-crossing partitions and Theorem 2.5, printed p.9 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_QCollLB_Buckets

set_option autoImplicit false
noncomputable section

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- §2.1 (printed p.9 / PDF p.11). The ground set [m] = {1,...,m} is encoded as
`Fin m`, element j standing for the paper's j+1. A permutation σ of [m] is read as
a sequence (σ(j) is the j-th element), so the prefix [n]_σ = {σ(1),...,σ(n)} is
the image under σ of the first n positions. Empty at n = 0, all of [m] for n ≥ m. -/
def permPrefix {m : ℕ} (σ : Equiv.Perm (Fin m)) (n : ℕ) : Finset (Fin m) := by
  classical
  exact (Finset.univ.filter (fun j : Fin m => j.val < n)).image σ

/-- §2.1: the set G is crossed by the cut (S, [m] \ S) iff it meets both sides. -/
def CrossedBy {m : ℕ} (S G : Finset (Fin m)) : Prop :=
  (G ∩ S).Nonempty ∧ (G \ S).Nonempty

/-- §2.1: the crossing number c_σ(n), the number of groups crossed by the cut
([n]_σ, [m] \ [n]_σ). The groups are the fibres of the published
QCollLB bucket map; IsBucketMap s asserts that every fibre has size s. -/
def crossingNumber {m s : ℕ} (b : Fin m → Fin (m / s))
    (σ : Equiv.Perm (Fin m)) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun g => CrossedBy (permPrefix σ n) (QCollLB.bucket b g))).card

end DenseLanguageGeneration.PatientScope.Supplement


