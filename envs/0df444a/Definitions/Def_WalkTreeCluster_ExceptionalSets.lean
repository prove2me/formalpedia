-- Prove2me | Definitions.Def_WalkTreeCluster_ExceptionalSets
-- name    : WalkTreeCluster_ExceptionalSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:56:42.446716+00:00
-- url     : https://prove2.me/theorems/9073f156-871c-44c0-8134-94ed125ffcb2
-- title:
--   $k_i(C)$, the stage $i_C$, and the exceptional sets $B_{\rm clusters}$, $B_{\rm noise}$, $B$ (Definitions 8.2, 8.8, 9.5)
-- statement:
--   For a cluster $C$:
--   1. $k_i(C)=\frac1{|C|}\sum_{u\in C}\mathbb E[\mathrm{Keep}(u,i)]$ (Definition 8.2);
--   2. $i_C=\max\{1,\lfloor\log_\alpha(a^{10}|C|)\rfloor\}$ (Lemma 8.1).
--
--   $B_{\rm clusters}\subseteq S$ consists of the vertices $u\in C\in\mathcal C$ with (Definition 8.8)
--   $$\sum_{i\ge1}\alpha^{2i}\,\|F_i\mathbb 1_u-F_iu_C\|_{F,w}^4>a^{40}.$$
--   With $J_C=\{1\}\cup\{2\le j\le H:\ a^{10}/(16\alpha)\le\alpha^j/|C|<a^{10}\}$, $B_{\rm noise}\subseteq V\setminus S$ consists of the vertices $v$ with
--   $$|\langle F_ju_C,F_j\mathbb 1_v\rangle_w|\ge\frac1{4|C|}\quad\text{for some }C\in\mathcal C,\ j\in J_C,$$
--   and $B=B_{\rm clusters}\cup B_{\rm noise}$ (Definition 9.5).
--
--   $B$ is the set of vertices the classifier may misclassify.
--
--   **Formalization Note.** The series of Definition 8.8 has nonnegative terms and is summed in $[0,\infty]$.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Definition 8.2, p.47; Lemma 8.1, p.46; Definition 8.8, p.58; Definition 9.5, p.65

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter

open scoped Classical

namespace WalkTreeCluster

/-!
# Exceptional sets, the cluster stage `i_C` and the average keep output `k_i(C)`

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Definition 8.2, Eq. (70), p.47; Lemma 8.1 (`i_C`), p.46;
Definition 8.8, p.58; Definition 9.5, p.65.

* `k_i(C) = |C|⁻¹ Σ_{u ∈ C} E[Keep(u, i)]` (Definition 8.2).
* `i_C = max{1, ⌊log_α(a^{10}|C|)⌋}` (Lemma 8.1).
* `B_clusters ⊆ S`: the vertices `u ∈ C ∈ 𝒞` with `Σ_{i ≥ 1} α^{2i} ‖F_i 1_u − F_i u_C‖⁴_{F,w} > a^{40}`
  (Definition 8.8).
* `J_C = {1} ∪ {2 ≤ j ≤ H : a^{10}/(16α) ≤ α^j/|C| < a^{10}}`, `B_noise ⊆ V ∖ S`: the vertices `v`
  with `|⟨F_j u_C, F_j 1_v⟩_w| ≥ 1/(4|C|)` for some `C ∈ 𝒞` and `j ∈ J_C`; `B = B_clusters ∪ B_noise`
  (Definition 9.5).

**Formalization Note.**
* The series of Definition 8.8 has nonnegative terms and is summed in `ℝ≥0∞`, so it is never a
  default value; `‖X‖⁴_{F,w}` is `(wNormSq X)²`.
* `i_C` is an integer floor of a real that may be negative, taken as a natural number after the
  maximum with `1`. `H` depends on `n`.
-/

/-- `k_i(C) = |C|⁻¹ Σ_{u ∈ C} E[Keep(u, i)]`, Definition 8.2. -/
noncomputable def keepAvg {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ)
    (C : Finset (Fin n)) : ℝ :=
  (1 / (C.card : ℝ)) * ∑ u ∈ C, meanKeep nbr ϵ ϕ i u

/-- `i_C = max{1, ⌊log_α(a^{10}|C|)⌋}`, Lemma 8.1. -/
noncomputable def clusterStage (ϵ ϕ : ℝ) {n : ℕ} (C : Finset (Fin n)) : ℕ :=
  (max 1 ⌊Real.logb (alphaParam ϵ ϕ) (aParam ϵ ϕ ^ 10 * (C.card : ℝ))⌋).toNat

/-- `Σ_{i ≥ 1} α^{2i} ‖F_i 1_u − F_i u_C‖⁴_{F,w}` in `ℝ≥0∞`. -/
noncomputable def deviationSum {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (C : Finset (Fin n)) (u : Fin n) : ENNReal :=
  ∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * (i + 1)) *
    (wNormSq (aParam ϵ ϕ)
      (filter nbr ϵ ϕ (i + 1) (coord u) - filter nbr ϵ ϕ (i + 1) (clusterMean C))) ^ 2)

/-- `B_clusters`, Definition 8.8. -/
noncomputable def Bclusters {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun u =>
    ∃ C ∈ 𝒞, u ∈ C ∧ ENNReal.ofReal (aParam ϵ ϕ ^ 40) < deviationSum nbr ϵ ϕ C u)

/-- `J_C`, Definition 9.5. -/
noncomputable def stageSet (ϵ ϕ : ℝ) (n : ℕ) (C : Finset (Fin n)) : Finset ℕ :=
  {1} ∪ (Finset.Icc 2 (HParam ϵ ϕ n)).filter (fun j =>
    aParam ϵ ϕ ^ 10 / (16 * alphaParam ϵ ϕ) ≤ alphaParam ϵ ϕ ^ j / (C.card : ℝ) ∧
      alphaParam ϵ ϕ ^ j / (C.card : ℝ) < aParam ϵ ϕ ^ 10)

/-- `B_noise`, Definition 9.5. -/
noncomputable def Bnoise {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∉ clusterUnion 𝒞 ∧
    ∃ C ∈ 𝒞, ∃ j ∈ stageSet ϵ ϕ n C,
      1 / (4 * (C.card : ℝ)) ≤
        |wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ j (clusterMean C)) (filter nbr ϵ ϕ j (coord v))|)

/-- `B = B_clusters ∪ B_noise`, Definition 9.5. -/
noncomputable def Bexc {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Bclusters nbr ϵ ϕ 𝒞 ∪ Bnoise nbr ϵ ϕ 𝒞

end WalkTreeCluster


