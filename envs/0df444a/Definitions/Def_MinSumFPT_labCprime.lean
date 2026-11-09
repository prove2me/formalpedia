-- Prove2me | Definitions.Def_MinSumFPT_labCprime
-- name    : MinSumFPT_labCprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:56.949366+00:00
-- url     : https://prove2.me/theorems/f54cef32-6080-4a10-ade8-7b2e4c57f852
-- title:
--   Stage 2: the labels $h_p$, the buckets $B^h$, the capacitated assignment $f$ and the clustering $\mathcal C'$
-- statement:
--   In the setting of the Stage 2 clustering $\mathcal D$:
--
--   1. For each point $p$, $j_p$ is a cluster $j$ with $p\in C_j^{\mathrm{far}}$ minimizing $\|e_p-e_{\hat\mu_{C_j}}\|_{W_1}$, or $0$ if $p$ is far for no cluster.
--   2. The label function $h_p$ on clusters takes values in $\{0,1,\dots,k,\mathrm{cls},\mathrm{mid}_1,\mathrm{mid}_2,\dots,\mathrm{far}\}$:
--      - on a cluster $i$ with $p\in C_i^{\mathrm{cls}}$, the value is $j_p$ if $j_p=0$ or $\|e_p-e_{\hat\mu_{C_{j_p}}}\|<\beta\,\widehat{\widehat{\Delta}}_{C_i}$, and $\mathrm{cls}$ otherwise;
--      - on $i$ with $p\in C_i^{\mathrm{mid}}$, the value is $\mathrm{mid}_s$ for the least $s$ such that $p$ is $\beta^{-2}(1+\gamma)^s$-close for $C_i$;
--      - on $i$ with $p\in C_i^{\mathrm{far}}$, the value is $\mathrm{far}$.
--   3. The buckets are $B^h=\{p:h_p=h\}$, and $\hat n_{h,i}$ are $\gamma^2$-approximations of $|B^h\cap D_i|$.
--   4. The assignment costs are $d_p(j)=\infty$ if $p\in C_i^{\mathrm{cls}}\cap C_j^{\mathrm{far}}$ for some $i$ with $\widehat{|C_i|}\ge\beta^4\widehat{|C_j|}$; otherwise $d_p(j)=\widehat{|C_j|}\,\|e_p-e_{\hat\mu_{C_j}}\|_{W_1}$ if $p\in C_j^{\mathrm{far}}$, and $0$ if $p\notin C_j^{\mathrm{far}}$.
--   5. $f$ is an assignment of minimum total cost that assigns to each cluster $i$ at most $\hat n_{h,i}$ points of each bucket $B^h$.
--   6. The clustering $\mathcal C'$ sends the points of $\bigcup_i(C_i^{\mathrm{far}}\cap f^{-1}(i))$ to $f(p)$, and keeps the remaining points of $\bigcup_i(C_i^{\mathrm{far}}\cap D_i)$ with a completion $l$. The completion sends each such point to a cluster for which it is not $\beta^{-7}$-far, within the capacities. All other points keep their $\mathcal D$-label.
--
--   $\mathcal C'$ extends the partial clustering that the algorithm returns. Lemma 15 bounds its cost.
--
--   **Formalization Note** The page lists $\mathrm{mid}_1,\dots,\mathrm{mid}_R$ with $R=\lfloor5\log_{1+\gamma}(1/\beta)\rfloor$, but a middle point can need $s=R+1$. For example, at $\gamma=1$ and $\beta=1/3$, $R=7$ and $(1+\gamma)^R=128<243=\beta^{-5}$, so the printed $h_p$ is undefined for such a point. Here every $\mathrm{mid}_s$ is a label; the capacities of empty buckets impose nothing. The value $d_p(j)=\infty$ is encoded as a constraint on $f$, and an optimal $f$ minimizes the finite cost among the feasible assignments.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.4, pp.19–20 (j_p, L, h_p, B^h, d_p(j), f, F_i, D′, P′, l, 𝒞′)

import Mathlib
import Definitions.Def_MinSumFPT_labD

open scoped Classical

namespace MinSumFPT

/-!
# Stage 2: the labels h_p, the buckets B^h, the capacitated assignment f and the clustering 𝒞′

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §2.4, pp.19–20: j_p = argmin_{j : p ∈ C_j^far} ‖e_p − µ̂_{C_j}‖ (0 if no such j); the
labels L = {0, 1, …, k, cls, mid_1, …, mid_R, far}; h_p : {1, …, k} → L; B^h = {p : h_p = h};
γ²-approximate cardinalities of |B^h ∩ D_i|; the assignment costs d_p(j); an optimal assignment f
under the capacities; F_i = f⁻¹(i); D′, P′ and the completion l; the clustering 𝒞′.

This module bundles `Label`, `IsJChoice`, `midIndex`, `hLabel`, `bucket`, `IsCapEstimate`,
`Forbidden`, `assignCost`, `IsFeasibleAssign`, `IsOptimalAssign`, `labCprime` and
`IsAdmissibleCompletion`.

**Formalization Note.**
* Labels: `Label k` has `pt none` (the paper's 0), `pt (some j)` (the paper's j), `cls`, `mid s` for
  every `s : ℕ`, and `far`. The page lists mid_1, …, mid_R with R = ⌊5 log_{1+γ}(1/β)⌋, but a point
  of C_i^mid can need s = R + 1 (e.g. γ = 1, β = 1/3: R = 7, (1+γ)^R = 128 < 243 = β⁻⁵), where the
  printed h_p is undefined; here every `mid s` is a label (only realized labels matter: the
  capacities of an empty bucket are void).
* `j_p` is any choice among the minimizers (`IsJChoice`); the statements hold for every choice.
* `d_p(j) = ∞` is the constraint `¬ Forbidden p (f p)` on the assignment; `assignCost` is the finite
  part (|Ĉ_j| ⋅ ‖e_p − µ̂_{C_j}‖ on C_j^far, 0 on C_j^{¬far}). An optimal assignment minimizes the
  total finite cost among the capacity-respecting assignments of finite cost (the paper's optimum,
  since the assignment induced by 𝒟 is feasible of finite cost, p.22).
* 𝒞′ (p.20): a point of ⋃_i (C_i^far ∩ F_i) goes to `f p`; otherwise a point of ⋃_i (C_i^far ∩ D_i)
  goes to `l p`; every other point keeps its 𝒟 label. `l` is admissible if it sends each of its
  points to a cluster for which the point is not β⁻⁷-far and 𝒞′ respects every capacity n̂_{h,i}.
-/

/-- The label set of §2.4 (with every `mid s`, see the module note). -/
inductive Label (k : ℕ) : Type
  /-- `0` (as `pt none`) or a cluster index `j` (as `pt (some j)`). -/
  | pt (o : Option (Fin k))
  /-- `cls`. -/
  | cls
  /-- `mid_s`. -/
  | mid (s : ℕ)
  /-- `far`. -/
  | far

/-- `jp` is a valid choice of `j_p` for every point: `none` iff `p` is far for no cluster, and
otherwise a cluster `j` with `p ∈ C_j^far` minimizing `‖e_p − µ̂_{C_j}‖` among those. -/
def IsJChoice {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (jp : Fin n → Option (Fin k)) : Prop :=
  ∀ p, (jp p = none ↔ ∀ j, p ∉ farSet d ε γ β E j) ∧
    ∀ j, jp p = some j → p ∈ farSet d ε γ β E j ∧
      ∀ j', p ∈ farSet d ε γ β E j' →
        PerturbedWF.transNorm d (unitVec p - unitVec (E.muHat j)) ≤
          PerturbedWF.transNorm d (unitVec p - unitVec (E.muHat j'))

/-- `s = argmin {j : p is β⁻²(1+γ)^j-close for C_i}` (0 if no such `j`; used for `p ∈ C_i^mid`). -/
noncomputable def midIndex {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (i : Fin k) (p : Fin n) : ℕ :=
  if h : ∃ j : ℕ, ¬ IsFarFor d ε γ E (β⁻¹ ^ 2 * (1 + γ) ^ j) i p then Nat.find h else 0

/-- The function `h_p : {1, …, k} → L` of p.19. -/
noncomputable def hLabel {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (jp : Fin n → Option (Fin k)) (p : Fin n) : Fin k → Label k :=
  fun i =>
    if p ∈ clsSet d ε γ β E i then
      match jp p with
      | none => .pt none
      | some j =>
          if PerturbedWF.transNorm d (unitVec p - unitVec (E.muHat j)) < β * dblHat ε γ E i then
            .pt (some j)
          else .cls
    else if p ∈ farSet d ε γ β E i then .far
    else .mid (midIndex d ε γ β E i p)

/-- The bucket `B^h = {p ∈ A : h_p = h}`. -/
noncomputable def bucket {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (jp : Fin n → Option (Fin k)) (h : Fin k → Label k) : Finset (Fin n) :=
  Finset.univ.filter (fun p => hLabel d ε γ β E jp p = h)

/-- `nhat h i` γ²-approximates `|B^h ∩ D_i|` for every `h` and `i` (Definition 2 with γ² for γ). -/
def IsCapEstimate {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ g : Fin n → Fin k) (jp : Fin n → Option (Fin k)) (nhat : (Fin k → Label k) → Fin k → ℝ) :
    Prop :=
  ∀ h i, GammaApprox (γ ^ 2) (nhat h i)
    ((bucket d ε γ β E jp h ∩ clusterOf (labD d ε γ β E σ g) i).card : ℝ)

/-- `d_p(j) = ∞`: `p ∈ C_i^cls ∩ C_j^far` for some `i` with `|Ĉ_i| ≥ β⁴ |Ĉ_j|`. -/
def Forbidden {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k) (p : Fin n)
    (j : Fin k) : Prop :=
  ∃ i, p ∈ clsSet d ε γ β E i ∧ p ∈ farSet d ε γ β E j ∧ β ^ 4 * E.chat j ≤ E.chat i

/-- The finite assignment cost: `|Ĉ_j| ⋅ ‖e_p − µ̂_{C_j}‖_{W₁}` if `p ∈ C_j^far`, else `0`. -/
noncomputable def assignCost {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (p : Fin n) (j : Fin k) : ℝ :=
  if p ∈ farSet d ε γ β E j then
    E.chat j * PerturbedWF.transNorm d (unitVec p - unitVec (E.muHat j))
  else 0

/-- `f` has finite cost and assigns to each `i` at most `n̂_{h,i}` points of each bucket `B^h`. -/
def IsFeasibleAssign {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (jp : Fin n → Option (Fin k)) (nhat : (Fin k → Label k) → Fin k → ℝ) (f : Fin n → Fin k) :
    Prop :=
  (∀ p, ¬ Forbidden d ε γ β E p (f p)) ∧
    ∀ h i, (((bucket d ε γ β E jp h).filter (fun p => f p = i)).card : ℝ) ≤ nhat h i

/-- `f` is an optimal assignment: feasible, of least total cost among the feasible ones. -/
def IsOptimalAssign {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (jp : Fin n → Option (Fin k)) (nhat : (Fin k → Label k) → Fin k → ℝ) (f : Fin n → Fin k) :
    Prop :=
  IsFeasibleAssign d ε γ β E jp nhat f ∧
    ∀ f', IsFeasibleAssign d ε γ β E jp nhat f' →
      ∑ p, assignCost d ε γ β E p (f p) ≤ ∑ p, assignCost d ε γ β E p (f' p)

/-- The clustering 𝒞′ of p.20 as a labelling: `f p` on ⋃_i (C_i^far ∩ F_i); otherwise `l p` on
⋃_i (C_i^far ∩ D_i); otherwise the 𝒟 label. -/
noncomputable def labCprime {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ g f l : Fin n → Fin k) (p : Fin n) : Fin k :=
  if p ∈ farSet d ε γ β E (f p) then f p
  else if p ∈ farSet d ε γ β E (labD d ε γ β E σ g p) then l p
  else labD d ε γ β E σ g p

/-- `l` is an admissible completion: each point it places goes to a cluster for which it is not
β⁻⁷-far (a cluster in h_p⁻¹(L ∖ {far})), and 𝒞′ respects every capacity `n̂_{h,i}`. -/
def IsAdmissibleCompletion {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε γ β : ℝ) (E : Estimates n k)
    (σ g : Fin n → Fin k) (jp : Fin n → Option (Fin k)) (nhat : (Fin k → Label k) → Fin k → ℝ)
    (f l : Fin n → Fin k) : Prop :=
  (∀ p, p ∉ farSet d ε γ β E (f p) → p ∈ farSet d ε γ β E (labD d ε γ β E σ g p) →
      p ∉ farSet d ε γ β E (l p)) ∧
    ∀ h i, (((bucket d ε γ β E jp h).filter
      (fun p => labCprime d ε γ β E σ g f l p = i)).card : ℝ) ≤ nhat h i

end MinSumFPT


