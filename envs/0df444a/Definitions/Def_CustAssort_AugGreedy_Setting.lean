-- Prove2me | Definitions.Def_CustAssort_AugGreedy_Setting
-- name    : CustAssort_AugGreedy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:15.092759+00:00
-- url     : https://prove2.me/theorems/26f865e8-c751-4921-9e40-43d547c9ea89
-- title:
--   §2, §4.1, Definition 4.1, pp. 5–11, 43 — MNL revenue, f_j, f^C, z_CAP, CAP optimality, Augmented Greedy runs, S*_j, complete types
-- statement:
--   There are products $\mathcal N=\{1,\ldots,n\}$ and customer types $\mathcal M=\{1,\ldots,m\}$. Product $i$ earns revenue $r_i$, customer type $j$ attaches preference weight $v_{ij}$ to product $i$, and the no-purchase option has weight one. A type-$j$ customer offered the assortment $T$ yields the MNL expected revenue
--   $$
--   \operatorname{Rev}_j(T)=\frac{\sum_{i\in T} r_i v_{ij}}{1+\sum_{i\in T} v_{ij}} .
--   $$
--   When the firm carries the products $S$, the best revenue it can earn from type $j$ by personalizing the offer is
--   $$
--   f_j(S)=\max_{T\subseteq S}\operatorname{Rev}_j(T).
--   $$
--   For a set of types $\mathcal C\subseteq\mathcal M$ with arrival probabilities $\theta_j$, write $f^{\mathcal C}(S)=\sum_{j\in\mathcal C}\theta_j f_j(S)$. The Customized Assortment Problem is
--   $$
--   z_{\mathsf{CAP}}=\max_{S\subseteq\mathcal N,\ |S|\le K} f^{\mathcal M}(S),
--   $$
--   and $S^*$ is an optimal solution of CAP when $|S^*|\le K$ and $f^{\mathcal M}(S)\le f^{\mathcal M}(S^*)$ for every $S$ with $|S|\le K$.
--
--   The module also records the objects of Augmented Greedy (§4.1). For each $i$, $\mathcal V_i=\{1,\ldots,i\}$; Greedy is run on $\mathcal V_i$ with cardinality $k$ and the objective $S\mapsto\sum_{j\in\mathcal C}\theta_j\min(f_j(S),r_i)$, producing $\Delta_i$; an output of Augmented Greedy is any $\Delta_i$ that maximizes $f^{\mathcal C}$ over the $n$ candidates. Every legal Greedy run and every tie-break is allowed. Finally, $S_j^*=\{i\in S^*: r_i\ge f_j(S^*)\}$ is the optimal assortment offered to type $j$ from $S^*$, and the types complete with respect to $\mathcal P\subseteq\mathcal N$ (Definition 4.1) are
--   $$
--   \mathcal C_{\mathcal P}=\{j\in\mathcal C:\ \mathcal P\cap S_j^*=\mathcal P\cap S^*\}.
--   $$
--
--   These are the objects shared by the series' two missions: the bound $z_{\mathsf{CAP}}\le m\, z_{\mathsf{MMNL}}$ and its tightness use $\operatorname{Rev}_j$, $f_j$, $f^{\mathcal C}$ and CAP optimality; the Augmented Greedy guarantee (Theorem 4.2) uses all of them.
--
--   **Formalization Note** Products and types are `Fin n` and `Fin m`, indexed from $0$: Lean index $i$ is the paper's $i+1$, so `Vset i` is the paper's $\mathcal V_{i+1}$ and the truncation level is $r_{i+1}$. $\operatorname{Rev}_j$ is the published `ChoiceCDLP.MNL.mnlObjective` with no-purchase weight $1$. Maxima are finite `Finset.sup'` over nonempty families (every powerset, and the size-$\le K$ family, which contains $\varnothing$). $S_j^*$ is the threshold set: the paper defines $S_j^*$ only as "the optimal assortment" (p. 11) and identifies it with $\{i\in S^*:r_i\ge f_j(S^*)\}$ on p. 43 via Lemma E.1. The standing assumptions of §2 ($r_1\ge\cdots\ge r_n>0$, $v_{ij}\ge0$, $\theta_j\ge0$, $\sum_j\theta_j=1$) are hypotheses of the theorems that use these definitions, not part of the definitions. With $n=0$ there is no Augmented Greedy output, as in the paper, where the algorithm needs $n\ge1$.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082, https://ssrn.com/abstract=3830082 (version of December 7, 2021), pp. 5–6, §2 and (CAP); p. 9, f^C and footnote 1; p. 10, Greedy and Augmented Greedy; p. 11, Definition 4.1; p. 39, Lemma E.1; p. 43, S*_j = {i ∈ S* : r_i ≥ f_j(S*)}

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_CustAssort_AugGreedy_SubmodularOn
import Definitions.Def_CustAssort_AugGreedy_Greedy

namespace CustAssort.AugGreedy

/-- The MNL expected revenue for type `j`, with no-purchase weight one (§2, p. 6). -/
noncomputable def rev {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (S : Finset (Fin n)) : ℝ :=
  ChoiceCDLP.MNL.mnlObjective (fun i => v i j) r 1 S

/-- Best personalized revenue from type `j` when only products in `S` are available (§2, p. 6). -/
noncomputable def fj {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (S : Finset (Fin n)) : ℝ :=
  S.powerset.sup' (Finset.powerset_nonempty S) (rev v r j)

/-- Revenue contributed by a subset of customer types (§4, p. 9). -/
noncomputable def fC {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (C : Finset (Fin m)) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ C, θ j * fj v r j S

/-- The CAP objective value, maximizing over every assortment of at most `K` products (§2, p. 6). -/
noncomputable def zCAP {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (K : ℕ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ K)).sup'
    (by refine ⟨∅, ?_⟩; simp) (fC θ v r Finset.univ)

/-- `Sstar` is an optimal first-stage assortment for CAP (§2, pp. 5–6). -/
def IsCAPOpt {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (K : ℕ) (Sstar : Finset (Fin n)) : Prop :=
  Sstar.card ≤ K ∧ ∀ S : Finset (Fin n), S.card ≤ K →
    fC θ v r Finset.univ S ≤ fC θ v r Finset.univ Sstar

/-- The products at or before index `i`, the paper's `V_{i+1}` (§4.1, p. 10). -/
def Vset {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => p ≤ i)

/-- Objective of Greedy in iteration `i` of Augmented Greedy (§4.1, p. 10). -/
noncomputable def truncObj {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (C : Finset (Fin m)) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ C, θ j * min (fj v r j S) (r i)

/-- Every iteration uses a legal Greedy run; the output maximizes `fC` among its candidates (§4.1, p. 10). -/
def IsAugGreedyOutput {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (C : Finset (Fin m)) (k : ℕ) (Δ : Finset (Fin n)) : Prop :=
  ∃ Δs : Fin n → Finset (Fin n),
    (∀ i, IsGreedyOutput (truncObj θ v r C i) (Vset i) k (Δs i)) ∧
    ∃ i, Δ = Δs i ∧ ∀ i', fC θ v r C (Δs i') ≤ fC θ v r C (Δs i)

/-- The threshold optimal personalized assortment from `Sstar` (Lemma E.1, p. 39). -/
noncomputable def SstarJ {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (Sstar : Finset (Fin n)) (j : Fin m) : Finset (Fin n) :=
  Sstar.filter (fun i => fj v r j Sstar ≤ r i)

/-- Types complete relative to `P` for the threshold optimal sub-assortments (Definition 4.1, p. 11). -/
noncomputable def completeTypes {n m : ℕ} (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (Sstar : Finset (Fin n)) (C : Finset (Fin m))
    (P : Finset (Fin n)) : Finset (Fin m) :=
  C.filter (fun j => P ∩ SstarJ v r Sstar j = P ∩ Sstar)

end CustAssort.AugGreedy


