-- Prove2me | Definitions.Def_CustAssort_Value_Setting
-- name    : CustAssort_Value_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:22.954887+00:00
-- url     : https://prove2.me/theorems/d0261de1-57c9-4c83-a1b0-152b79466c49
-- title:
--   §2–3, pp. 5–8 — CAP, MMNL, and the tightness instance
-- statement:
--   Let $N$ be a finite set of products and $M$ a finite set of customer types. Product $i$ has revenue $r_i>0$, type $j$ has arrival probability $\theta_j$, and its preference weight for product $i$ is $v_{ij}\ge 0$. The no-purchase weight is one. For an offered assortment $S$, the **MNL expected revenue** for type $j$ is
--
--   $$\operatorname{Rev}_j(S)=\frac{\sum_{i\in S}r_i v_{ij}}{1+\sum_{i\in S}v_{ij}}.$$
--
--   The **personalized value** $f_j(S)$ maximizes $\operatorname{Rev}_j(T)$ over $T\subseteq S$. For a set of types $C$, let $f^C(S)=\sum_{j\in C}\theta_j f_j(S)$. With a first-stage budget $K$, the **customized assortment problem** and its **mixed multinomial logit** counterpart have values
--
--   $$z_{\rm CAP}=\max_{S\subseteq N,\ |S|\le K} f^M(S),\qquad z_{\rm MMNL}=\max_{S\subseteq N,\ |S|\le K}\sum_{j\in M}\theta_j\operatorname{Rev}_j(S).$$
--
--   The shared setting records when $S^*$ is a CAP optimum; this definition records the instance used to show tightness in Theorem 3.1. For that instance $n=m=K$, $\alpha=(\sum_{j=1}^m a^{-j})^{-1}$, $\theta_j=\alpha a^{-j}$, $r_i=a^i$, and $v_{ij}=b^{m-i+1}$ if $i\le j$, zero otherwise. The proof chooses $b=m-1$ and $a=2m(m-1)^m$. Its equation (3.1) separates each weighted type revenue into earlier-product and diagonal-product terms.
--
--   These definitions fix the optimization domains and the explicit witness family reused by the theorem statements.
--
--   **Formalization Note** Products and types use 0-based `Fin` indices. Both maxima are `Finset.sup'` over the nonempty finite family $|S|\le K$; the empty assortment is feasible even at $K=0$. `rev` imports the published MNL objective with no-purchase weight one.
-- source:
--   El Housni & Topaloglu, Joint Assortment Optimization and Customization under a Mixture of Multinomial Logit Models: Value of Personalized Assortments, SSRN 3830082 (version of December 7, 2021), pp. 5–8, §2, (CAP), (MMNL), proof of Theorem 3.1, (3.1)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_CustAssort_AugGreedy_Setting

namespace CustAssort.Value

/-- All first-stage assortments of size at most `K`. -/
def feasible (n K : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S.card ≤ K)

/-- The empty assortment is feasible, including when `K = 0`. -/
theorem feasible_nonempty (n K : ℕ) : (feasible n K).Nonempty :=
  ⟨∅, by simp [feasible]⟩

/-- CAP optimum: a finite maximum over feasible first-stage assortments. -/
noncomputable def zCAP {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (K : ℕ) : ℝ :=
  (feasible n K).sup' (feasible_nonempty n K) (CustAssort.AugGreedy.fC θ v r Finset.univ)

/-- MMNL optimum: one common assortment is offered to every type. -/
noncomputable def zMMNL {n m : ℕ} (θ : Fin m → ℝ) (v : Fin n → Fin m → ℝ)
    (r : Fin n → ℝ) (K : ℕ) : ℝ :=
  (feasible n K).sup' (feasible_nonempty n K)
    (fun S => ∑ j : Fin m, θ j * CustAssort.AugGreedy.rev v r j S)

/-- The normalizing constant of the tightness instance on page 8. -/
noncomputable def alpha (a : ℝ) (m : ℕ) : ℝ :=
  (∑ j : Fin m, 1 / a ^ (j.val + 1))⁻¹

/-- Arrival probability of type `j` in the tightness instance. -/
noncomputable def thetaI (a : ℝ) (m : ℕ) (j : Fin m) : ℝ :=
  alpha a m / a ^ (j.val + 1)

/-- Revenue of product `i` in the tightness instance. -/
def revI (a : ℝ) (m : ℕ) (i : Fin m) : ℝ :=
  a ^ (i.val + 1)

/-- Preference weight of product `i` for type `j` in the tightness instance. -/
def vI (b : ℝ) (m : ℕ) (i j : Fin m) : ℝ :=
  if i ≤ j then b ^ (m - i.val) else 0

/-- The parameter `b = m - 1` chosen in the proof of Theorem 3.1. -/
def bStar (m : ℕ) : ℝ := (m : ℝ) - 1

/-- The parameter `a = 2m(m - 1)^m` chosen in the proof of Theorem 3.1. -/
def aStar (m : ℕ) : ℝ := 2 * (m : ℝ) * ((m : ℝ) - 1) ^ m

/-- The first (earlier-product) term on the right of equation (3.1). -/
noncomputable def firstTerm {m : ℕ} (a b : ℝ) (S : Finset (Fin m)) (j : Fin m) : ℝ :=
  thetaI a m j *
    (∑ i ∈ S, if i < j then revI a m i * b ^ (m - i.val) else 0) /
      (1 + ∑ i ∈ S, vI b m i j)

/-- The second (diagonal-product) term on the right of equation (3.1). -/
noncomputable def secondTerm {m : ℕ} (a b : ℝ) (S : Finset (Fin m)) (j : Fin m) : ℝ :=
  alpha a m * (if j ∈ S then (b ^ (m - j.val) : ℝ) else 0) /
    (1 + ∑ i ∈ S, vI b m i j)

end CustAssort.Value


