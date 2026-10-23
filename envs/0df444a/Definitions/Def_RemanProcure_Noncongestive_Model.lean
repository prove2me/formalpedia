-- Prove2me | Definitions.Def_RemanProcure_Noncongestive_Model
-- name    : RemanProcure_Noncongestive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:36.445668+00:00
-- url     : https://prove2.me/theorems/2810fecf-4050-4b95-9b6c-e8ee2157148f
-- title:
--   §2–§3, pp. 1443–1445 — core acquisition MDP: parameters, standing assumptions, operators T1, T2, T (eq. (1)), v*, acquisition gap, levels S*_i, property set V^A (A.1)–(A.6)
-- statement:
--   This file fixes the core acquisition model of Nadar, Akan, Debo and Scheller-Wolf (§2) and the objects of §3.
--
--   **Model.** A remanufacturer acquires used items (cores) one at a time. An acquired core is inspected and falls into one of $K$ quality types $i=1,\dots,K$, type 1 being the best, with probability $p_i$. Remanufacturing a type $i$ core costs $r_i$, with $r_1\le r_2\le\dots\le r_K$; holding a type $i$ core costs $h_i>0$ per unit time, with $h_1\ge h_2\ge\dots\ge h_K$. Each acquisition costs $c_A$; acquisition lead times are exponential with rate $\mu$; demand arrives at Poisson rate $\lambda$, and an unmet demand costs $c_L>r_K$. Time is scaled so that $\alpha+\lambda+\mu=1$, where $\alpha\in(0,1)$ is the discount parameter. The state $x=(x_1,\dots,x_K)\in\mathbb N_0^K$ counts the available cores of each type, $e_i$ is the $i$-th unit vector, and $h(x)=\sum_i h_i x_i$.
--
--   **Operators.** For $v:\mathbb N_0^K\to\mathbb R$,
--   $$T_1v(x)=\min\Big\{v(x),\ c_A+\sum_{1\le i\le K}p_i\,v(x+e_i)\Big\},\qquad T_2v(x)=\min\Big\{v(x)+c_L,\ \min_{1\le i\le K,\ x_i>0}\{v(x-e_i)+r_i\}\Big\},$$
--   $$Tv(x)=\mu T_1v(x)+\lambda T_2v(x)+h(x).$$
--
--   **Optimal cost.** $v^*(x)$ is the limit of value iteration $T^n0(x)$ as $n\to\infty$, started from the zero function.
--
--   **Acquisition.** The acquisition gap is $\Delta(x)=c_A+\sum_i p_i v^*(x+e_i)-v^*(x)$, and it is optimal to acquire in $x$ when $\Delta(x)\le 0$. The acquire-up-to level of type $i$ is
--   $$S^*_i(x_{-i})=\min\{n\in\mathbb N_0:\ \text{acquiring is not optimal in the state } x \text{ with } x_i \text{ replaced by } n\}\in\mathbb N_0\cup\{\infty\},$$
--   with $\min\emptyset=\infty$; it depends on $x$ only through $x_{-i}$.
--
--   **The set $\mathcal V^A$.** For type indices $d\le l\le q\le w$, a function $g$ belongs to $\mathcal V^A$ when it satisfies
--   1. (A.1) $g(x+e_w)+c_L\ge g(x)+r_w$ for all $w$;
--   2. (A.2) $g(x+e_q)+r_w\ge g(x+e_w)+r_q$ for $q<w$;
--   3. (A.3) $g(x+e_q+e_l)-g(x+e_q+e_d)\ge g(x+e_l)-g(x+e_d)$ for $d\le l\le q$;
--   4. (A.4) $g(x+e_q+e_l)-g(x+e_q+e_d)\ge g(x+e_w+e_l)-g(x+e_w+e_d)$ for $d\le l\le q\le w$;
--   5. (A.5) $\sum_{i\le l}p_i g(x+e_q+e_l)+\sum_{l<i\le K}p_i g(x+e_q+e_i)-g(x+e_q)\ge\sum_{i\le l}p_i g(x+e_l)+\sum_{l<i\le K}p_i g(x+e_i)-g(x)$ for $l\le q$;
--   6. (A.6) the left-hand side of (A.5) at $q$ is at least the same expression at $w$, for $l\le q<w$.
--
--   As printed, the first sum in (A.5) and (A.6) has the summand $g(\cdot+e_l)$ for every $i\le l$.
--
--   These objects are shared by every statement of the mission: equation (1), Lemma 1, the two claims drawn from (A.5) and (A.6), and Theorem 1.
--
--   **Formalization Note** Types are indexed by `Fin K`; index $0$ is the paper's type 1. The demand rate $\lambda$ is the field `lam` (a Lean keyword). `T2` is a fold of `min` in which unavailable types contribute the rejection value $v(x)+c_L$, so it equals the paper's expression also when $x=0$, and $x-e_i$ (truncated subtraction on $\mathbb N$) is only used when $x_i>0$. $S^*_i$ takes values in `ℕ∞`. `Standing` collects the page's assumptions and adds, as disclosed additions implicit in the model: $K\ge1$; $p_i\ge0$ with $\sum_i p_i=1$; $r_i\ge0$ (equivalent to $r_1\ge0$ under monotonicity); $c_A\ge0$; $\mu>0$, $\lambda>0$. Ties in the acquisition decision count as acquiring.
-- source:
--   Nadar, Akan, Debo & Scheller-Wolf, Optimal Procurement in Remanufacturing Systems with Uncertain Used-Item Condition, Oper. Res. 71(5) (2023), pp. 1443–1445 (PDF 4–6), §2, eq. (1), §3 properties (A.1)–(A.6), Theorem 1 (S*_i)

import Mathlib

namespace RemanProcure.Noncongestive

/-- Parameters of the remanufacture-to-order core acquisition model of §2 (pp. 1443–1444).
Core types are indexed by `Fin K`; index `0` is the paper's type 1 (highest quality).
`p i` is the probability that an acquired core is of type `i`, `r i` the unit remanufacturing
cost, `h i` the unit holding cost rate, `cA` the acquisition cost, `cL` the unit lost-sale cost,
`α` the discount parameter, `μ` the acquisition rate and `lam` the demand rate `λ`
(`λ` is a Lean keyword). -/
structure Params (K : ℕ) where
  p : Fin K → ℝ
  r : Fin K → ℝ
  h : Fin K → ℝ
  cA : ℝ
  cL : ℝ
  α : ℝ
  μ : ℝ
  lam : ℝ

/-- The standing assumptions of §2 (pp. 1443–1444), together with the disclosed additions
`0 < K`, `p` a probability vector, `0 ≤ r₁`, `0 ≤ cA`, `0 < μ`, `0 < λ`. -/
def Standing {K : ℕ} (P : Params K) : Prop :=
  0 < K ∧
  (∀ i, 0 ≤ P.p i) ∧ ∑ i, P.p i = 1 ∧
  Monotone P.r ∧ (∀ i, 0 ≤ P.r i) ∧
  Antitone P.h ∧ (∀ i, 0 < P.h i) ∧
  (∀ i, P.r i < P.cL) ∧
  0 ≤ P.cA ∧
  0 < P.α ∧ P.α < 1 ∧ 0 < P.μ ∧ 0 < P.lam ∧
  P.α + P.lam + P.μ = 1

/-- The `i`-th unit vector `eᵢ` of `ℕ₀^K`. -/
def e {K : ℕ} (i : Fin K) : Fin K → ℕ := Pi.single i 1

/-- Total holding cost rate `h(x) = ∑ᵢ hᵢ xᵢ`. -/
def hold {K : ℕ} (P : Params K) (x : Fin K → ℕ) : ℝ := ∑ i, P.h i * (x i : ℝ)

/-- Acquisition operator: `T₁v(x) = min{v(x), c_A + ∑ᵢ pᵢ v(x + eᵢ)}`. -/
noncomputable def T1 {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) (x : Fin K → ℕ) : ℝ :=
  min (v x) (P.cA + ∑ i, P.p i * v (x + e i))

/-- Remanufacturing and core-choice operator:
`T₂v(x) = min{v(x) + c_L, min_{i : xᵢ > 0} {v(x − eᵢ) + rᵢ}}`.
Unavailable types (`xᵢ = 0`) contribute the rejection value `v(x) + c_L`, so the fold equals the
paper's expression, including the case `x = 0` where the inner minimum is over the empty set. -/
noncomputable def T2 {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) (x : Fin K → ℕ) : ℝ :=
  Finset.univ.fold min (v x + P.cL)
    (fun i => if 0 < x i then v (x - e i) + P.r i else v x + P.cL)

/-- The operator `Tv(x) = μ T₁v(x) + λ T₂v(x) + h(x)` of equation (1). -/
noncomputable def T {K : ℕ} (P : Params K) (v : (Fin K → ℕ) → ℝ) : (Fin K → ℕ) → ℝ :=
  fun x => P.μ * T1 P v x + P.lam * T2 P v x + hold P x

/-- The optimal cost function `v*`, defined as the pointwise limit of value iteration
`Tⁿ 0` started from the zero function. -/
noncomputable def vstar {K : ℕ} (P : Params K) (x : Fin K → ℕ) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => ((T P)^[n] 0) x)

/-- The acquisition gap `c_A + ∑ᵢ pᵢ v*(x + eᵢ) − v*(x)`. -/
noncomputable def acqGap {K : ℕ} (P : Params K) (x : Fin K → ℕ) : ℝ :=
  P.cA + ∑ i, P.p i * vstar P (x + e i) - vstar P x

/-- "It is optimal to acquire in state `x`": acquisition attains the minimum in `T₁v*(x)`
(ties count as acquiring). -/
def AcqOpt {K : ℕ} (P : Params K) (x : Fin K → ℕ) : Prop := acqGap P x ≤ 0

/-- The acquire-up-to level `S*ᵢ(x₋ᵢ) ∈ ℕ ∪ {∞}`: the least `n` such that acquiring is not
optimal in the state obtained from `x` by setting the `i`-th coordinate to `n`; `⊤` if there is
no such `n`. It depends only on `x₋ᵢ`. -/
noncomputable def Sstar {K : ℕ} (P : Params K) (i : Fin K) (x : Fin K → ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : ¬ AcqOpt P (Function.update x i n)), (n : ℕ∞)

/-- The property set `V^A` of §3, p. 1445: properties (A.1)–(A.6). -/
def VA {K : ℕ} (P : Params K) (g : (Fin K → ℕ) → ℝ) : Prop :=
  -- (A.1)
  (∀ (x : Fin K → ℕ) (w : Fin K), g (x + e w) + P.cL ≥ g x + P.r w) ∧
  -- (A.2)
  (∀ (x : Fin K → ℕ) (q w : Fin K), q < w → g (x + e q) + P.r w ≥ g (x + e w) + P.r q) ∧
  -- (A.3)
  (∀ (x : Fin K → ℕ) (d l q : Fin K), d ≤ l → l ≤ q →
    g (x + e q + e l) - g (x + e q + e d) ≥ g (x + e l) - g (x + e d)) ∧
  -- (A.4)
  (∀ (x : Fin K → ℕ) (d l q w : Fin K), d ≤ l → l ≤ q → q ≤ w →
    g (x + e q + e l) - g (x + e q + e d) ≥ g (x + e w + e l) - g (x + e w + e d)) ∧
  -- (A.5)
  (∀ (x : Fin K → ℕ) (l q : Fin K), l ≤ q →
    (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e q + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e q + e i)) - g (x + e q)
    ≥ (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e i)) - g x) ∧
  -- (A.6)
  (∀ (x : Fin K → ℕ) (l q w : Fin K), l ≤ q → q < w →
    (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e q + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e q + e i)) - g (x + e q)
    ≥ (∑ i ∈ Finset.univ.filter (· ≤ l), P.p i * g (x + e w + e l))
      + (∑ i ∈ Finset.univ.filter (l < ·), P.p i * g (x + e w + e i)) - g (x + e w))

end RemanProcure.Noncongestive


