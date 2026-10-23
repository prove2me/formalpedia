-- Prove2me | Definitions.Def_RankAssort_SimpleLearn_Model
-- name    : RankAssort_SimpleLearn_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:03.021745+00:00
-- url     : https://prove2.me/theorems/da16ed2c-0732-4681-9024-60afae19b3e9
-- title:
--   §2, pp. 8–11; App. A, pp. 50, 53 — customer types (p, f, k), the sequential click law with bias, hooking H, the coupled first-click law, C̄(r, π), expected hook and marginal benefit
-- statement:
--   There are $n$ products $[n]$. A **customer type** is a triple $(p, f, k)$ (pp. 9–10):
--
--   1. $p = (p_1,\dots,p_n)$ with $p_i \in [0,1]$, the **intrinsic click probabilities**;
--   2. $f_i : 2^{[n]} \to [-p_i,\, 1-p_i]$, the **bias functions**, with $f_i(\emptyset) = 0$;
--   3. $k \in [n]$, the **first impression window**: the customer browses the top $k$ positions of the ranking.
--
--   Types are drawn from an arbitrary distribution $\mathcal D$; the three components may be correlated.
--
--   **Sequential click law with bias.** Given a ranking $\pi$ (or a prefix of one), a customer of type $(p,f,k)$ inspects the products at positions $1,\dots,\min(k,|\pi|)$ in order. If $\chi_i(\pi)$ is the set of products she clicked at earlier positions, she clicks the product $i$ she is looking at with probability $p_i + f_i(\chi_i(\pi))$. Clicks outside the window are set to $0$ (p. 10). The customer is **hooked**, $H(\pi) = 1$, iff she clicks at least one product in her window (pp. 10–11). The conditional hook probability given the type is
--
--   $$
--   \Pr[H(\pi)=1 \mid (p,f,k)] = \sum_{c \ne 0} \prod_{j=1}^{\min(k,|\pi|)} \mathrm{Bern}\bigl(p_{\pi^{-1}(j)} + f_{\pi^{-1}(j)}(\chi_j(c))\bigr)(c_j),
--   $$
--
--   the sum over click patterns $c \in \{0,1\}^{\min(k,|\pi|)}$ with at least one click. The **expected hook** is $\mathbb E[H(\pi)] = \mathbb E_{(p,f,k)\sim\mathcal D}\Pr[H(\pi)=1\mid(p,f,k)]$, and the **marginal benefit** of placing product $i$ immediately after a prefix $\sigma$ is (Algorithms 1–2, pp. 17, 23)
--
--   $$
--   \Delta(\sigma, i) = \mathbb E[H(\sigma \cup i)] - \mathbb E[H(\sigma)].
--   $$
--
--   **Coupled first-click law** (proof of Lemma 1, p. 53). To compare several rankings on one customer the paper uses, for each product $i$, a single Bernoulli$(p_i)$ variable "the customer clicks $i$ when no product was clicked before it", shared by all rankings. Under this coupling, $\bar C(r,\pi) = 1$ (p. 50) is the event that none of the products at positions $1,\dots,\min(r,k)$ of $\pi$ is liked, and $\bar C(r,\pi)\,C_{\pi^{-1}(r+1)}(\pi) = 1$ is the event that, in addition, position $r+1 \le k$ holds a liked product. This gives
--
--   $$
--   \mathbb E\bigl[\bar C(r-1,\pi)\,C_{\pi^{-1}(r)}(\pi)\bigr], \qquad \mathbb E\bigl[\bar C(r-1,\pi)\,\bar C(r-1,\pi^*)\,C_{\pi^{*-1}(r)}(\pi^*)\bigr],
--   $$
--
--   the quantities of (6) and (10), as expectations over types of coupled probabilities.
--
--   These are the objects of the online assortment ranking problem; every statement of the mission is phrased with them.
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. A type is the structure `CustomerType n`; the type distribution is a probability measure $D$ on a measurable space $\Theta$ with a type map $\tau : \Theta \to$ `CustomerType n`, and `TypeMeasurable τ` says that every coordinate of $\tau$ is measurable (the page's "$(p_t,f_t,k_t) \sim \mathcal D$" is a random variable; without measurability the Bochner integrals defining the expectations would be $0$). `hookProb` is the sequential law, `coupledProb`/`noClickTop`/`clicksAt` the coupled law, `firstClickTerm` and `jointTerm` the two expectations displayed above with 0-based $r$, `expHook` and `margBenefit` the expected hook and marginal benefit.
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, pp. 9–11 (§2 model), p. 16–17 (marginal benefit, Algorithm 1), p. 50 (C̄(r, π) and (6)), p. 53 (coupled Bernoulli clicks)

import Mathlib

namespace RankAssort.SimpleLearn
open MeasureTheory

/-- A customer type `(p, f, k)` (Ferreira–Parthasarathy–Sekar, §2, pp. 9–10): intrinsic click
probabilities `p i ∈ [0, 1]`, bias functions `f i : 2^[n] → [-p i, 1 - p i]` with `f i ∅ = 0`,
and a first impression window `k ∈ [n]`. Products are `Fin n` (0-based). -/
structure CustomerType (n : ℕ) where
  p : Fin n → ℝ
  f : Fin n → Finset (Fin n) → ℝ
  k : ℕ
  p_nonneg : ∀ i, 0 ≤ p i
  p_le_one : ∀ i, p i ≤ 1
  f_ge : ∀ i S, -p i ≤ f i S
  f_le : ∀ i S, f i S ≤ 1 - p i
  f_empty : ∀ i, f i ∅ = 0
  one_le_k : 1 ≤ k
  k_le : k ≤ n

/-- Weight of the outcome `b` of a Bernoulli(`q`) coin. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

variable {n : ℕ}

/-- The browsed window of a (partial) ranking `l`: its first `min k (length l)` positions. -/
def window (θ : CustomerType n) (l : List (Fin n)) : ℕ := min θ.k l.length

/-- The product at window position `j` (0-based), i.e. `π⁻¹(j + 1)`. -/
def windowGet (θ : CustomerType n) (l : List (Fin n)) (j : Fin (window θ l)) : Fin n :=
  l.get ⟨j.1, lt_of_lt_of_le j.2 (min_le_right _ _)⟩

/-- Under click pattern `c` on the window, the set `χ` of products clicked before position `j`. -/
def clickedBefore (θ : CustomerType n) (l : List (Fin n)) (c : Fin (window θ l) → Bool)
    (j : Fin (window θ l)) : Finset (Fin n) :=
  (Finset.univ.filter (fun j' : Fin (window θ l) => j' < j ∧ c j' = true)).image (windowGet θ l)

/-- Probability, under the sequential click law with bias (pp. 9–10), that a customer of type `θ`
facing `l` produces exactly the click pattern `c` on her window: at window position `j` she clicks
with probability `p + f(χ)`, `χ` the set of products she clicked earlier. Clicks outside the
window are `0` by the convention of p. 10 and are not part of the pattern. -/
def clickWeight (θ : CustomerType n) (l : List (Fin n)) (c : Fin (window θ l) → Bool) : ℝ :=
  ∏ j, bern (θ.p (windowGet θ l j) + θ.f (windowGet θ l j) (clickedBefore θ l c j)) (c j)

/-- `E[H(π) | type θ]`: the probability that a customer of type `θ` is hooked by `l`, i.e. clicks
at least one product in her window (pp. 10–11). -/
def hookProb (θ : CustomerType n) (l : List (Fin n)) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin (window θ l) → Bool => ∃ j, c j = true),
    clickWeight θ l c

/-- Weight of a like-profile `L` in the coupled first-click law (p. 53): one independent
Bernoulli(`p i`) coin per product, "`i` is clicked when no product was clicked before it",
shared by every ranking. -/
def likeWeight (θ : CustomerType n) (L : Fin n → Bool) : ℝ :=
  ∏ i, bern (θ.p i) (L i)

open Classical in
/-- Probability of an event `E` of like-profiles under the coupled first-click law. -/
noncomputable def coupledProb (θ : CustomerType n) (E : (Fin n → Bool) → Prop) : ℝ :=
  ∑ L, if E L then likeWeight θ L else 0

/-- `C̄(r, π) = 1` under the coupling (p. 50): no product at 0-based positions `j < r` inside the
window is clicked. -/
def noClickTop (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) (L : Fin n → Bool) : Prop :=
  ∀ j (hj : j < l.length), j < r → j < θ.k → L (l.get ⟨j, hj⟩) = false

/-- The product at 0-based position `r` of `l` lies in the window and is liked; together with
`noClickTop θ l r L` this is the event `C̄(r, π) · C_{π⁻¹(r+1)}(π) = 1`. -/
def clicksAt (θ : CustomerType n) (l : List (Fin n)) (r : ℕ) (L : Fin n → Bool) : Prop :=
  ∃ hr : r < l.length, r < θ.k ∧ L (l.get ⟨r, hr⟩) = true

/-- `E[H(π)]` (p. 50): the hook probability averaged over types `τ θ`, `θ ∼ D`. -/
noncomputable def expHook {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (l : List (Fin n)) : ℝ :=
  ∫ θ, hookProb (τ θ) l ∂D

/-- `E[C̄(r, π) C_{π⁻¹(r+1)}(π)]` (0-based `r`; the paper's `E[C̄(r−1, π) C_{π⁻¹(r)}(π)]`, p. 50). -/
noncomputable def firstClickTerm {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (l : List (Fin n)) (r : ℕ) : ℝ :=
  ∫ θ, coupledProb (τ θ) (fun L => noClickTop (τ θ) l r L ∧ clicksAt (τ θ) l r L) ∂D

/-- `E[C̄(r, π) C̄(r, π') C_{π'⁻¹(r+1)}(π')]` (0-based `r`; the paper's
`E[C̄(r−1, π) C̄(r−1, π∗) C_{π∗⁻¹(r)}(π∗)]`, p. 51). -/
noncomputable def jointTerm {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (l l' : List (Fin n)) (r : ℕ) : ℝ :=
  ∫ θ, coupledProb (τ θ)
    (fun L => noClickTop (τ θ) l r L ∧ noClickTop (τ θ) l' r L ∧ clicksAt (τ θ) l' r L) ∂D

/-- Marginal benefit of placing product `i` right after the prefix `σ` (Algorithms 1–2, pp. 17, 23):
`E[H(σ ∪ i) − H(σ)]`. -/
noncomputable def margBenefit {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (σ : List (Fin n)) (i : Fin n) : ℝ :=
  expHook D τ (σ ++ [i]) - expHook D τ σ

/-- The type map is a random variable: each coordinate of `(p, f, k)` is measurable. -/
def TypeMeasurable {Θ : Type*} [MeasurableSpace Θ] (τ : Θ → CustomerType n) : Prop :=
  (∀ i, Measurable fun θ => (τ θ).p i) ∧ (∀ i S, Measurable fun θ => (τ θ).f i S) ∧
    Measurable fun θ => (τ θ).k

end RankAssort.SimpleLearn


