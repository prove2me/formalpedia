-- Prove2me | Definitions.Def_DPCutRelease_Main_EdgeDP
-- name    : DPCutRelease_Main_EdgeDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:09:15.012897+00:00
-- url     : https://prove2.me/theorems/369988e0-f8fc-41ad-9396-9701f825286a
-- title:
--   Edge weights on unordered pairs, cut values, ℓ₁-adjacency and (ε, δ) edge-differential privacy (Definitions 4–5)
-- statement:
--   The public vertex set is $[n]=\{0,\dots,n-1\}$. Every unordered pair $e=\{u,v\}$, $u\ne v$, is an **edge coordinate** (zero-weight non-edges included); it is written as the ordered pair $(u,v)$ with $u<v$, and $\mathbb R^{\binom n2}$ is the space of vectors indexed by these pairs. For $x,y\in\mathbb R^{\binom n2}$, $\langle x,y\rangle=\sum_e x_ey_e$, $\|x\|_1=\sum_e|x_e|$ and $x\odot y$ is the coordinatewise product.
--
--   For $S\subseteq[n]$ (including $\emptyset$ and $[n]$) the **cut incidence vector** is $c_S(\{u,v\})=1$ if exactly one of $u,v$ lies in $S$ and $0$ otherwise, and the **cut value** of a weight vector $w$ is
--   $$w(S,V\setminus S)=\langle w,c_S\rangle .$$
--
--   **Definition 4.** Histograms $w,w'\in\mathbb R_{\ge0}^{\binom n2}$ are **adjacent** if $\|w-w'\|_1\le1$. A randomized algorithm whose output on $w$ has law $M(w)$ is **$(\varepsilon,\delta)$ edge-DP** if for all adjacent $w,w'$ and measurable output events $A$,
--   $$\Pr[M(w)\in A]\le e^{\varepsilon}\Pr[M(w')\in A]+\delta .$$
--   Since adjacency is symmetric, quantifying over ordered adjacent pairs also gives the inequality with $w,w'$ exchanged. The variant for an algorithm given as a function $f(w,\omega)$ of its input and of randomness $\omega\sim\mu$ reads $\Pr[f(w)\in A]=\mu(f(w,\cdot)^{-1}(A))$.
--
--   **Definition 5.** $\mathrm{Lap}(b)$, $b>0$, has density $\frac1{2b}e^{-|z|/b}$; the published `PrivLearn.Generic.laplace` is exactly this law, and $\mathrm{Lap}(1)$ is a probability measure.
--
--   **Formalization Note.** `Pair n` is the subtype `{p : Fin n × Fin n // p.1 < p.2}`, `EdgeVec n = Pair n → ℝ`, and `x * y` is $x\odot y$. `IsEdgeDP M ε δ` compares $(M\,w\,A)$ and $(M\,w'\,A)$ as real numbers (`toReal`); it is only applied to probability laws. `IsEdgeDPFun μ f ε δ` evaluates $\mu$ on preimages, so a non-measurable algorithm cannot satisfy it vacuously. The file also records the instance that `PrivLearn.Generic.laplace 1` is a probability measure.
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 11, Definitions 4–5; p. 5 (§1.2.1, cut values); p. 27 (§5.1, c_S)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace DPCutRelease.Main

/-!
# Edge weights, cut values, ℓ₁-adjacency and (ε, δ) edge-differential privacy

Eliáš, Kamath, Kulkarni, Li, Liu, Mahabadi, Peng, Tarnawski, Xu, Zou, *Polynomial-Time
Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error*,
arXiv:2611.06670v1, p. 11 (§2, Definitions 4 and 5), p. 5 (§1.2.1) and p. 27 (§5.1).

* The vertex set is `[n] = Fin n` (0-based). An edge coordinate is an unordered pair `{u, v}`,
  `u ≠ v`, written as the ordered pair `(u, v)` with `u < v` (`Pair n`); there are `(n choose 2)`
  of them and every one is a coordinate, including zero-weight non-edges.
* `EdgeVec n = Pair n → ℝ` holds weight vectors `w ∈ ℝ^{(n choose 2)}`, masks and witnesses;
  `x * y` is the coordinatewise product `x ⊙ y`.
* `cutVec S` is the incidence vector `c_S` of the cut `(S, [n] ∖ S)`, for every `S ⊆ [n]`
  (`∅` and `[n]` included), and `cutValue w S = ⟨w, c_S⟩ = w(S, V ∖ S)`.
* Adjacency (Definition 4): both histograms nonnegative and `‖w − w'‖₁ ≤ 1`.
* `IsEdgeDP M ε δ` (Definition 4) for a map `M` from histograms to output laws:
  `Pr[M(w) ∈ A] ≤ e^ε Pr[M(w') ∈ A] + δ` for all adjacent `w, w'` and measurable `A`. Adjacency is
  symmetric, so the clause "and symmetrically with `w, w'` exchanged" is the same condition for the
  swapped pair. Probabilities are compared as real numbers (`toReal`); every law to which it is
  applied in this mission is a probability measure.
* `IsEdgeDPFun μ f ε δ`: the same for a randomized algorithm given as a function `f w ω` of the
  input and of its randomness `ω ∼ μ`; `Pr[f(w) ∈ A]` is `μ (f w ⁻¹' A)` (an outer measure if the
  preimage were not measurable), so no measurability side condition can make it vacuous.
* Lap(1) (Definition 5) is the published `PrivLearn.Generic.laplace 1`; the instance below records
  that it is a probability measure (needed for infinite products of Laplace draws).
-/

/-- An unordered pair `{u, v}` of distinct vertices of `[n] = Fin n`, written with `u < v`. -/
abbrev Pair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-- Vectors indexed by the `(n choose 2)` edge coordinates. -/
abbrev EdgeVec (n : ℕ) : Type := Pair n → ℝ

/-- The inner product `⟨x, y⟩ = Σ_e x_e y_e`. -/
def dot {n : ℕ} (x y : EdgeVec n) : ℝ := ∑ e, x e * y e

/-- The ℓ₁ norm `‖x‖₁ = Σ_e |x_e|`. -/
def l1 {n : ℕ} (x : EdgeVec n) : ℝ := ∑ e, |x e|

/-- The incidence vector `c_S ∈ {0,1}^{(n choose 2)}` of the cut `(S, [n] ∖ S)`:
`c_S({u, v}) = 1` iff exactly one of `u, v` lies in `S`. -/
def cutVec {n : ℕ} (S : Finset (Fin n)) : EdgeVec n :=
  fun e => if (e.1.1 ∈ S ↔ e.1.2 ∈ S) then 0 else 1

/-- The cut value `w(S, V ∖ S) = ⟨w, c_S⟩`. -/
def cutValue {n : ℕ} (w : EdgeVec n) (S : Finset (Fin n)) : ℝ := dot w (cutVec S)

/-- A nonnegative weight vector (a nonnegative weighted graph on `[n]`). -/
def Nonneg {n : ℕ} (w : EdgeVec n) : Prop := ∀ e, 0 ≤ w e

/-- Definition 4: histograms `w, w' ∈ ℝ_{≥0}^{(n choose 2)}` are adjacent if `‖w − w'‖₁ ≤ 1`. -/
def Adjacent {n : ℕ} (w w' : EdgeVec n) : Prop :=
  Nonneg w ∧ Nonneg w' ∧ l1 (w - w') ≤ 1

/-- Definition 4: the randomized algorithm whose output on `w` has law `M w` is `(ε, δ)` edge-DP. -/
def IsEdgeDP {n : ℕ} {O : Type*} [MeasurableSpace O] (M : EdgeVec n → Measure O)
    (ε δ : ℝ) : Prop :=
  ∀ w w' : EdgeVec n, Adjacent w w' → ∀ A : Set O, MeasurableSet A →
    (M w A).toReal ≤ Real.exp ε * (M w' A).toReal + δ

/-- Definition 4 for a randomized algorithm `w ↦ f w ω` with randomness `ω ∼ μ`. -/
def IsEdgeDPFun {n : ℕ} {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    (μ : Measure Ω) (f : EdgeVec n → Ω → O) (ε δ : ℝ) : Prop :=
  ∀ w w' : EdgeVec n, Adjacent w w' → ∀ A : Set O, MeasurableSet A →
    (μ (f w ⁻¹' A)).toReal ≤ Real.exp ε * (μ (f w' ⁻¹' A)).toReal + δ

/-- Lap(1) (Definition 5, density `e^{−|z|}/2`) is a probability measure. -/
instance laplace_one_isProbabilityMeasure : IsProbabilityMeasure (PrivLearn.Generic.laplace 1) := by
  constructor
  have hf : ∫ x : ℝ, Real.exp (-|x| / 1) / (2 * 1) = 1 := by
    have h := integral_comp_abs (f := fun x : ℝ => Real.exp (-x / 1) / (2 * 1))
    rw [h]
    simp only [div_one, mul_one]
    rw [integral_div, integral_exp_neg_Ioi_zero]
    norm_num
  have hint : Integrable (fun x : ℝ => Real.exp (-|x| / 1) / (2 * 1)) :=
    Integrable.of_integral_ne_zero (by rw [hf]; norm_num)
  rw [PrivLearn.Generic.laplace, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity), hf,
    ENNReal.ofReal_one]

end DPCutRelease.Main


