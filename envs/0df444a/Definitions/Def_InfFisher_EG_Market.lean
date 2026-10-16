-- Prove2me | Definitions.Def_InfFisher_EG_Market
-- name    : InfFisher_EG_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:06.791783+00:00
-- url     : https://prove2.me/theorems/4cef2291-0fa3-4c9a-80c0-f5a69f9b894d
-- title:
--   §2–§3, pp. 5–8 — pairing, bundles, allocations, prices, pure allocations, demand sets, market equilibrium, (P_EG), (D_EG), max_i β_i v_i, the utility set U of (1)
-- statement:
--   These definitions fix the infinite-dimensional linear Fisher market of Section 2 of Gao and Kroer and the two Eisenberg–Gale programs of Section 3, over an arbitrary measure $\mu$ on a measurable item space (in the paper, Lebesgue measure on a compact $\Theta\subseteq\mathbb R^d$). There are $n$ buyers with valuations $v_i$ and budgets $B_i$.
--
--   1. **Pairing.** $\langle f,g\rangle=\int fg\,d\mu$.
--   2. **Bundles and allocations.** A bundle is an element of $L^\infty(\Theta)_+$: an essentially bounded function that is nonnegative almost everywhere. An allocation is a tuple $x=(x_1,\dots,x_n)$ of bundles with $\sum_i x_i\le\mathbf 1$ almost everywhere.
--   3. **Prices.** A price is an element of $L^1(\Theta)_+$: an integrable function that is nonnegative almost everywhere.
--   4. **Pure allocations.** $x$ is pure if $x_i=\mathbf 1_{\Theta_i}$ almost everywhere for measurable, pairwise a.e.-disjoint sets $\Theta_i\subseteq\Theta$.
--   5. **Demand.** $y\in D_i(p)=\arg\max\{\langle v_i,y'\rangle: y'\in L^\infty(\Theta)_+,\ \langle p,y'\rangle\le B_i\}$.
--   6. **Market equilibrium (ME).** A pair $(x^*,p^*)$ with $p^*$ a price, $x^*$ an allocation, $x_i^*\in D_i(p^*)$ for all $i$, and $\langle p^*,\mathbf 1-\sum_i x_i^*\rangle=0$.
--   7. **The programs.** The primal $(\mathcal P_{\mathrm{EG}})$ maximizes $\sum_i B_i\log\langle v_i,x_i\rangle$ over allocations $x$; the dual $(\mathcal D_{\mathrm{EG}})$ minimizes
--   $$\langle p,\mathbf 1\rangle-\sum_i B_i\log\beta_i\quad\text{over prices }p\text{ and }\beta\in\mathbb R^n_+\text{ with }p\ge\beta_i v_i\ \text{a.e. for all }i.$$
--   8. **Auxiliary objects.** The pointwise maximum $\max_i\beta_i v_i$, and the feasible utility set $U(v,\Theta)=\{(\langle v_1,x_1\rangle,\dots,\langle v_n,x_n\rangle): x \text{ an allocation}\}$ of (1).
--
--   These are the shared interface of every equilibrium, duality and fairness statement in the paper.
--
--   **Formalization Note** Functions are compared almost everywhere instead of being taken as quotient classes; with $\mu$ restricted to $\Theta$, values outside $\Theta$ are irrelevant. Lean's real logarithm has $\log 0=0$, whereas the paper's objectives are $-\infty$ (primal) and $+\infty$ (dual) there. So an optimal primal solution must give every buyer positive utility and is compared only with allocations that do, and an optimal dual solution must have $\beta>0$ and is compared only with feasible pairs that do; the excluded points are never better in the paper. The maximum over buyers is a supremum over the finite index set, equal to the maximum when $n\ge1$. Budgets are not required to be positive inside these definitions; $B_i>0$ is a hypothesis of each theorem.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, §2 pp. 5–7, (PEG) p. 7, (DEG) p. 8, (1) p. 8

import Mathlib

namespace InfFisher.EG

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

noncomputable def pair (μ : Measure α) (f g : α → ℝ) : ℝ := ∫ θ, f θ * g θ ∂μ

def IsBundle (μ : Measure α) (y : α → ℝ) : Prop :=
  MemLp y ⊤ μ ∧ 0 ≤ᵐ[μ] y

def IsAllocation (μ : Measure α) {n : ℕ} (x : Fin n → α → ℝ) : Prop :=
  (∀ i, IsBundle μ (x i)) ∧ ∀ᵐ θ ∂μ, ∑ i, x i θ ≤ 1

def IsPrice (μ : Measure α) (p : α → ℝ) : Prop :=
  Integrable p μ ∧ 0 ≤ᵐ[μ] p

def IsPure (μ : Measure α) (Θ : Set α) {n : ℕ} (x : Fin n → α → ℝ) : Prop :=
  ∃ S : Fin n → Set α,
    (∀ i, MeasurableSet (S i) ∧ S i ⊆ Θ) ∧
    (∀ i j, i ≠ j → μ (S i ∩ S j) = 0) ∧
    ∀ i, x i =ᵐ[μ] (S i).indicator (fun _ => (1 : ℝ))

def InDemand (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (i : Fin n) (y : α → ℝ) : Prop :=
  IsBundle μ y ∧ pair μ p y ≤ B i ∧
  ∀ y', IsBundle μ y' → pair μ p y' ≤ B i → pair μ (v i) y' ≤ pair μ (v i) y

def IsME (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) (p : α → ℝ) : Prop :=
  IsPrice μ p ∧ IsAllocation μ x ∧
  (∀ i, InDemand μ v B p i (x i)) ∧
  pair μ p (fun θ => 1 - ∑ i, x i θ) = 0

noncomputable def pegObj (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) : ℝ :=
  ∑ i, B i * Real.log (pair μ (v i) (x i))

def IsPEGOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (x : Fin n → α → ℝ) : Prop :=
  IsAllocation μ x ∧ (∀ i, 0 < pair μ (v i) (x i)) ∧
  ∀ x', IsAllocation μ x' → (∀ i, 0 < pair μ (v i) (x' i)) →
    pegObj μ v B x' ≤ pegObj μ v B x

def IsDEGFeasible (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  IsPrice μ p ∧ (∀ i, 0 ≤ β i) ∧
  ∀ i, (fun θ => β i * v i θ) ≤ᵐ[μ] p

noncomputable def degObj (μ : Measure α) {n : ℕ}
    (B : Fin n → ℝ) (p : α → ℝ) (β : Fin n → ℝ) : ℝ :=
  (∫ θ, p θ ∂μ) - ∑ i, B i * Real.log (β i)

def IsDEGOptimal (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ)
    (B : Fin n → ℝ) (p : α → ℝ) (β : Fin n → ℝ) : Prop :=
  IsDEGFeasible μ v p β ∧ (∀ i, 0 < β i) ∧
  ∀ p' β', IsDEGFeasible μ v p' β' → (∀ i, 0 < β' i) →
    degObj μ B p β ≤ degObj μ B p' β'

noncomputable def maxScaled {n : ℕ} (v : Fin n → α → ℝ)
    (β : Fin n → ℝ) : α → ℝ :=
  fun θ => ⨆ i, β i * v i θ

def feasUtil (μ : Measure α) {n : ℕ} (v : Fin n → α → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ x, IsAllocation μ x ∧ ∀ i, u i = pair μ (v i) (x i)}

end InfFisher.EG


