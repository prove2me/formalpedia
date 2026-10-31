-- Prove2me | Definitions.Def_OfflineZeroSumMG_OfflineData
-- name    : OfflineZeroSumMG_OfflineData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:56.973929+00:00
-- url     : https://prove2.me/theorems/71113363-53bb-4be1-89f7-ed94e0223f64
-- title:
--   (2.4), (2.6), (3.1)–(3.2), (A.1) — offline data law, counts, empirical model, variance, clipped unilateral concentrability
-- statement:
--   This module fixes the offline data and the empirical model.
--
--   1. **Data law (2.4).** A dataset of $N$ transitions $D=\{(s_i,a_i,b_i,s'_i)\}_{i\le N}$ is drawn with $(s_i,a_i,b_i)$ i.i.d. from $d_{\mathsf b}\in\Delta(\mathcal S\times\mathcal A\times\mathcal B)$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ independently, so $D$ has probability $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$.
--   2. **Counts and empirical model.** $N(s,a,b)=\sum_i 1\{(s_i,a_i,b_i)=(s,a,b)\}$;
--   $$\widehat P(s'\mid s,a,b)=\begin{cases}\frac1{N(s,a,b)}\sum_i 1\{(s_i,a_i,b_i,s'_i)=(s,a,b,s')\},&N(s,a,b)>0,\\ 1/S,&N(s,a,b)=0,\end{cases}$$
--   and $\widehat r(s,a,b)=r(s,a,b)$ if $N(s,a,b)>0$, $0$ otherwise (3.1)–(3.2).
--   3. **Variance (A.1), (3.6).** $\mathrm{Var}_p(V)=p(V\circ V)-(pV)^2$ for a probability row $p$.
--   4. **Clipped unilateral concentrability (2.6).** For a Nash pair $(\mu^\star,\nu^\star)$ and an initial distribution $\rho$, the constant $C$ covers the data when, for all policies $\mu,\nu$ and all $(s,a,b)$,
--   $$\min\Big\{d^{\mu,\nu^\star}(s,a,b;\rho),\tfrac{1}{S(A+B)}\Big\}\le C\,d_{\mathsf b}(s,a,b),\qquad \min\Big\{d^{\mu^\star,\nu}(s,a,b;\rho),\tfrac{1}{S(A+B)}\Big\}\le C\,d_{\mathsf b}(s,a,b).$$
--   5. **I.i.d. draws from one row (Claim 1).** The probability of an event on $n$ i.i.d. draws $X_1,\dots,X_n\sim p$, and their empirical distribution $\hat p(s)=\frac1n\sum_i1\{X_i=s\}$.
--
--   Assumption 2 says that $C^\star_{\mathsf{clipped}}$, the larger of the two suprema of $\min\{d,1/(S(A+B))\}/d_{\mathsf b}$ (with $0/0=0$), is finite.
--
--   **Formalization Note** Datasets are functions `Fin N → Fin S × Fin A × Fin B × Fin S`, and the probability of an event is the finite sum of the weights of the datasets in it, which is the law (2.4) exactly. Assumption 2 is written in product form: the predicate holds for $C$ exactly when $C^\star_{\mathsf{clipped}}$ is finite and $C^\star_{\mathsf{clipped}}\le C$; it holds for $C=C^\star_{\mathsf{clipped}}$ itself. The product form keeps the paper's convention that the ratio is $+\infty$ when $d_{\mathsf b}=0<d$, which Lean's $x/0=0$ would lose. The branch $1/S$ of $\widehat P$ is explicit.
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (2.4), p.5; Assumption 2, (2.6), p.6; (3.1)–(3.2), p.6; (3.6), p.7; (A.1), p.13; Claim 1, p.25

import Mathlib
import Definitions.Def_OfflineZeroSumMG_MarkovGame

open Classical

namespace OfflineZeroSumMG

/-! # Offline data, the empirical game, and clipped unilateral concentrability

Yan, Li, Chen & Fan, arXiv:2206.04044v2, (2.4), p.5; Assumption 2, (2.6), p.6; (3.1), (3.2),
p.6; (3.6), p.7; (A.1), p.13.

**Formalization Note.** A dataset of `N` transitions is `D : Fin N → Fin S × Fin A × Fin B ×
Fin S`, the `i`-th entry being `(s_i, a_i, b_i, s'_i)`. Under (2.4) the dataset is a random
element of this finite set with probability `∏_i d_b(s_i, a_i, b_i) P(s'_i | s_i, a_i, b_i)`,
so the probability of an event is a finite sum (`dataProb`) and no measure theory is needed. -/

/-- One sample transition `(s, a, b, s')`. -/
abbrev Sample (S A B : ℕ) := Fin S × Fin A × Fin B × Fin S

/-- `d_b ∈ Δ(S × A × B)`: a probability distribution on state-action triples
(arXiv:2206.04044v2, (2.4), p.5). -/
def IsDist {S A B : ℕ} (db : Fin S → Fin A → Fin B → ℝ) : Prop :=
  (∀ s a b, 0 ≤ db s a b) ∧ ∑ s, ∑ a, ∑ b, db s a b = 1

/-- The probability of a dataset `D` under (2.4) (arXiv:2206.04044v2, p.5):
`(s_i, a_i, b_i)` i.i.d. `∼ d_b` and `s'_i ∼ P(· | s_i, a_i, b_i)` independently, so
`D` has probability `∏_i d_b(s_i, a_i, b_i) P(s'_i | s_i, a_i, b_i)`. -/
def dataWeight {S A B N : ℕ} (db : Fin S → Fin A → Fin B → ℝ) (P : Kernel S A B)
    (D : Fin N → Sample S A B) : ℝ :=
  ∏ i, db (D i).1 (D i).2.1 (D i).2.2.1 * P (D i).1 (D i).2.1 (D i).2.2.1 (D i).2.2.2

/-- The probability, under the data law (2.4) with `N` samples, of the event `E` on datasets
(arXiv:2206.04044v2, p.5): `∑_D 1{E(D)} · dataWeight D`. -/
noncomputable def dataProb {S A B : ℕ} (db : Fin S → Fin A → Fin B → ℝ) (P : Kernel S A B)
    (N : ℕ) (E : (Fin N → Sample S A B) → Prop) : ℝ :=
  ∑ D : Fin N → Sample S A B, if E D then dataWeight db P D else 0

/-- The sample size `N(s, a, b) = ∑_{i=1}^N 1{(s_i, a_i, b_i) = (s, a, b)}`
(arXiv:2206.04044v2, p.6). -/
def cnt {S A B N : ℕ} (D : Fin N → Sample S A B) (s : Fin S) (a : Fin A) (b : Fin B) : ℕ :=
  (Finset.univ.filter fun i => (D i).1 = s ∧ (D i).2.1 = a ∧ (D i).2.2.1 = b).card

/-- The empirical transition kernel (3.1) (arXiv:2206.04044v2, p.6):
`P̂(s' | s, a, b) = (1/N(s,a,b)) ∑_i 1{(s_i, a_i, b_i, s'_i) = (s, a, b, s')}` if
`N(s, a, b) > 0`, and `1/S` if `N(s, a, b) = 0`. -/
noncomputable def Phat {S A B N : ℕ} (D : Fin N → Sample S A B) :
    Fin S → Fin A → Fin B → Fin S → ℝ :=
  fun s a b s' =>
    if cnt D s a b = 0 then 1 / (S : ℝ)
    else ((Finset.univ.filter fun i => D i = (s, a, b, s')).card : ℝ) / (cnt D s a b : ℝ)

/-- The empirical reward (3.2) (arXiv:2206.04044v2, p.6): `r̂(s, a, b) = r(s, a, b)` if
`N(s, a, b) > 0`, and `0` if `N(s, a, b) = 0`. -/
def rhat {S A B N : ℕ} (r : Reward S A B) (D : Fin N → Sample S A B) : Reward S A B :=
  fun s a b => if cnt D s a b = 0 then 0 else r s a b

/-- The variance of `W` under a probability row `p`,
`Var_p(W) = p(W ∘ W) − (pW)²` (arXiv:2206.04044v2, (A.1), p.13; (3.6), p.7 with `p = P̂_{s,a,b}`). -/
def varP {S : ℕ} (p : Fin S → ℝ) (W : Fin S → ℝ) : ℝ :=
  ∑ s, p s * W s ^ 2 - (∑ s, p s * W s) ^ 2

/-- Assumption 2 (clipped unilateral concentrability) with constant `C`
(arXiv:2206.04044v2, (2.6), p.6), relative to the Nash pair `(μ⋆, ν⋆)` and the initial
distribution `ρ`: for every policy `μ` and every `(s, a, b)`,
`min{d^{μ,ν⋆}(s, a, b; ρ), 1/(S(A+B))} ≤ C · d_b(s, a, b)`, and for every policy `ν` and every
`(s, a, b)`, `min{d^{μ⋆,ν}(s, a, b; ρ), 1/(S(A+B))} ≤ C · d_b(s, a, b)`.

**Formalization Note.** The paper's `C⋆_clipped` is the larger of the two suprema of
`min{d, 1/(S(A+B))} / d_b` with `0/0 = 0` (and the ratio `+∞` when `d_b = 0 < min{…}`).
`C⋆_clipped` is finite and `≤ C` exactly when this predicate holds, and it holds for
`C = C⋆_clipped` itself. The multiplicative form avoids Lean's `x / 0 = 0`. -/
def IsClippedCoverage {S A B : ℕ} (P : Kernel S A B) (γ : ℝ) (ρ : Fin S → ℝ)
    (db : Fin S → Fin A → Fin B → ℝ) (μs : Policy S A) (νs : Policy S B) (C : ℝ) : Prop :=
  (∀ (μ : Policy S A) s a b,
      min (occ P γ ρ μ νs s a b) (1 / ((S : ℝ) * ((A : ℝ) + (B : ℝ)))) ≤ C * db s a b) ∧
  (∀ (ν : Policy S B) s a b,
      min (occ P γ ρ μs ν s a b) (1 / ((S : ℝ) * ((A : ℝ) + (B : ℝ)))) ≤ C * db s a b)

/-- The probability of an event `E` on `n` i.i.d. draws `X_1, …, X_n ∼ p` from `Fin S`:
`∑_X 1{E(X)} ∏_i p(X_i)` (the law of the next states `s'_i` from a fixed `(s₀, a, b)` given
`N(s₀, a, b) = n`, arXiv:2206.04044v2, Claim 1, p.25). -/
noncomputable def iidProb {S : ℕ} (p : Fin S → ℝ) (n : ℕ) (E : (Fin n → Fin S) → Prop) : ℝ :=
  ∑ X : Fin n → Fin S, if E X then ∏ i, p (X i) else 0

/-- The empirical distribution of `X_1, …, X_n`: `p̂(s) = (1/n) ∑_i 1{X_i = s}`. -/
noncomputable def empirical {S n : ℕ} (X : Fin n → Fin S) : Fin S → ℝ :=
  fun s => ((Finset.univ.filter fun i => X i = s).card : ℝ) / (n : ℝ)

end OfflineZeroSumMG


