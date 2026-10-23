-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Model
-- name    : RobustPrefLearn_MTP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:42.212405+00:00
-- url     : https://prove2.me/theorems/b9e55e58-21fb-4ceb-84ff-79c2d5f74b0b
-- title:
--   §4–§5, pp. 10–15 — display sets, p-separable preferences M_p (Definition 1), KL divergences (1), kl, Chernoff information I_*(f) (Max-Min) and I^OA_* (2)
-- statement:
--   This file sets up the choice model of Feng, Caldentey and Ryan.
--
--   1. **Display sets.** There are $K$ versions of a product, $[K]=\{1,\dots,K\}$. A display set is a subset $S\subseteq[K]$ with $|S|\ge 2$; the collection of display sets is $\mathcal S$.
--   2. **Preferences.** A preference (consumer choice model) assigns to every display set $S$ and version $X$ a number $f(X|S)$, the probability that a consumer shown $S$ picks $X$.
--   3. **Definition 1 ($p$-separable preferences).** For a constant $p$, the class $\mathcal M_p$ consists of the preferences $f$ such that
--      - (A-1) $f(X|S)>0$ for $X\in S$ and $f(X|S)=0$ for $X\notin S$;
--      - (A-2) $\sum_{X\in S} f(X|S)=1$ for every $S\in\mathcal S$;
--      - (A-3) there is a ranking $\sigma_f$ (a permutation of $[K]$, rank $1$ being the top) such that for every $S$ and distinct $X,X'\in S$, $f(X'|S)\le f(X|S)$ if and only if $\sigma_f(X)<\sigma_f(X')$;
--      - (A-4) for every $S$ and $X,X'\in S$ with $\sigma_f(X)<\sigma_f(X')$, $f(X'|S)\le p\,f(X|S)$.
--
--      $\mathcal M_p(\sigma)$ is the set of $f\in\mathcal M_p$ whose ranking is $\sigma$, and $k$ is the top-ranked version of $f$ when $\sigma_f(k)=1$.
--   4. **Divergences.** For preferences $f_1,f_2$, a display set $S$ and a probability distribution $\lambda$ on $\mathcal S$,
--   $$D_S(f_1\|f_2)=\sum_{k\in S} f_1(k|S)\log\frac{f_1(k|S)}{f_2(k|S)},\qquad D_\lambda(f_1\|f_2)=\sum_{S\in\mathcal S}\lambda(S)\,D_S(f_1\|f_2),$$
--   and the Bernoulli divergence is $\mathrm{kl}(\delta_1,\delta_2)=\delta_1\log\frac{\delta_1}{\delta_2}+(1-\delta_1)\log\frac{1-\delta_1}{1-\delta_2}$.
--   5. **Chernoff information.** With $\overline{\mathcal M}_p(f)$ the preferences in $\mathcal M_p$ whose top-ranked version differs from that of $f$, and $\Delta(\mathcal S)$ the probability distributions on $\mathcal S$,
--   $$I_*(f)=\sup_{\lambda\in\Delta(\mathcal S)}\ \inf_{\bar f\in\overline{\mathcal M}_p(f)} D_\lambda(f\|\bar f),\qquad I^{\mathrm{OA}}_*=\inf_{f\in\mathcal M_p} I_*(f).$$
--
--   $I_*(f)$ measures how hard it is to identify the top-ranked version when the consumers' preference is $f$; every later statement of the mission is phrased through these objects.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. (A-3) is required only for distinct $X\neq X'$: for $X=X'$ the printed equivalence is false, and with it no preference would satisfy Definition 1. $I_*$ and $I^{\mathrm{OA}}_*$ take values in $[0,\infty]$ (`ℝ≥0∞`), each divergence entering through `ENNReal.ofReal`; for $f,\bar f\in\mathcal M_p$ the divergence $D_\lambda(f\|\bar f)$ is a finite nonnegative real. The parameter $p$ is unconstrained here; the theorems assume $0<p<1$.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), pp. 10–15, §4 (𝒮, Definition 1), §5 ((1), M̄_p(f), (Max-Min), kl), §6 ((2)); Appendix D p. 57 (M_p(σ))

import Mathlib

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-! # §4–§5 (pp. 10–15): display sets, `p`-separable preferences, KL divergences, Chernoff
information.

Conventions. The paper's versions `1, …, K` are `Fin K` (version `m` is `⟨m - 1, _⟩`). A ranking
`σ : Equiv.Perm (Fin K)` sends a version to its rank, **0-based**: `σ X = 0` is the top rank (the
paper's `σ(X) = 1`). -/

/-- The collection `𝒮 = {S ⊆ [K] : |S| ≥ 2}` of display sets (p. 10). -/
abbrev DS (K : ℕ) := {S : Finset (Fin K) // 2 ≤ S.card}

/-- A preference (consumer choice model): `f S X` is the probability `f(X|S)` that a consumer
shown the display set `S` selects version `X` (p. 10). -/
abbrev Pref (K : ℕ) := DS K → Fin K → ℝ

/-- (A-3) Ranking-based preference with respect to the ranking `σ`: for every display set `S` and
distinct `X, X' ∈ S`, `f(X'|S) ≤ f(X|S)` iff `σ(X) < σ(X')`. The paper writes "any `X, X' ∈ S`";
the case `X = X'` is excluded because the right-hand side is then false while the left-hand side
is true (with it, no preference would satisfy (A-3)). -/
def Ranks {K : ℕ} (f : Pref K) (σ : Equiv.Perm (Fin K)) : Prop :=
  ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 → X ≠ X' →
    (f S X' ≤ f S X ↔ σ X < σ X')

/-- (A-4) `p`-separability with respect to `σ`: for every `S` and `X, X' ∈ S` with
`σ(X) < σ(X')`, `f(X'|S) ≤ p · f(X|S)`. -/
def PSep {K : ℕ} (p : ℝ) (f : Pref K) (σ : Equiv.Perm (Fin K)) : Prop :=
  ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 → σ X < σ X' → f S X' ≤ p * f S X

/-- Definition 1 (p. 10): the class `M_p` of `p`-separable preferences, i.e. (A-1)
non-degeneracy, (A-2) probability mass function, and a ranking `σ_f` satisfying (A-3) and (A-4). -/
def Mp {K : ℕ} (p : ℝ) : Set (Pref K) :=
  {f | (∀ (S : DS K) (X : Fin K), (X ∈ S.1 → 0 < f S X) ∧ (X ∉ S.1 → f S X = 0)) ∧
       (∀ S : DS K, ∑ X ∈ S.1, f S X = 1) ∧
       ∃ σ : Equiv.Perm (Fin K), Ranks f σ ∧ PSep p f σ}

/-- `M_p(σ) = {f ∈ M_p : σ_f = σ}` (Appendix D, p. 57). -/
def MpRank {K : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin K)) : Set (Pref K) :=
  {f | f ∈ Mp p ∧ Ranks f σ}

/-- `k` is the top-ranked version of `f`, i.e. `k = σ_f^{-1}(1)`: some ranking satisfying (A-3)
for `f` puts `k` at rank `0` (rank 1 in the paper). -/
def IsTop {K : ℕ} (f : Pref K) (k : Fin K) : Prop :=
  ∃ σ : Equiv.Perm (Fin K), Ranks f σ ∧ (σ k).val = 0

/-- The KL divergence with respect to a display set, (1) p. 13:
`D_S(f₁‖f₂) = ∑_{k ∈ S} f₁(k|S) log (f₁(k|S) / f₂(k|S))`. -/
noncomputable def DS_ {K : ℕ} (f₁ f₂ : Pref K) (S : DS K) : ℝ :=
  ∑ k ∈ S.1, f₁ S k * Real.log (f₁ S k / f₂ S k)

/-- `Δ(𝒮)`, the probability distributions on the display sets. -/
def simplex (K : ℕ) : Set (DS K → ℝ) :=
  {lam | (∀ S, 0 ≤ lam S) ∧ ∑ S, lam S = 1}

/-- The KL divergence with respect to `λ ∈ Δ(𝒮)`, (1) p. 13:
`D_λ(f₁‖f₂) = ∑_{S ∈ 𝒮} λ(S) D_S(f₁‖f₂)`. -/
noncomputable def Dlam {K : ℕ} (lam : DS K → ℝ) (f₁ f₂ : Pref K) : ℝ :=
  ∑ S, lam S * DS_ f₁ f₂ S

/-- The Bernoulli KL divergence (p. 14):
`kl(δ₁, δ₂) = δ₁ log (δ₁/δ₂) + (1 - δ₁) log ((1 - δ₁)/(1 - δ₂))`. -/
noncomputable def kl (x y : ℝ) : ℝ :=
  x * Real.log (x / y) + (1 - x) * Real.log ((1 - x) / (1 - y))

/-- `M̄_p(f)` (p. 13): the preferences in `M_p` whose top-ranked version differs from that of
`f`. -/
def alt {K : ℕ} (p : ℝ) (f : Pref K) : Set (Pref K) :=
  {g | g ∈ Mp p ∧ ∀ k k' : Fin K, IsTop f k → IsTop g k' → k ≠ k'}

/-- Chernoff's information (Max-Min), p. 13:
`I_*(f) = sup_{λ ∈ Δ(𝒮)} inf_{f̄ ∈ M̄_p(f)} D_λ(f‖f̄)`, valued in `[0, ∞]`. -/
noncomputable def Istar {K : ℕ} (p : ℝ) (f : Pref K) : ℝ≥0∞ :=
  ⨆ lam ∈ simplex K, ⨅ g ∈ alt p f, ENNReal.ofReal (Dlam lam f g)

/-- (2), p. 15: `I^OA_* = inf_{f ∈ M_p} I_*(f)`. -/
noncomputable def IOA {K : ℕ} (p : ℝ) : ℝ≥0∞ :=
  ⨅ f ∈ (Mp p : Set (Pref K)), Istar p f

end RobustPrefLearn.MTP


