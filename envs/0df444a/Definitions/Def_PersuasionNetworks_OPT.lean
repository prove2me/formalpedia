-- Prove2me | Definitions.Def_PersuasionNetworks_OPT
-- name    : PersuasionNetworks_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:54.503713+00:00
-- url     : https://prove2.me/theorems/f2c05749-d027-44c5-b48c-cb0a11786aa8
-- title:
--   The convex program (OPT), conditions C1–C4 and the auxiliary program (19)
-- statement:
--   The program (OPT) has variables $(p_k,z_k)_{k\in\mathcal S}$, $\mathcal S=\{1,\dots,K\}$:
--   $$
--   \max\ \sum_{k\in\mathcal S}p_kr_k
--   \quad\text{s.t.}\quad
--   \sum_{k\in L}z_k\le\int_{1-\sum_{k\in L}p_k}^{1}F^{-1}(x)\,dx\ \ (L=[k'],\ k'\in\mathcal S),\quad
--   b_kp_k\le z_k,\quad
--   \sum_{k\in\mathcal S}p_k=1,\quad
--   p_k\ge0 .
--   $$
--   By footnote 17, the constraint $b_kp_k\le z_k$ is omitted for $k=K$ when $b_K=-\infty$.
--
--   Let $P=\{k\mid p_k>0\}$, let $L_1\subsetneq\dots\subsetneq L_m$ be the sets $[k']$ at which the first constraint binds, $L_0=\emptyset$, and $\bar L_i=L_i\setminus L_{i-1}$. The conditions are:
--
--   1. **C1**: $L_m=\mathcal S$;
--   2. **C2**: $z_k=0$ for $k\notin P$;
--   3. **C3**: $|\bar L_i\cap P|\le2$ for all $i$;
--   4. **C4**: $\sum_{k\in L_{i-1}\cup\{\ell\}}z_k<\int_{1-\sum_{k\in L_{i-1}\cup\{\ell\}}p_k}^{1}F^{-1}(x)\,dx$ for all $\ell\in\bar L_i\cap P$ and all $i$ with $|\bar L_i\cap P|=2$.
--
--   The item also defines the auxiliary linear program (19) on a block $\bar L_i$, with data $\gamma_i=\int_{1-\sum_{L_i}p^\star_k}^{1-\sum_{L_{i-1}}p^\star_k}F^{-1}(x)\,dx$ and $\beta_i=\sum_{\bar L_i}p^\star_k$, and the homotopy (20) between a solution and an optimal solution of (19).
--
--   (OPT) is the finite-dimensional relaxation of the designer's infinite-dimensional problem, and C1–C4 are the structure that makes the relaxation tight.
--
--   **Formalization Note** The index $i\in[m]$ is represented by a pair of consecutive binding indices $(e',e)$: $L_{i-1}=[e']$, $L_i=[e]$, $\bar L_i=\{e'+1,\dots,e\}$, with $e'=0$ for $i=1$. The omission of footnote 17 is a guard $b_k\neq-\infty$ on a real product, and it carries over to (19). The variables are functions on $\mathbb N$, read only on $\{1,\dots,K\}$.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, (OPT) and footnote 17, p.17; C1–C4, p.18; (19), p.43; (20), p.44

import Mathlib
import Definitions.Def_PersuasionNetworks_Quantile

open MeasureTheory

namespace PersuasionNetworks

/-- The objective `∑_{k ∈ 𝒮} p_k r_k` of (OPT), for `𝒮 = {1, …, K}`. Candogan, SSRN 3346144
(preprint), (OPT), p.17. -/
def objective (K : ℕ) (r p : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, p k * r k

/-- The **first constraint** of (OPT): `∑_{k ∈ L} z_k ≤ ∫_{1 - ∑_{k ∈ L} p_k}^{1} F⁻¹(x) dx` for all
`k' ∈ 𝒮` and `L = [k']`. Candogan, SSRN 3346144 (preprint), (OPT), p.17. -/
def FirstConstraint (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) : Prop :=
  ∀ k' ∈ Finset.Icc 1 K,
    ∑ k ∈ Finset.Icc 1 k', z k ≤ g μ 𝒯 (∑ k ∈ Finset.Icc 1 k', p k)

/-- The **last three constraints** of (OPT): `b_k p_k ≤ z_k`, `∑_k p_k = 1`, and `p_k ≥ 0`.
Candogan, SSRN 3346144 (preprint), (OPT), p.17, and footnote 17.

**Formalization Note.** Footnote 17: "when `b_K = -∞`, we omit the second constraint for `k = K`".
This is the guard `b k ≠ ⊥`, and the product is computed in `ℝ`, never in `EReal`. -/
structure LastConstraints (K : ℕ) (b : ℕ → EReal) (p z : ℕ → ℝ) : Prop where
  lower : ∀ k ∈ Finset.Icc 1 K, b k ≠ ⊥ → (b k).toReal * p k ≤ z k
  sum_eq_one : ∑ k ∈ Finset.Icc 1 K, p k = 1
  nonneg : ∀ k ∈ Finset.Icc 1 K, 0 ≤ p k

/-- **Feasibility** in (OPT). Candogan, SSRN 3346144 (preprint), (OPT), p.17.

**Formalization Note.** `p` and `z` are functions on `ℕ`; only their values on `{1, …, K}` are
constrained. -/
def IsFeasible (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (p z : ℕ → ℝ) : Prop :=
  FirstConstraint μ 𝒯 K p z ∧ LastConstraints K b p z

/-- An **optimal solution** of (OPT). Candogan, SSRN 3346144 (preprint), (OPT), p.17. -/
def IsOptimal (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r p z : ℕ → ℝ) : Prop :=
  IsFeasible μ 𝒯 K b p z ∧
    ∀ p' z', IsFeasible μ 𝒯 K b p' z' → objective K r p' ≤ objective K r p

/-- The first constraint of (OPT) is **binding** at `L = [k']`. Candogan, SSRN 3346144 (preprint),
§3.1, p.18. -/
def IsBinding (μ : Measure ℝ) (𝒯 : Set ℝ) (p z : ℕ → ℝ) (k' : ℕ) : Prop :=
  ∑ k ∈ Finset.Icc 1 k', z k = g μ 𝒯 (∑ k ∈ Finset.Icc 1 k', p k)

/-- `(e', e)` is a pair of **consecutive binding indices**: on p.18 the sets `L_1 ⊊ ⋯ ⊊ L_m` are the
sets `[k']` at which the first constraint of (OPT) binds, and `L_0 = ∅`. Writing `L_i = [e_i]` with
`e_0 = 0`, this says `(e', e) = (e_{i-1}, e_i)` for some `i ∈ [m]`, so that
`L̄_i = L_i \ L_{i-1} = {e' + 1, …, e}`. Candogan, SSRN 3346144 (preprint), §3.1, p.18.

**Formalization Note.** A block stands for the index `i ∈ [m]`, and each `L_i` is represented by its
largest element. -/
structure IsBlock (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) (e' e : ℕ) : Prop where
  mem : e ∈ Finset.Icc 1 K
  binding : IsBinding μ 𝒯 p z e
  prev : e' = 0 ∨ (e' ∈ Finset.Icc 1 K ∧ IsBinding μ 𝒯 p z e')
  lt : e' < e
  no_between : ∀ j, e' < j → j < e → ¬ IsBinding μ 𝒯 p z j

open scoped Classical in
/-- The set `L̄_i ∩ P`, where `L̄_i = {e' + 1, …, e}` and `P = {k | p_k > 0}`. Candogan, SSRN 3346144
(preprint), §3.1, p.18. -/
noncomputable def active (p : ℕ → ℝ) (e' e : ℕ) : Finset ℕ :=
  (Finset.Ioc e' e).filter (fun k => 0 < p k)

/-- **C1**: `L_m = 𝒮`, i.e. the first constraint binds at `K`. Candogan, SSRN 3346144 (preprint),
p.18. -/
def C1 (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) : Prop :=
  IsBinding μ 𝒯 p z K

/-- **C2**: `z_k = 0` for `k ∉ P`. Candogan, SSRN 3346144 (preprint), p.18. -/
def C2 (K : ℕ) (p z : ℕ → ℝ) : Prop :=
  ∀ k ∈ Finset.Icc 1 K, ¬ 0 < p k → z k = 0

/-- **C3**: `L̄_i ∩ P` has cardinality at most `2` for all `i ∈ [m]`. Candogan, SSRN 3346144
(preprint), p.18. -/
def C3 (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) : Prop :=
  ∀ e' e, IsBlock μ 𝒯 K p z e' e → (active p e' e).card ≤ 2

/-- **C4**: `∑_{k ∈ L_{i-1} ∪ {ℓ}} z_k < ∫_{1 - ∑_{k ∈ L_{i-1} ∪ {ℓ}} p_k}^{1} F⁻¹(x) dx` for all
`ℓ ∈ L̄_i ∩ P` and `i ∈ [m]` such that `|L̄_i ∩ P| = 2`. Candogan, SSRN 3346144 (preprint), p.18.

**Formalization Note.** `L_{i-1} ∪ {ℓ}` need not be an initial segment, so C4 is not an instance of
the first constraint of (OPT). -/
def C4 (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) : Prop :=
  ∀ e' e, IsBlock μ 𝒯 K p z e' e → (active p e' e).card = 2 → ∀ ℓ ∈ active p e' e,
    ∑ k ∈ insert ℓ (Finset.Icc 1 e'), z k < g μ 𝒯 (∑ k ∈ insert ℓ (Finset.Icc 1 e'), p k)

/-- Conditions **C1–C4** together. Candogan, SSRN 3346144 (preprint), p.18. -/
structure SatisfiesC (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) : Prop where
  c1 : C1 μ 𝒯 K p z
  c2 : C2 K p z
  c3 : C3 μ 𝒯 K p z
  c4 : C4 μ 𝒯 K p z

/-- `γ_i = ∫_{1 - ∑_{k ∈ L_i} p_k}^{1 - ∑_{k ∈ L_{i-1}} p_k} F⁻¹(x) dx`, for the block `(e', e)`.
Candogan, SSRN 3346144 (preprint), Proof of Lemma 4, "Proof C3 holds", p.43. -/
noncomputable def gammaBlock (μ : Measure ℝ) (𝒯 : Set ℝ) (p : ℕ → ℝ) (e' e : ℕ) : ℝ :=
  ∫ x in (1 - ∑ k ∈ Finset.Icc 1 e, p k)..(1 - ∑ k ∈ Finset.Icc 1 e', p k),
    (stateQuantile μ 𝒯 x).toReal

/-- **Feasibility in the auxiliary program (19)** for the block `(e', e)`, built from the solution
`pS` (the paper's `p⋆`, which supplies `γ_i`, `β_i = ∑_{k ∈ L̄_i} p⋆_k` and `P`). Candogan, SSRN
3346144 (preprint), Proof of Lemma 4, "Proof C3 holds", (19), p.43.

**Formalization Note.** The convention of footnote 17 carries over to the second constraint: it is
omitted at `k = K` when `b_K = -∞` (the proof on p.45 treats it so implicitly, since (19) inherits it
from (OPT)). `p` and `z` are read only on `L̄_i`. -/
structure IsAuxFeasible (μ : Measure ℝ) (𝒯 : Set ℝ) (b : ℕ → EReal) (pS : ℕ → ℝ) (e' e : ℕ)
    (p z : ℕ → ℝ) : Prop where
  sum_z : ∑ k ∈ Finset.Ioc e' e, z k = gammaBlock μ 𝒯 pS e' e
  lower : ∀ k ∈ Finset.Ioc e' e, 0 < pS k → b k ≠ ⊥ → (b k).toReal * p k ≤ z k
  z_zero : ∀ k ∈ Finset.Ioc e' e, ¬ 0 < pS k → z k = 0
  sum_p : ∑ k ∈ Finset.Ioc e' e, p k = ∑ k ∈ Finset.Ioc e' e, pS k
  nonneg : ∀ k ∈ Finset.Ioc e' e, 0 < pS k → 0 ≤ p k
  p_zero : ∀ k ∈ Finset.Ioc e' e, ¬ 0 < pS k → p k = 0

/-- An **optimal solution of the auxiliary program (19)**: it maximizes `∑_{k ∈ L̄_i} p_k r_k`.
Candogan, SSRN 3346144 (preprint), Proof of Lemma 4, "Proof C3 holds", (19), p.43. -/
def IsAuxOptimal (μ : Measure ℝ) (𝒯 : Set ℝ) (b : ℕ → EReal) (r pS : ℕ → ℝ) (e' e : ℕ)
    (p z : ℕ → ℝ) : Prop :=
  IsAuxFeasible μ 𝒯 b pS e' e p z ∧
    ∀ p' z', IsAuxFeasible μ 𝒯 b pS e' e p' z' →
      ∑ k ∈ Finset.Ioc e' e, p' k * r k ≤ ∑ k ∈ Finset.Ioc e' e, p k * r k

open scoped Classical in
/-- The homotopy (20): `x̂_k = α x̄_k + (1 - α) x⋆_k` for `k ∈ L̄_j = {e' + 1, …, e}`, and `x̂_k = x⋆_k`
otherwise. It is used both for `p̂` and for `ẑ`. Candogan, SSRN 3346144 (preprint), Proof of Lemma 4,
(20), p.44. -/
noncomputable def blockMix (e' e : ℕ) (α : ℝ) (xBar xS : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ∈ Finset.Ioc e' e then α * xBar k + (1 - α) * xS k else xS k

end PersuasionNetworks


