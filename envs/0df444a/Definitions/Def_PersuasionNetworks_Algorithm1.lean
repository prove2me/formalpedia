-- Prove2me | Definitions.Def_PersuasionNetworks_Algorithm1
-- name    : PersuasionNetworks_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:36.492459+00:00
-- url     : https://prove2.me/theorems/d149c32f-27d8-43d4-86b8-77b3654c2937
-- title:
--   Algorithm 1: runs and signal maps of the double-interval construction
-- statement:
--   Given a feasible tuple $(p_k,z_k)$ with C1–C4, Algorithm 1 sets $t_i=F^{-1}\bigl(1-\sum_{k\in L_i}p_k\bigr)$ for $i=0,\dots,m$ and treats each block in turn:
--
--   1. if $\bar L_i\cap P=\emptyset$, nothing happens;
--   2. if $\bar L_i\cap P=\{k\}$, then $I_1^k=(t_i,t_{i-1}]$ and $I_2^k=\emptyset$;
--   3. if $\bar L_i\cap P=\{k_1,k_2\}$ with $k_1>k_2$, it finds $t',t''\in[t_i,t_{i-1}]$, $t'\le t''$, with
--   $$
--   F(t')-F(t_i)+F(t_{i-1})-F(t'')=p_{k_1},\qquad
--   \int_{F(t_i)}^{F(t')}F^{-1}(x)\,dx+\int_{F(t'')}^{F(t_{i-1})}F^{-1}(x)\,dx=z_{k_1},
--   $$
--   and sets $I_1^{k_1}=(t_i,t']$, $I_2^{k_1}=(t'',t_{i-1}]$, $I_1^{k_2}=(t',t'']$, $I_2^{k_2}=\emptyset$.
--
--   Finally $t_m$ is added to $I_1^{k}$ for $k=\max P$, and the mechanism sends signal $k$ on $I_1^k\cup I_2^k$. Each signal therefore gets at most two intervals of states.
--
--   This item defines a *run*, the numbers $t',t''$ for each two-signal block, and a *signal map* of a run, a measurable map from states to $\{1,\dots,K\}$ that agrees with the intervals.
--
--   **Formalization Note** Algorithm 1 is a relation because Step S1 says "find", and the equations may have several solutions. The end points are extended reals (footnote 24), and intervals are sets of real numbers. Off the intervals a signal map is free: that set is $\mu$-null but may be nonempty (the claim $[t_m,t_0]\supset\mathcal T$ on p.48 fails when $F$ reaches $1$ before $\sup\mathcal T$), and a mechanism must assign a signal to every state.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Algorithm 1, (9), (10), p.20; footnote 24, p.19

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT

open MeasureTheory

namespace PersuasionNetworks

/-- The threshold `t_i = F⁻¹(1 - ∑_{k ∈ L_i} p_k)` of Step S0 of Algorithm 1, for `L_i = [e]`; `e = 0`
gives `t_0 = F⁻¹(1)`. Candogan, SSRN 3346144 (preprint), Algorithm 1, S0, p.20. -/
noncomputable def thresh (μ : Measure ℝ) (𝒯 : Set ℝ) (p : ℕ → ℝ) (e : ℕ) : EReal :=
  stateQuantile μ 𝒯 (1 - ∑ k ∈ Finset.Icc 1 e, p k)

/-- The set of real numbers in the interval `(a, c]` with end points in `EReal`; see footnote 24 of
Candogan, SSRN 3346144 (preprint), p.19.

**Formalization Note.** The algorithm's intervals are sets of states, so they are sets of real
numbers even when an end point is infinite. -/
def extIoc (a c : EReal) : Set ℝ :=
  {t | a < (t : EReal) ∧ (t : EReal) ≤ c}

/-- `(t', t'')` solves the system of Step S1 of Algorithm 1 for the block `(e', e)`, whose signal with
the larger index is `k₁`: `t', t'' ∈ [t_i, t_{i-1}]`, `t' ≤ t''`,
(9) `F(t') - F(t_i) + F(t_{i-1}) - F(t'') = p_{k₁}`, and
(10) `∫_{F(t_i)}^{F(t')} F⁻¹ + ∫_{F(t'')}^{F(t_{i-1})} F⁻¹ = z_{k₁}`.
Candogan, SSRN 3346144 (preprint), Algorithm 1, S1, (9)–(10), p.20.

**Formalization Note.** `t'` and `t''` live in `EReal` since `t_i` and `t_{i-1}` may be infinite; `F`
is extended by `extCdf`. -/
def SolvesS1 (μ : Measure ℝ) (𝒯 : Set ℝ) (p z : ℕ → ℝ) (e' e k₁ : ℕ) (t' t'' : EReal) : Prop :=
  thresh μ 𝒯 p e ≤ t' ∧ t' ≤ t'' ∧ t'' ≤ thresh μ 𝒯 p e' ∧
    extCdf μ t' - extCdf μ (thresh μ 𝒯 p e) + extCdf μ (thresh μ 𝒯 p e') - extCdf μ t'' = p k₁ ∧
    (∫ x in (extCdf μ (thresh μ 𝒯 p e))..(extCdf μ t'), (stateQuantile μ 𝒯 x).toReal) +
        (∫ x in (extCdf μ t'')..(extCdf μ (thresh μ 𝒯 p e')), (stateQuantile μ 𝒯 x).toReal) =
      z k₁

/-- A **run of Algorithm 1** on `(p, z)`: for each `i ∈ [m]` with `L̄_i ∩ P = {k₁, k₂}` and `k₁ > k₂`,
the numbers `t'(e)`, `t''(e)`, indexed by the block's right end `e`, solve (9)–(10). Candogan, SSRN
3346144 (preprint), Algorithm 1, S1, p.20.

**Formalization Note.** Algorithm 1 is a relation and not a function, since Step S1 says "find
`t', t''`" and the system may have several solutions. The other steps are determined by the data.
The values of `t'`, `t''` at other `e` are not used. -/
def IsAlgorithm1Run (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) (t' t'' : ℕ → EReal) :
    Prop :=
  ∀ e' e, IsBlock μ 𝒯 K p z e' e → ∀ k₁ k₂, active p e' e = {k₁, k₂} → k₂ < k₁ →
    SolvesS1 μ 𝒯 p z e' e k₁ (t' e) (t'' e)

/-- `f` is a **signal map of the run** `(t', t'')`: Step S3 sends the state `t` to the signal `k` for
`t ∈ I₁ᵏ ∪ I₂ᵏ`, with the intervals of Steps S1 and S2:

* if `L̄_i ∩ P = {k}`, then `I₁ᵏ = (t_i, t_{i-1}]`;
* if `L̄_i ∩ P = {k₁, k₂}` with `k₁ > k₂`, then `I₁^{k₁} = (t_i, t']`, `I₂^{k₁} = (t'', t_{i-1}]`, and
  `I₁^{k₂} = (t', t'']`;
* the point `t_m` is added to `I₁ᵏ` for `k = max P`, when `t_m` is a real number.

Candogan, SSRN 3346144 (preprint), Algorithm 1, S1–S3, p.20.

**Formalization Note.** A mechanism must assign a signal to every state, while the intervals may
omit a `μ`-null set of `𝒯` (when `F` reaches `1` before `sup 𝒯`, the claim `[t_m, t_0] ⊃ 𝒯` of p.48
fails). So `f` is free outside the intervals, apart from taking values in `{1, …, K}`, and the
theorems of this mission hold for every such completion. `t_m = F⁻¹(1 - ∑_{k ≤ K} p_k)` since
`L_m = [K]` under C1. -/
structure IsSignalMap (μ : Measure ℝ) (𝒯 : Set ℝ) (K : ℕ) (p z : ℕ → ℝ) (t' t'' : ℕ → EReal)
    (f : ℝ → ℕ) : Prop where
  measurable : Measurable f
  mem : ∀ t, f t ∈ Finset.Icc 1 K
  single : ∀ e' e, IsBlock μ 𝒯 K p z e' e → ∀ k, active p e' e = {k} →
    ∀ t ∈ extIoc (thresh μ 𝒯 p e) (thresh μ 𝒯 p e'), f t = k
  pair_outer : ∀ e' e, IsBlock μ 𝒯 K p z e' e → ∀ k₁ k₂, active p e' e = {k₁, k₂} → k₂ < k₁ →
    ∀ t ∈ extIoc (thresh μ 𝒯 p e) (t' e) ∪ extIoc (t'' e) (thresh μ 𝒯 p e'), f t = k₁
  pair_inner : ∀ e' e, IsBlock μ 𝒯 K p z e' e → ∀ k₁ k₂, active p e' e = {k₁, k₂} → k₂ < k₁ →
    ∀ t ∈ extIoc (t' e) (t'' e), f t = k₂
  last : ∀ k ∈ Finset.Icc 1 K, 0 < p k → (∀ j ∈ Finset.Icc 1 K, 0 < p j → j ≤ k) →
    ∀ t : ℝ, (t : EReal) = thresh μ 𝒯 p K → f t = k

end PersuasionNetworks


