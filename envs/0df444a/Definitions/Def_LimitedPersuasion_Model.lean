-- Prove2me | Definitions.Def_LimitedPersuasion_Model
-- name    : LimitedPersuasion_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:00.536987+00:00
-- url     : https://prove2.me/theorems/d50af8fb-bf3c-4973-b902-dfcc8310f6eb
-- title:
--   Signaling with $k$ limited messages — instances, schemes, best response with sender-favourable ties, $u_S$, $\varrho_E$, direct persuasive and symmetric schemes
-- statement:
--   This module defines the persuasion model of §2 and the symmetric schemes of §3.1 of the paper.
--
--   1. **Instance** (§2, p.4). A receiver $R$ chooses one of $n$ actions $[n]$. Action $i$ has a type $\theta_i$ from a finite type set $T$; the state of nature $\boldsymbol\theta=(\theta_1,\dots,\theta_n)$ is drawn with probability $q_{\boldsymbol\theta}\ge 0$, $\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}=1$. A type $t$ carries the value pair $(\varrho(t),\xi(t))$: $\varrho(t)$ is the receiver's and $\xi(t)$ the sender's value of taking an action of type $t$. The values are arbitrary reals.
--   2. **Symmetric instance** (p.5). $q_{\boldsymbol\theta}=q_{\boldsymbol\theta'}$ whenever $\boldsymbol\theta'$ is a permutation of $\boldsymbol\theta$.
--   3. **Distinct types** (p.5). Every state of positive probability assigns pairwise distinct types to the $n$ actions.
--   4. **Signaling scheme with $k$ signals** (p.4). $\varphi(\boldsymbol\theta,\sigma)\ge0$ is the probability of sending signal $\sigma\in[k]$ in state $\boldsymbol\theta$, with $\sum_\sigma\varphi(\boldsymbol\theta,\sigma)=1$.
--   5. **Joint utilities.** For signal $\sigma$ and action $i$,
--   $$w_\sigma(i)=\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\,\varphi(\boldsymbol\theta,\sigma)\,\varrho(\theta_i),\qquad v_\sigma(i)=\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\,\varphi(\boldsymbol\theta,\sigma)\,\xi(\theta_i),$$
--   i.e. $\Pr[\sigma]$ times the conditional expected utility of $R$, resp. $S$, from action $i$ given $\sigma$.
--   6. **Best response and utilities** (pp.4–5). The receiver's best responses to $\sigma$ are $BR(\sigma)=\arg\max_i w_\sigma(i)$; ties are broken in favour of the sender, so
--   $$u_S(\varphi)=\sum_\sigma\max_{i\in BR(\sigma)}v_\sigma(i),\qquad u_R(\varphi)=\sum_\sigma\max_i w_\sigma(i).$$
--   A scheme is **optimal** if no $k$-signal scheme gives the sender a larger $u_S$.
--   7. **Direct and persuasive** (p.5). A direct scheme uses signal $\sigma$ to recommend action $a(\sigma)$; it is persuasive if $w_\sigma(a(\sigma))\ge w_\sigma(i)$ for all $\sigma$ and $i$. When the receiver follows the recommendation the utilities are $\sum_\sigma v_\sigma(a(\sigma))$ and $\sum_\sigma w_\sigma(a(\sigma))$.
--   8. **$\varrho_E$** (p.5). $\varrho_E=\max_{i\in[n]}\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\,\varrho(\theta_i)$, the best expected utility of any fixed action for $R$.
--   9. **Symmetric scheme** (p.7). A direct scheme in which signal $j\in[k]$ recommends action $j$, such that the conditional distribution of types given the signal is (a) the same for each recommended action, (b) the same for each non-recommended action in $[k]$, no matter which other action is recommended, and (c) the same for each action in $[n]\setminus[k]$, no matter which action is recommended.
--
--   These are the objects in which Lemmas 1–4 and Theorem 1 are stated.
--
--   **Formalization Note** All actions share one finite type set $T$, so a state is a function $[n]\to T$ and the paper's $\Theta\subseteq\Theta_1\times\cdots\times\Theta_n$ is the support of $q$. Signals are $\mathrm{Fin}\,k$. The quantities $w,v$ are not divided by $\Pr[\sigma]$, so null signals need no division and impose no obedience constraint. The paper's further "fixed tie-breaking rule" among sender-optimal best responses does not affect $u_S$. The equalities of conditional distributions in a symmetric scheme are cross-multiplied: $\Pr[\theta_i=t,\sigma=j]\Pr[\sigma=j']=\Pr[\theta_{i'}=t,\sigma=j']\Pr[\sigma=j]$. Distinct types are required only on the support of $q$.
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, §2 "Model", pp.4–5 (signaling scheme, best response with sender tie-breaking, direct and persuasive, ϱ_E, symmetric instances, distinct types); §3.1, p.7 (symmetric scheme)

import Mathlib

namespace LimitedPersuasion

/-- **Instance of signaling with limited messages**, Gradwohl–Hahn–Hoefer–Smorodinsky,
*Algorithms for Persuasion with Limited Communication*, arXiv:2007.12489v2, §2 "Model", p.4.

The receiver has `n` actions `Fin n`; each action `i` has a type `θ i` from a finite type set,
the state of nature `θ = (θ₁, …, θₙ)` is drawn with probability `q θ`, and a type `t` carries the
value pair `(ρ t, ξ t)`: `ρ t` is the receiver's value and `ξ t` the sender's value of an action of
type `t`.

**Formalization Note.** All actions share one finite type set `T` (each paper set `Θᵢ` embeds in
it), so a state is a function `Fin n → T` and the paper's `Θ ⊆ Θ₁ × ⋯ × Θₙ` is the support of
`q`. The prior is a weight function `q` with `q ≥ 0` and `∑ θ, q θ = 1`. The values `ρ, ξ` are
arbitrary reals. -/
structure Instance (T : Type*) [Fintype T] (n : ℕ) where
  /-- the prior probability `q_θ` of the state `θ` -/
  q : (Fin n → T) → ℝ
  q_nonneg : ∀ θ, 0 ≤ q θ
  q_sum_one : ∑ θ, q θ = 1
  /-- the receiver's value `ϱ(t)` of an action of type `t` -/
  ρ : T → ℝ
  /-- the sender's value `ξ(t)` of an action of type `t` -/
  ξ : T → ℝ

variable {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ}

/-- **Symmetric instance**, arXiv:2007.12489v2, §2 "Symmetric Instances", p.5:
`q_θ = q_θ'` whenever `θ'` is any permutation of `θ`. -/
def Instance.IsSymmetric (I : Instance T n) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (θ : Fin n → T), I.q (θ ∘ π) = I.q θ

/-- **All types are distinct**, arXiv:2007.12489v2, §2, p.5 ("For simplicity, we will assume
throughout that all types are indeed distinct"): every state of positive probability assigns
pairwise distinct types to the `n` actions.

**Formalization Note.** Required only on the support of `q`; states of probability zero are
unconstrained. -/
def Instance.DistinctTypes (I : Instance T n) : Prop :=
  ∀ θ : Fin n → T, I.q θ ≠ 0 → Function.Injective θ

/-- **Signaling scheme with `k` signals**, arXiv:2007.12489v2, §2, p.4: `φ θ σ` is the probability
that in state `θ` the scheme sends signal `σ`.

**Formalization Note.** Signals are `Fin k`; a scheme is a nonnegative function with
`∑ σ, φ θ σ = 1` for every state `θ` (including states of probability zero). -/
def IsScheme (φ : (Fin n → T) → Fin k → ℝ) : Prop :=
  (∀ θ σ, 0 ≤ φ θ σ) ∧ ∀ θ, ∑ σ, φ θ σ = 1

/-- `w φ σ i = ∑_θ q_θ φ(θ, σ) ϱ(θᵢ)`: the receiver's utility of action `i` jointly with signal
`σ`, i.e. `Pr[σ] · E[ϱ(θᵢ) | σ]` (arXiv:2007.12489v2, §2, p.4).

**Formalization Note.** Unnormalized (not divided by `Pr[σ]`), so a null signal gives `0` and no
division occurs. -/
noncomputable def Instance.w (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (σ : Fin k)
    (i : Fin n) : ℝ :=
  ∑ θ, I.q θ * φ θ σ * I.ρ (θ i)

/-- `v φ σ i = ∑_θ q_θ φ(θ, σ) ξ(θᵢ)`: the sender's utility of action `i` jointly with signal `σ`,
i.e. `Pr[σ] · E[ξ(θᵢ) | σ]` (arXiv:2007.12489v2, §2, p.4). Unnormalized, as `w`. -/
noncomputable def Instance.v (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (σ : Fin k)
    (i : Fin n) : ℝ :=
  ∑ θ, I.q θ * φ θ σ * I.ξ (θ i)

/-- The receiver's best responses to signal `σ` (arXiv:2007.12489v2, §2, p.4): the actions with
optimal expected utility conditioned on observing `σ`.

**Formalization Note.** Compared through the unnormalized `w`, which is `Pr[σ]` times the
conditional expectation; for a null signal every action is a best response. -/
noncomputable def Instance.BR (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (σ : Fin k) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j, I.w φ σ j ≤ I.w φ σ i

omit [DecidableEq T] in
/-- The receiver always has a best response (`n ≥ 1`). -/
theorem Instance.BR_nonempty [NeZero n] (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ)
    (σ : Fin k) : (I.BR φ σ).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (I.w φ σ) Finset.univ_nonempty
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩

/-- **The sender's expected utility `u_S(φ)`** of a scheme, arXiv:2007.12489v2, §2, pp.4–5: the
receiver best responds to every signal and breaks ties in favor of the sender, so signal `σ`
contributes the largest sender utility among the receiver's best responses.

**Formalization Note.** `u_S(φ) = ∑_σ max_{i ∈ BR(σ)} v φ σ i`. The paper's further "fixed
tie-breaking rule" among sender-optimal best responses does not change this value. -/
noncomputable def Instance.uS [NeZero n] (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) : ℝ :=
  ∑ σ, (I.BR φ σ).sup' (I.BR_nonempty φ σ) (I.v φ σ)

/-- **The receiver's expected utility `u_R(φ)`** of a scheme under best response,
arXiv:2007.12489v2, §2, p.4: `∑_σ max_i w φ σ i`. -/
noncomputable def Instance.uR [NeZero n] (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) : ℝ :=
  ∑ σ, Finset.univ.sup' Finset.univ_nonempty (I.w φ σ)

/-- **Optimal scheme with `k` signals**, arXiv:2007.12489v2, §2, pp.4–5: `φ` is a `k`-signal
scheme and no `k`-signal scheme gives the sender a larger expected utility `u_S` (best response
with sender-favourable tie-breaking on both sides). -/
def Instance.IsOptimal [NeZero n] (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) : Prop :=
  IsScheme φ ∧ ∀ ψ : (Fin n → T) → Fin k → ℝ, IsScheme ψ → I.uS ψ ≤ I.uS φ

/-- **Persuasive direct scheme**, arXiv:2007.12489v2, §2, p.5: the scheme uses signal `σ` to
recommend action `a σ`, and the receiver has no incentive to deviate from the recommended action:
for every signal `σ` and action `i`, `E[ϱ(θ_{a σ}) | σ] ≥ E[ϱ(θ_i) | σ]`.

**Formalization Note.** Stated with the unnormalized `w` (multiplied through by `Pr[σ]`), so null
signals impose nothing. -/
def Instance.Persuasive (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (a : Fin k → Fin n) :
    Prop :=
  ∀ σ i, I.w φ σ i ≤ I.w φ σ (a σ)

/-- **Sender utility of a direct scheme** when the receiver follows the recommendation `a`:
`∑_σ v φ σ (a σ)` (the `u_S(φ)` of a direct scheme in §3, arXiv:2007.12489v2, pp.6–8). -/
noncomputable def Instance.followS (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ)
    (a : Fin k → Fin n) : ℝ :=
  ∑ σ, I.v φ σ (a σ)

/-- **Receiver utility of a direct scheme** when the receiver follows the recommendation `a`:
`∑_σ w φ σ (a σ)` (the `u_R(φ)` of a direct scheme in §3, arXiv:2007.12489v2, pp.6–8). -/
noncomputable def Instance.followR (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ)
    (a : Fin k → Fin n) : ℝ :=
  ∑ σ, I.w φ σ (a σ)

/-- **`ϱ_E`**, arXiv:2007.12489v2, §2, p.5: the best expected utility of any fixed action for the
receiver, `ϱ_E = max_{i ∈ [n]} ∑_θ q_θ · ϱ(θᵢ)`. -/
noncomputable def Instance.rhoE [NeZero n] (I : Instance T n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin n => ∑ θ, I.q θ * I.ρ (θ i)

/-- `J φ t i σ = Pr[θᵢ = t, σ]`, the joint probability that action `i` has type `t` and the
scheme sends `σ` (arXiv:2007.12489v2, §3.1, p.7). -/
noncomputable def Instance.J (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (t : T) (i : Fin n)
    (σ : Fin k) : ℝ :=
  ∑ θ, I.q θ * φ θ σ * (if θ i = t then 1 else 0)

/-- `Pσ φ σ = Pr[σ]`, the probability that the scheme sends `σ`. -/
noncomputable def Instance.Pσ (I : Instance T n) (φ : (Fin n → T) → Fin k → ℝ) (σ : Fin k) : ℝ :=
  ∑ θ, I.q θ * φ θ σ

/-- **Symmetric scheme**, arXiv:2007.12489v2, §3.1, p.7: a direct scheme that recommends with
each signal a distinct action in `[k]` (signal `j` recommends action `j`), such that

1. the conditional distribution over types is the same for each recommended action:
   `Pr[θ_j = t | σ = j] = Pr[θ_{j'} = t | σ = j']`;
2. the conditional distribution over types is the same for each non-recommended action in `[k]`,
   no matter which other action is recommended: `Pr[θ_i = t | σ = j] = Pr[θ_{i'} = t | σ = j']`
   for `i ≠ j`, `i' ≠ j'` in `[k]`;
3. the conditional distribution over types is the same for each action in `[n] ∖ [k]`, no matter
   which action is recommended: `Pr[θ_i = t | σ = j] = Pr[θ_{i'} = t | σ = j']` for
   `i, i' ∉ [k]`.

**Formalization Note.** Action `j ∈ [k]` is `Fin.castLE hkn j`, and `[n] ∖ [k]` is
`{i : k ≤ i}`. Each equality of conditional probabilities is cross-multiplied,
`Pr[θ_i = t, σ = j] · Pr[σ = j'] = Pr[θ_{i'} = t, σ = j'] · Pr[σ = j]`, so it says nothing
about null signals and involves no division. -/
def Instance.IsSymmetricScheme (I : Instance T n) (hkn : k ≤ n)
    (φ : (Fin n → T) → Fin k → ℝ) : Prop :=
  IsScheme φ ∧
  (∀ (t : T) (j j' : Fin k),
    I.J φ t (Fin.castLE hkn j) j * I.Pσ φ j' = I.J φ t (Fin.castLE hkn j') j' * I.Pσ φ j) ∧
  (∀ (t : T) (i j i' j' : Fin k), i ≠ j → i' ≠ j' →
    I.J φ t (Fin.castLE hkn i) j * I.Pσ φ j' = I.J φ t (Fin.castLE hkn i') j' * I.Pσ φ j) ∧
  (∀ (t : T) (i i' : Fin n) (j j' : Fin k), k ≤ (i : ℕ) → k ≤ (i' : ℕ) →
    I.J φ t i j * I.Pσ φ j' = I.J φ t i' j' * I.Pσ φ j)

end LimitedPersuasion


