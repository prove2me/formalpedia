-- Prove2me | Definitions.Def_MenuPricing_Supplement_OnlineLearner
-- name    : MenuPricing_Supplement_OnlineLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:24:42.200515+00:00
-- url     : https://prove2.me/theorems/3870a095-1875-4087-8636-e2d7991f8ea6
-- title:
--   Online learning algorithms (Definition 3), Hedge, Fixed-Share, and comparator classes $\mathcal C_S$
-- statement:
--   An **online learning algorithm** $\mathcal A^{OL}$ on $K$ actions plays weights $w_t\in\triangle[K]$ and has coefficients $q_t\in[0,1]^K$, both functions of the past loss vectors $\ell_1,\dots,\ell_{t-1}$. For a class $\mathcal C\subseteq[K]^T$ of comparator sequences it is **suitable for Algorithm 3** (Definition 3) if for every sequence of loss vectors with $\ell_{t,i}\ge -1$,
--   $$
--   \sum_{t=1}^T\Big(\mathop{\mathbb E}_{i\sim w_t}[\ell_{t,i}] - \ell_{t,i^*_t}\Big) \le \mathrm{Penalty}(\mathcal C,T,K,\eta) + \eta\sum_{t=1}^T \mathop{\mathbb E}_{i\sim w_t}\big[q_{t,i}\ell_{t,i}^2\big]
--   $$
--   for every $(i^*_1,\dots,i^*_T)\in\mathcal C$.
--
--   **Hedge** plays $w_{t,i}\propto\exp(-\eta\sum_{\tau<t}\ell_{\tau,i})$; **Fixed-Share** starts uniform and sets $w_{t+1,i}=(1-\tfrac1T)\tilde w_{t+1,i}+\tfrac1{KT}$, where $\tilde w_{t+1,i}\propto w_{t,i}e^{-\eta\ell_{t,i}}$ is the Hedge update. Both have $q_t\equiv1$. Finally, $\mathcal C_S$ is the class of price sequences in $[0,1]^T$ with at most $S$ switches ($p^*_t\ne p^*_{t+1}$); $\mathcal C_0$ is the class of fixed prices.
--
--   These are the inputs of Algorithm 3 and of Theorem 5.3.
--
--   **Formalization Note** The ranges $w_t\in\triangle[K]$, $q_t\in[0,1]^K$ are the predicate `Valid`; with $\mathcal C$, $T$, $K$, $\eta$ fixed, the penalty function is one number. Rounds and actions are 0-indexed.
-- source:
--   Dai, Lin, Slivkins, The Power of Two Choices in Dynamic Pricing (manuscript, sha256 2dbec470…), Definition 3, p.19 (PDF p.21); §5 Preliminaries, p.18 (PDF p.20); Definition 12, p.71 (PDF p.73)

import Mathlib

namespace MenuPricing.Supplement

open Finset Set

/-- An online learning algorithm `𝒜^OL` on `K` actions (Dai, Lin, Slivkins, manuscript sha256
2dbec470…, Definition 3, p.19): after the loss vectors `ℓ_1, …, ℓ_{t−1}` (a list, oldest first) it
plays the weights `w_t = w [ℓ_1, …, ℓ_{t−1}]` and has second-order coefficients
`q_t = q [ℓ_1, …, ℓ_{t−1}]`; both are functions of the past losses only. -/
structure OnlineLearner (K : ℕ) where
  /-- The weights `w_t ∈ △[K]` after the given losses. -/
  w : List (Fin K → ℝ) → Fin K → ℝ
  /-- The coefficients `q_t ∈ [0, 1]^K` after the given losses. -/
  q : List (Fin K → ℝ) → Fin K → ℝ

namespace OnlineLearner

variable {K : ℕ}

/-- The ranges required by Definition 3 (manuscript sha256 2dbec470…, p.19): `w_t ∈ △[K]` and
`q_t ∈ [0, 1]^K` after every loss history. -/
def Valid (OL : OnlineLearner K) : Prop :=
  ∀ L : List (Fin K → ℝ), (∀ i, 0 ≤ OL.w L i) ∧ ∑ i, OL.w L i = 1 ∧ ∀ i, OL.q L i ∈ Icc (0 : ℝ) 1

/-- The losses `ℓ_1, …, ℓ_{t−1}` before round `t` (0-indexed `t`), oldest first. -/
def lossPrefix {T : ℕ} (ℓ : Fin T → Fin K → ℝ) (t : Fin T) : List (Fin K → ℝ) :=
  List.ofFn fun s : Fin t.val => ℓ ⟨s.val, s.isLt.trans t.isLt⟩

/-- Definition 3 (Online Learning Algorithm) (manuscript sha256 2dbec470…, p.19): `𝒜^OL` is
suitable for Algorithm 3 with the comparator class `𝒞 ⊆ [K]^T`, the parameter `η` and the penalty
`Pen = Penalty(𝒞, T, K, η)` if for every sequence of loss vectors with `ℓ_{t,i} ≥ −1`,
`∑_t (E_{i∼w_t}[ℓ_{t,i}] − ℓ_{t,i*_t}) ≤ Pen + η ∑_t E_{i∼w_t}[q_{t,i} ℓ²_{t,i}]` for every
`(i*_1, …, i*_T) ∈ 𝒞`.

**Formalization Note** `𝒞`, `T`, `K`, `η` are all fixed here, so the penalty function is the single
number `Pen`. Rounds are `Fin T` and actions `Fin K` (0-indexed). -/
def Suitable (OL : OnlineLearner K) (T : ℕ) (𝒞 : Set (Fin T → Fin K)) (η Pen : ℝ) : Prop :=
  ∀ ℓ : Fin T → Fin K → ℝ, (∀ t i, -1 ≤ ℓ t i) → ∀ istar ∈ 𝒞,
    ∑ t, (∑ i, OL.w (lossPrefix ℓ t) i * ℓ t i - ℓ t (istar t)) ≤
      Pen + η * ∑ t, ∑ i, OL.w (lossPrefix ℓ t) i * (OL.q (lossPrefix ℓ t) i * ℓ t i ^ 2)

end OnlineLearner

/-- Hedge [FS97] with learning rate `η` (manuscript sha256 2dbec470…, p.19 and Definition 12, p.71):
`w_{t,i} ∝ exp(−η ∑_{τ<t} ℓ_{τ,i})` (so `w_1` is uniform), and `q_t ≡ 1`. -/
noncomputable def hedge (K : ℕ) (η : ℝ) : OnlineLearner K where
  w L i := Real.exp (-η * (L.map fun ℓ => ℓ i).sum) /
    ∑ j, Real.exp (-η * (L.map fun ℓ => ℓ j).sum)
  q _ _ := 1

/-- One Fixed-Share update (manuscript sha256 2dbec470…, Definition 12, p.71): the Hedge update
`w̃_{t+1,i} = w_{t,i} exp(−η ℓ_{t,i}) / ∑_j w_{t,j} exp(−η ℓ_{t,j})`, mixed with the uniform
distribution at rate `1/T`: `w_{t+1,i} = (1 − 1/T) w̃_{t+1,i} + 1/(KT)`. -/
noncomputable def fixedShareStep (K T : ℕ) (η : ℝ) (w ℓ : Fin K → ℝ) : Fin K → ℝ := fun i =>
  (1 - 1 / (T : ℝ)) * (w i * Real.exp (-η * ℓ i) / ∑ j, w j * Real.exp (-η * ℓ j)) +
    1 / ((K : ℝ) * T)

/-- Fixed-Share [HW98] with horizon `T` and learning rate `η` (manuscript sha256 2dbec470…, p.19
and Definition 12, p.71): start from the uniform `w_1,i = 1/K` and apply `fixedShareStep` once per
loss vector; `q_t ≡ 1`. -/
noncomputable def fixedShare (K T : ℕ) (η : ℝ) : OnlineLearner K where
  w L := L.foldl (fixedShareStep K T η) fun _ => 1 / (K : ℝ)
  q _ _ := 1

/-- The number of switches `#{t | p*_t ≠ p*_{t+1}}` of a sequence (manuscript sha256 2dbec470…,
§5, p.18). -/
noncomputable def numSwitches {T : ℕ} {β : Type} (p : Fin T → β) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin T)).filter fun t =>
    ∃ h : t.val + 1 < T, p t ≠ p ⟨t.val + 1, h⟩).card

/-- The class `𝒞_S` of price sequences in `[0, 1]^T` that switch at most `S` times (manuscript
sha256 2dbec470…, §5, p.18); `𝒞_0` is the class of fixed prices. -/
def switchClass (T S : ℕ) : Set (Fin T → ℝ) :=
  {p | (∀ t, p t ∈ Icc (0 : ℝ) 1) ∧ numSwitches p ≤ S}

end MenuPricing.Supplement


