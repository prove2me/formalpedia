-- Prove2me | Definitions.Def_MallowsChoice_DP_Setting
-- name    : MallowsChoice_DP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:44.162814+00:00
-- url     : https://prove2.me/theorems/23d79162-837c-4f5b-9ac2-700ebe3ded0c
-- title:
--   §2.1–2.2 and §4.1 — Mallows rankings, choice probabilities, repeated insertion, and Algorithm 2
-- statement:
--   Products are $a_1,\ldots,a_n$. A **ranking** assigns each product a distinct position, with a smaller position meaning higher preference. The modal ranking is $a_1\cdots a_n$. The **Kendall–Tau distance** $d(\sigma,\omega)$ counts pairs whose order in $\sigma$ disagrees with this modal ranking. For concentration $\theta\ge 0$, the **Mallows probability** of a ranking is
--
--   $$
--   \lambda_\theta(\sigma)=\frac{\exp(-\theta d(\sigma,\omega))}{\psi_n(\theta)},\qquad
--   \psi_n(\theta)=\sum_\sigma\exp(-\theta d(\sigma,\omega)).
--   $$
--
--   For an offer set $S$ and an offered product $a$, its **choice probability** is the sum of $\lambda_\theta(\sigma)$ over rankings that place $a$ before every other product in $S$. The file also defines Algorithm 1's repeated insertion law and its insertion probabilities
--
--   $$
--   \alpha_{s,i}=\frac{e^{-\theta(i-s)}}{\sum_{k=0}^{i-1}e^{-\theta k}},\qquad
--   \gamma_{s,m}=\sum_{\ell=1}^{s}\alpha_{\ell,m}.
--   $$
--
--   The probability $\pi(i,s,m)$ records that $a_i$ is the first offered product after step $m$ of Algorithm 1 and occupies position $s$. A separate table $\pi_{\mathrm{DP}}(i,s,m)$ is computed solely by Algorithm 2's initial condition and recursions (3)–(4). Separating these two tables makes the dynamic program's correctness a theorem.
--
--   **Formalization Note** Products and ranks use zero-based `Fin n`, whereas $i$ and $s$ in the tables use the paper's one-based indices. The modal ranking is identity after the paper's relabelling. Both tables are zero outside their valid ranges; the dynamic program initializes $\pi_{\mathrm{DP}}(1,1,1)=1$ when $n\ge1$. The Mallows normalizer is the sum over rankings, not the printed closed form. Equation (1), read literally for $a\notin S$, can be positive; the choice-probability theorems therefore compare it with the dynamic program only for $a\in S$.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), §2.1–2.2 and §4.1, pp. 7–8, 16–18

import Mathlib

namespace MallowsChoice.DP

open Finset

/-- The Kendall–Tau distance to the modal ranking `a₁⋯aₙ`: the number of inversions. -/
def kendall {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1)).card

/-- The Mallows normalizer, defined by its sum over all rankings. -/
noncomputable def psi (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), Real.exp (-θ * (kendall σ : ℝ))

/-- The Mallows probability of a ranking, with modal ranking `a₁⋯aₙ`. -/
noncomputable def mallows {n : ℕ} (θ : ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  Real.exp (-θ * (kendall σ : ℝ)) / psi n θ

/-- Equation (1): the weight of rankings putting `a` ahead of every other offered product. -/
noncomputable def choiceProb {n : ℕ} (θ : ℝ) (S : Finset (Fin n)) (a : Fin n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), mallows θ σ *
    (if ∀ b ∈ S, b ≠ a → σ a < σ b then (1 : ℝ) else 0)

/-- Algorithm 1's insertion probability `αₛ,ᵢ`, with paper's one-based indices. -/
noncomputable def alpha (θ : ℝ) (s i : ℕ) : ℝ :=
  if 1 ≤ s ∧ s ≤ i then
    Real.exp (-θ * ((i : ℝ) - (s : ℝ))) /
      ∑ k ∈ range i, Real.exp (-θ * (k : ℝ))
  else 0

/-- The cumulative insertion probability `γₛ,ₘ`; in particular `γ₀,ₘ = 0`. -/
noncomputable def gamma (θ : ℝ) (s m : ℕ) : ℝ :=
  ∑ ℓ ∈ Icc 1 s, alpha θ ℓ m

/-- Insert the new product `aₘ₊₁` at zero-based rank `s`. The old ranks at or after `s`
move up by one. The result is the product-to-rank map of the new ranking. -/
def insertRank {m : ℕ} (σ : Equiv.Perm (Fin m)) (s : Fin (m + 1)) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.lastCases s (fun j : Fin m => s.succAbove (σ j))

/-- The law after `m` steps of Algorithm 1. Its first step inserts `a₁` with probability one. -/
noncomputable def rimProb (θ : ℝ) : (m : ℕ) → Equiv.Perm (Fin m) → ℝ
  | 0, _ => 1
  | m + 1, τ =>
      ∑ σ : Equiv.Perm (Fin m), ∑ s : Fin (m + 1),
        if (∀ j : Fin (m + 1), τ j = insertRank σ s j) then
          rimProb θ m σ * alpha θ (s.val + 1) (m + 1)
        else 0

/-- The probability `π(i,s,m)` after step `m` of Algorithm 1: `aᵢ` is the earliest
offered product among the first `m`, at one-based position `s`. Out-of-range values are zero. -/
noncomputable def piProb {n : ℕ} (θ : ℝ) (S : Finset (Fin n))
    (i s m : ℕ) : ℝ :=
  if hm : m ≤ n then
    if hi : 1 ≤ i ∧ i ≤ m then
      if hs : 1 ≤ s ∧ s ≤ m then
        let a : Fin m := ⟨i - 1, by omega⟩
        ∑ σ : Equiv.Perm (Fin m), rimProb θ m σ *
          (if Fin.castLE hm a ∈ S ∧ (σ a).val + 1 = s ∧
                ∀ b : Fin m, Fin.castLE hm b ∈ S → b ≠ a → σ a < σ b
           then (1 : ℝ) else 0)
      else 0
    else 0
  else 0

/-- Algorithm 2's table `π(i,s,m)`, with one-based indices and the printed recursions
(3)–(4). It is zero outside `1 ≤ i,s ≤ m ≤ n`; its initial entry is `π(1,1,1)=1`. -/
noncomputable def piDPAux {n : ℕ} (θ : ℝ) (S : Finset (Fin n)) :
    (m : ℕ) → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | m + 1, i, s =>
      if m = 0 then
        if 1 ≤ n ∧ i = 1 ∧ s = 1 then 1 else 0
      else if hmn : m < n then
        if 1 ≤ i ∧ i ≤ m + 1 ∧ 1 ≤ s ∧ s ≤ m + 1 then
          if i ≤ m then
            (1 - gamma θ s (m + 1)) * piDPAux θ S m i s +
              (if (⟨m, hmn⟩ : Fin n) ∈ S then (0 : ℝ) else 1) *
                gamma θ (s - 1) (m + 1) * piDPAux θ S m i (s - 1)
          else
            (if (⟨m, hmn⟩ : Fin n) ∈ S then (1 : ℝ) else 0) *
              alpha θ s (m + 1) *
                ∑ j ∈ Icc 1 m, ∑ ℓ ∈ Icc s n, piDPAux θ S m j ℓ
        else 0
      else 0

/-- The entry of Algorithm 2's dynamic program. -/
noncomputable def piDP {n : ℕ} (θ : ℝ) (S : Finset (Fin n))
    (i s m : ℕ) : ℝ := piDPAux θ S m i s

end MallowsChoice.DP


