-- Prove2me | Definitions.Def_PosetMarginals_Chains_Algorithm
-- name    : PosetMarginals_Chains_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:40.485803+00:00
-- url     : https://prove2.me/theorems/159b4b04-3684-4d25-96d2-22f4ef4f82ac
-- title:
--   Algorithm 1 — the maximal-chain marginal construction
-- statement:
--   Algorithm 1 maintains residual element marginals $\rho^k$, chain slacks $\delta^k$, residual chain targets $\pi^k$, and an active family $\mathcal C^k$ of maximal chains. Its current support is $X^k=\{x:\rho^k_x>0\}$. The chains with zero slack generate an order on $X^k$; $S^k$ is its set of minimal elements. The weight $w^k$ is the least of the residual marginals on $S^k$ and the positive-slack chain ratios $\delta^k_C/(|S^k\cap C|-1)$ for chains meeting $S^k$ at least twice.
--
--   The update subtracts $w^k$ from each marginal in $S^k$, reduces every chain slack according to its overlap with $S^k$, and reduces each residual target for a chain meeting $S^k$. A chain remains active exactly when the least point of its intersection with $X^k$ in the original poset belongs to $S^k$. The output assigns the accumulated weights
--   $$\sigma_S=\sum_{k:S^k=S}w^k.$$
--
--   This state machine supplies the precise construction used by Propositions 2–4.
--
--   **Formalization Note** Lean state $k=0$ is paper iteration $1$; state $n$ is after $n$ updates. The additive output is the disclosed interpretation of A7's assignment. The weight is defined as $0$ if the candidate set is empty, which occurs after the stopping condition; statements about live iterations require nonempty support.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, pp. 12–13, Algorithm 1, steps A1–A12 and eq. (9)

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

open Classical

namespace PosetMarginals.Chains

/-- The values before a paper iteration; state `k` is the paper's iteration `k+1`. -/
structure AlgState (α : Type*) where
  ρ : α → ℝ
  δ : Finset α → ℝ
  π : Finset α → ℝ
  chains : Finset (Finset α)
  prevX : Finset α

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The positive marginal support `Xᵏ`. -/
noncomputable def AlgState.X (s : AlgState α) : Finset α :=
  Finset.univ.filter (fun x => 0 < s.ρ x)

/-- The active zero slack chains. -/
noncomputable def AlgState.tight (s : AlgState α) : Finset (Finset α) :=
  s.chains.filter (fun C => s.δ C = 0)

/-- The active positive slack chains. -/
noncomputable def AlgState.slack (s : AlgState α) : Finset (Finset α) :=
  s.chains.filter (fun C => 0 < s.δ C)

/-- Step A6: minimal elements in the generated subposet of step A5. -/
noncomputable def AlgState.S (s : AlgState α) : Finset α :=
  s.X.filter (fun x => ∀ y ∈ s.X, relGen s.tight y x → y = x)

/-- Step A7: minimum of the element and slack-chain bounds. -/
noncomputable def AlgState.w (s : AlgState α) : ℝ :=
  let cands : Finset ℝ := s.S.image s.ρ ∪
    (s.slack.filter (fun C => 2 ≤ (s.S ∩ C).card)).image
      (fun C => s.δ C / (((s.S ∩ C).card : ℝ) - 1))
  if h : cands.Nonempty then cands.min' h else 0

/-- A8, A9 and equation (9), with `prevX` recording the previous support. -/
noncomputable def AlgState.step (s : AlgState α) : AlgState α where
  ρ x := s.ρ x - s.w * (if x ∈ s.S then 1 else 0)
  δ C := s.δ C - (if 2 ≤ (s.S ∩ C).card then s.w * (((s.S ∩ C).card : ℝ) - 1) else 0)
  π C := s.π C - (if (s.S ∩ C).Nonempty then s.w else 0)
  chains := s.chains.filter (fun C =>
    ∃ m ∈ C ∩ s.X, (∀ y ∈ C ∩ s.X, m ≤ y) ∧ m ∈ s.S)
  prevX := s.X

/-- Step A1, including `X⁰ = X`. -/
noncomputable def init (ρ : α → ℝ) (π : Finset α → ℝ) : AlgState α :=
  ⟨ρ, delta ρ π, π, maxChains α, Finset.univ⟩

/-- Repeated application of the algorithm's update. -/
noncomputable def iter (ρ : α → ℝ) (π : Finset α → ℝ) : ℕ → AlgState α
  | 0 => init ρ π
  | k + 1 => (iter ρ π k).step

/-- The additive interpretation of the output assignment in A7, through `n` iterations. -/
noncomputable def output (ρ : α → ℝ) (π : Finset α → ℝ)
    (n : ℕ) (S : Finset α) : ℝ :=
  ∑ k ∈ Finset.range n, if (iter ρ π k).S = S then (iter ρ π k).w else 0

end PosetMarginals.Chains


