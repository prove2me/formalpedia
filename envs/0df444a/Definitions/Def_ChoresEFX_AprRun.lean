-- Prove2me | Definitions.Def_ChoresEFX_AprRun
-- name    : ChoresEFX_AprRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:26.388202+00:00
-- url     : https://prove2.me/theorems/a8fc3479-444e-4411-8a16-01afaf0bf051
-- title:
--   Adaptive Packet Reallocation: the hypotheses of Lemma 3.6 and the run relation of Algorithm 4
-- statement:
--   The hypotheses of Lemma 3.6 are: $\lambda\ge2$ and $\rho>0$; residual bundles and packets partition the chores; each agent has at most two packets; each packet has at most $k$ chores and price at least $\rho$; $p(S_i)\ge\rho$ and $\hat C_i(S_i)\le\lambda\gamma_i\rho$ when $\nu_i=0$; and $\hat C_i(S_i)\le(\lambda-\nu_i)\gamma_i\rho$ when $\nu_i\in\{1,2\}$.
--
--   A **run of APR** fixes an order of the active agents ($\nu_i>0$) and makes two passes in that order:
--
--   1. Each active agent chooses her $\nu_i$ cheapest available packets from a common pool, and $X_i$ becomes $S_i$ together with those packets.
--   2. Each active agent $i$ compares $R^k_i(X_i)$ with $\lambda b_1$, where $b_1$ is her cost for a cheapest bundle $B_1$ among the other agents' bundles. If there is a violation and $\nu_i=1$, then $X_i$ becomes $S_i\cup B_1$ and the other agent receives her packet. If there is a violation and $\nu_i=2$, with packets $Q^+,Q^-$ ordered by her cost and $B_2$ a second-cheapest bundle, then either she keeps $Q^-$, receives $B_1$ and sends out $Q^+$, when $\hat C_i(Q^-)\le\hat C_i(B_2)$ or no $B_2$ exists; or she sends out both packets and receives $B_1\cup B_2$, otherwise.
--
--   This is the third stage of the algorithm, which repairs the remaining envy.
--
--   **Formalization Note** The run relation allows every choice: the order and all ties. So a statement about every run is the strongest reading of "the algorithm".
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma 3.6 and Algorithm 4, p.12

import Mathlib
import Definitions.Def_ChoresEFX_IsPacketDecomp

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The hypotheses of Lemma 3.6**, p.12.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

`λ ≥ 2`; each agent has at most two packets; each packet contains at most `k` chores and has price at
least `ρ > 0`; (10) `p(S_i) ≥ ρ` and `Ĉ_i(S_i) ≤ λγ_iρ` when `ν_i = 0`; (11)
`Ĉ_i(S_i) ≤ (λ − ν_i)γ_iρ` when `ν_i ∈ {1, 2}`.

**Formalization Note.** That residual bundles and packets partition the chores is the standing shape of
the input ("Decompose each integral bundle", p.11), written `IsDecomposition`. -/
structure AprHypotheses (C : ι → κ → ℝ) (p : κ → ℝ) (γ : ι → ℝ) (k : ℕ) (lam ρ : ℝ)
    (S : ι → Finset κ) (K : ι → List (Finset κ)) : Prop where
  lam_ge : 2 ≤ lam
  rho_pos : 0 < ρ
  decomposition : IsDecomposition S K
  nu_le : ∀ i, (K i).length ≤ 2
  packet_card : ∀ i, ∀ P ∈ K i, P.card ≤ k
  packet_price : ∀ i, ∀ P ∈ K i, ρ ≤ priceOf p P
  eq_10_price : ∀ i, K i = [] → ρ ≤ priceOf p (S i)
  eq_10_cost : ∀ i, K i = [] → cost C i (S i) ≤ lam * γ i * ρ
  eq_11 : ∀ i, K i ≠ [] → cost C i (S i) ≤ (lam - ((K i).length : ℝ)) * γ i * ρ

/-- **The first pass of APR**, Algorithm 4, line 1, p.12 (Qin et al., STOC 2027 submission): in the
given order, each agent chooses her `ν_i` cheapest packets among those still available, from a common
pool.

**Formalization Note.** `Pass1 C K order pool Q`: `Q i` is the set of packets chosen by `i`; ties are free
(paper.md decision 8). -/
inductive Pass1 (C : ι → κ → ℝ) (K : ι → List (Finset κ)) :
    List ι → Finset (Finset κ) → (ι → Finset (Finset κ)) → Prop
  | nil (pool : Finset (Finset κ)) : Pass1 C K [] pool (fun _ => ∅)
  | cons (i : ι) (rest : List ι) (pool ch : Finset (Finset κ)) (Q : ι → Finset (Finset κ)) :
      ch ⊆ pool → ch.card = (K i).length →
      (∀ P ∈ ch, ∀ P' ∈ pool \ ch, cost C i P ≤ cost C i P') →
      Pass1 C K rest (pool \ ch) Q →
      Pass1 C K (i :: rest) pool (Function.update Q i ch)

/-- `j` is a cheapest bundle for agent `i` among the bundles of the agents in `A`. -/
def IsCheapestIn (C : ι → κ → ℝ) (i : ι) (X : ι → Finset κ) (A : Finset ι) (j : ι) : Prop :=
  j ∈ A ∧ ∀ h ∈ A, cost C i (X j) ≤ cost C i (X h)

/-- **One iteration of the second pass of APR**, Algorithm 4, lines 4–21, p.12 (Qin et al., STOC 2027
submission): `B₁ = X_{j₁}` is a cheapest bundle for `i` among the other bundles, `b₁ = Ĉ_i(B₁)`.

**Formalization Note.** Each constructor is one branch of the algorithm. `B₂ = X_{j₂}` is a cheapest bundle
among those of the remaining agents, and "if no such bundle exists, set `b₂ = +∞`" is the condition that
no remaining agent exists, under which the first branch of line 15 applies. Ties among bundles and between
`Q⁺` and `Q⁻` are free (paper.md decision 8). -/
inductive RepairStep (C : ι → κ → ℝ) (k : ℕ) (lam : ℝ) (S : ι → Finset κ)
    (Q : ι → Finset (Finset κ)) (i : ι) (X : ι → Finset κ) : (ι → Finset κ) → Prop
  | keep (j₁ : ι) : IsCheapestIn C i X (univ.erase i) j₁ →
      resid C k i (X i) ≤ lam * cost C i (X j₁) → RepairStep C k lam S Q i X X
  | one (j₁ : ι) (Q₁ : Finset κ) : IsCheapestIn C i X (univ.erase i) j₁ →
      lam * cost C i (X j₁) < resid C k i (X i) → Q i = {Q₁} →
      RepairStep C k lam S Q i X (Function.update (Function.update X i (S i ∪ X j₁)) j₁ Q₁)
  | twoKeep (j₁ : ι) (Qp Qm : Finset κ) : IsCheapestIn C i X (univ.erase i) j₁ →
      lam * cost C i (X j₁) < resid C k i (X i) → Q i = {Qp, Qm} → Qp ≠ Qm →
      cost C i Qm ≤ cost C i Qp →
      (((univ.erase i).erase j₁ = ∅) ∨
        ∃ j₂, IsCheapestIn C i X ((univ.erase i).erase j₁) j₂ ∧ cost C i Qm ≤ cost C i (X j₂)) →
      RepairStep C k lam S Q i X
        (Function.update (Function.update X i (S i ∪ Qm ∪ X j₁)) j₁ Qp)
  | twoSend (j₁ j₂ : ι) (Qp Qm : Finset κ) : IsCheapestIn C i X (univ.erase i) j₁ →
      lam * cost C i (X j₁) < resid C k i (X i) → Q i = {Qp, Qm} → Qp ≠ Qm →
      cost C i Qm ≤ cost C i Qp →
      IsCheapestIn C i X ((univ.erase i).erase j₁) j₂ → cost C i (X j₂) < cost C i Qm →
      RepairStep C k lam S Q i X
        (Function.update (Function.update (Function.update X i (S i ∪ X j₁ ∪ X j₂)) j₁ Qp) j₂ Qm)

/-- **The second pass of APR**, Algorithm 4, lines 3–22, p.12 (Qin et al., STOC 2027 submission): the
active agents are checked and repaired in the same order. -/
inductive Pass2 (C : ι → κ → ℝ) (k : ℕ) (lam : ℝ) (S : ι → Finset κ) (Q : ι → Finset (Finset κ)) :
    List ι → (ι → Finset κ) → (ι → Finset κ) → Prop
  | nil (X : ι → Finset κ) : Pass2 C k lam S Q [] X X
  | cons (i : ι) (rest : List ι) (X Y Z : ι → Finset κ) :
      RepairStep C k lam S Q i X Y → Pass2 C k lam S Q rest Y Z →
      Pass2 C k lam S Q (i :: rest) X Z

/-- **A run of APR**, Algorithm 4, p.12 (Qin et al., STOC 2027 submission), with output `X`: some fixed
order of the active agents (`ν_i > 0`), used in both passes, with `X_i ← S_i ∪ ⋃_ℓ Q_{i,ℓ}` after the
first (line 2).

**Formalization Note.** The pool of the first pass is all packets of all agents. Every choice of the
algorithm is free, so a statement about every run is the strongest reading (paper.md decision 8). -/
def AprRun (C : ι → κ → ℝ) (k : ℕ) (lam : ℝ) (S : ι → Finset κ) (K : ι → List (Finset κ))
    (X : ι → Finset κ) : Prop :=
  ∃ (order : List ι) (Q : ι → Finset (Finset κ)),
    order.Nodup ∧ (∀ i, i ∈ order ↔ K i ≠ []) ∧
    Pass1 C K order (univ.biUnion fun i => (K i).toFinset) Q ∧
    Pass2 C k lam S Q order (fun i => S i ∪ (Q i).biUnion id) X

end ChoresEFX


