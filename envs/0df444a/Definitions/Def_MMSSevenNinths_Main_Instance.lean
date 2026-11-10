-- Prove2me | Definitions.Def_MMSSevenNinths_Main_Instance
-- name    : MMSSevenNinths_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:46:29.70667+00:00
-- url     : https://prove2.me/theorems/f454461c-ad8b-4012-9ad8-01fa9eb38089
-- title:
--   Instances, MMS, ordered instances, complete allocations and α-MMS (§2, Definitions 2.1–2.3)
-- statement:
--   Agents are `Fin n` (the paper's agent $i+1$ is `i`), goods are `Fin m` (the paper's $e_{g+1}$ is `g`), and a valuation profile is $V$ : `Fin n → Finset (Fin m) → ℝ`, $V_i(S)=v_i(S)$. Nonnegative additive valuations are the published predicate `LittleCharity.MMS.IsAdditive V`: $v_i(S)=\sum_{g\in S}v_i(\{g\})$ and $v_i(S)\ge 0$.
--
--   * `MMS V i` is the maximin share $\mathrm{MMS}_i=\max_{P\in\Pi_n(M)}\min_j v_i(P_j)$ (Definition 2.1), via the published `LittleCharity.MMS.mms (V i) n univ`: the maximum over all labellings of the goods by $n$ parts (empty parts allowed) of the minimum part value. Statements use it with $n\ge1$.
--   * `IsOrdered V` (Definition 2.3): every agent has $v_i(e_1)\ge v_i(e_2)\ge\dots\ge v_i(e_m)$, i.e. $V_i(\{h\})\le V_i(\{g\})$ whenever $g\le h$; ties keep the index order permanently.
--   * A complete allocation is an owner map $\sigma$ : `Fin m → Fin n`; `bundle σ i` $=\{g:\sigma(g)=i\}$ is $B_i$. Owner maps are exactly the complete, disjoint, labelled partitions of $M$ with possibly empty bundles.
--   * `IsApproxMMS ρ V σ` (Definition 2.2): $v_i(B_i)\ge\rho\cdot\mathrm{MMS}_i$ for every agent $i$.
--
--   The source introduces α-MMS for α ≤ 1. `IsApproxMMS` extends the same inequality to every real ρ; on the source domain it is identical, and the goal uses only ρ = 7/9. `IsOrdered` uses the fixed common indexing chosen immediately after Lemma 2.4.
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, §2, Definitions 2.1–2.3, printed pp. 3–4 (PDF 6–7)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

open scoped Classical

namespace MMSSevenNinths.Main

/-! Huang and Zhou (2026), §2, printed pp. 3–4 (PDF 6–7).
Agents are `Fin n` (agent `i + 1` of the paper is `i : Fin n`), goods are `Fin m`
(good `e_{g+1}` is `g : Fin m`), and a valuation profile is `V : Fin n → Finset (Fin m) → ℝ`.
Nonnegative additive valuations are exactly the published `LittleCharity.MMS.IsAdditive V`. -/

/-- The maximin share `MMS_i` (Definition 2.1, printed p. 4): the maximum over all
`n`-partitions of `M` (labelled, possibly empty parts) of the minimum part value, via the
published `LittleCharity.MMS.mms`. Meaningful for `0 < n`. -/
noncomputable def MMS {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (i : Fin n) : ℝ :=
  LittleCharity.MMS.mms (V i) n Finset.univ

/-- Ordered instance (Definition 2.3, printed p. 4): every agent values the goods in the
common nonincreasing order `e_1, …, e_m`, i.e. `v_i(e_g) ≥ v_i(e_h)` whenever `g ≤ h`. -/
def IsOrdered {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i : Fin n, ∀ g h : Fin m, g ≤ h → V i {h} ≤ V i {g}

/-- A complete allocation is an owner map `σ : Fin m → Fin n` (every good goes to exactly
one agent; bundles may be empty). `bundle σ i` is agent `i`'s bundle `B_i`. -/
def bundle {n m : ℕ} (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun g => σ g = i)

/-- `ρ`-MMS (Definition 2.2, printed p. 4): `v_i(B_i) ≥ ρ · MMS_i` for every agent `i`. -/
def IsApproxMMS {n m : ℕ} (ρ : ℝ) (V : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) :
    Prop :=
  ∀ i : Fin n, ρ * MMS V i ≤ V i (bundle σ i)

end MMSSevenNinths.Main


