-- Prove2me | Definitions.Def_CompDesign_Supplement_IsCombPNE
-- name    : CompDesign_Supplement_IsCombPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:51:37.59783+00:00
-- url     : https://prove2.me/theorems/507ccbaa-b503-4978-81d5-2ee7ff13feb6
-- title:
--   Pure and principal-favoring pure Nash equilibria of the multi-agent combinatorial game
-- statement:
--   A ground set $A=\{1,\dots,m\}$ of atomic actions is partitioned as $A=A_1\sqcup\dots\sqcup A_n$ among $n$ agents. A profile is the realized set $S\subseteq A$, agent $i$ playing $S_i=S\cap A_i$; a payment rule pays $p_i(S)$, and agent $i$'s utility is $p_i(S)-c(S_i)$ with $c(S_i)=\sum_{e\in S_i}c_e$.
--
--   1. $S$ is a **pure Nash equilibrium** if no agent $i$ gains strictly by replacing $S_i$ with any $S'_i\subseteq A_i$ (the new realized set being $(S\setminus A_i)\cup S'_i$).
--   2. $S$ is a **principal-favoring** pure Nash equilibrium if moreover no replacement with equal payoff raises $v$ strictly.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.2, p.57 (PDF 60)

import Mathlib

namespace CompDesign.Supplement

/-- The realized set after agent `i` replaces its own actions by `T ⊆ A_i` in the multi-agent
combinatorial model of §7.2, p.57 (PDF 60), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): `(S ∖ A_i) ∪ T`, where `A_i = own⁻¹(i)`. -/
def deviate {n m : ℕ} (own : Fin m → Fin n) (S : Finset (Fin m)) (i : Fin n)
    (T : Finset (Fin m)) : Finset (Fin m) :=
  S.filter (fun e => own e ≠ i) ∪ T

/-- A pure Nash equilibrium of the multi-agent combinatorial game of §7.2, p.57 (PDF 60), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…):
the ground set `A = Fin m` is partitioned among `n` agents by `own`; a profile is the realized set
`S` (agent `i` plays `S_i = S ∩ A_i`), agent `i` is paid `P(S)_i` and pays `c(S_i) = ∑_{e∈S_i} c_e`;
no agent gains strictly by replacing `S_i` with any `T ⊆ A_i`. -/
def IsCombPNE {n m : ℕ} (own : Fin m → Fin n) (P : Finset (Fin m) → Fin n → ℝ)
    (c : Fin m → ℝ) (S : Finset (Fin m)) : Prop :=
  ∀ (i : Fin n) (T : Finset (Fin m)), (∀ e ∈ T, own e = i) →
    P (deviate own S i T) i - ∑ e ∈ T, c e ≤ P S i - ∑ e ∈ S.filter (fun e => own e = i), c e

/-- A principal-favoring pure Nash equilibrium of the multi-agent combinatorial game (§7.2, p.57,
PDF 60, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): "whenever an agent has multiple payoff-maximizing choices against the other agents'
choices, it chooses one that maximizes the principal's value"): a pure Nash equilibrium in which no
payoff-equal replacement `T ⊆ A_i` raises `v` strictly. -/
def IsCombPFPNE {n m : ℕ} (own : Fin m → Fin n) (P : Finset (Fin m) → Fin n → ℝ)
    (v : Finset (Fin m) → ℝ) (c : Fin m → ℝ) (S : Finset (Fin m)) : Prop :=
  IsCombPNE own P c S ∧ ∀ (i : Fin n) (T : Finset (Fin m)), (∀ e ∈ T, own e = i) →
    P (deviate own S i T) i - ∑ e ∈ T, c e = P S i - ∑ e ∈ S.filter (fun e => own e = i), c e →
      v (deviate own S i T) ≤ v S

end CompDesign.Supplement


