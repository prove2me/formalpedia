-- Prove2me | Definitions.Def_HZFixp_Main_NashProblem
-- name    : HZFixp_Main_NashProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:51:25.328884+00:00
-- url     : https://prove2.me/theorems/908551db-59d8-46e9-a676-85ffdb95bf1b
-- title:
--   Definition 2.3 — the three-player Nash equilibrium search problem
-- statement:
--   A **three-player game** gives player $i \in \{1,2,3\}$ a set $[m_i]$ of pure strategies ($m_i \ge 1$) and a rational payoff $u_i(s)$ at every pure profile $s = (s_1,s_2,s_3)$. A **mixed strategy** of player $i$ is $\xi_i \in \Delta_{m_i}$; for a profile $\xi = (\xi_i)_i$, $U_{ij}(\xi_{-i})$ is player $i$'s expected payoff from pure strategy $j$ when the others play $\xi_{-i}$. The profile is a **Nash equilibrium** (Definition 2.3) if
--   $$U_{ij}(\xi_{-i}) \le \sum_{t=1}^{m_i} \xi_{it}\, U_{it}(\xi_{-i}) \qquad \text{for every player } i \text{ and pure strategy } j.$$
--
--   The search problem has as instances the games, written in binary as $[m_1,m_2,m_3]$ followed by the three payoff tables (each listing $u_i$ at all pure profiles in lexicographic order), and as solutions the Nash equilibria, written as the vector of the $m_1+m_2+m_3$ probabilities, player $1$ first.
--
--   This is the problem Etessami and Yannakakis proved FIXP-complete, the starting point of the paper's chain of reductions.
--
--   **Formalization Note.** The equilibrium condition is the published `AGT.IsMixedNash` (no player gains by switching to any mixed strategy), which is equivalent to Definition 2.3's pure-deviation form (published as `FixpNash.DivFree.isMixedNash_iff_purePayoff_le`).
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 5 (PDF 7), Definition 2.3 and the paragraph after Definition 2.4; p. 8 (PDF 10), §3.2

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_agt_games

namespace HZFixp.Main

open OnlineCRS.Combine FixpReciprocal

/-- The data of a three-player normal-form game: the numbers `m_1, m_2, m_3` of pure strategies and
the three payoff tables, each listing the payoffs of one player at all pure profiles
`(s_1, s_2, s_3)` in lexicographic order (`s_1` slowest). -/
structure NashData where
  /-- the numbers of pure strategies `[m_1, m_2, m_3]` -/
  m : List ℕ
  /-- the payoff tables of players `1, 2, 3` -/
  tables : List (List ℚ)

/-- The number of pure strategies of player `i` (`0`-based). -/
def NashData.ms (D : NashData) (i : Fin 3) : ℕ := D.m.getD i.val 0

/-- **A three-player game (Definition 2.3):** three players, player `i` with pure strategies
`[m_i]`, `m_i ≥ 1`, and a rational payoff for every player at every pure profile. -/
def NashData.IsInstance (D : NashData) : Prop :=
  D.m.length = 3 ∧ (∀ k ∈ D.m, 1 ≤ k) ∧ D.tables.length = 3 ∧
    ∀ t ∈ D.tables, t.length = D.ms 0 * D.ms 1 * D.ms 2

/-- Instances of the three-player Nash problem. -/
def NashInst : Type := {D : NashData // D.IsInstance}

/-- The payoff `u_i(s)` of player `i` at the pure profile `s`, read from its table at position
`s_1·m_2·m_3 + s_2·m_3 + s_3`. -/
noncomputable def NashData.payoff (D : NashData) (i : Fin 3) (s : ∀ j : Fin 3, Fin (D.ms j)) : ℝ :=
  (((D.tables.getD i.val []).getD
    ((s 0).val * (D.ms 1 * D.ms 2) + (s 1).val * D.ms 2 + (s 2).val) 0 : ℚ) : ℝ)

/-- The index of the coordinate `ξ_{ij}` in a solution vector: player `1`'s probabilities come
first, then player `2`'s, then player `3`'s. -/
def NashData.offset (D : NashData) (i : Fin 3) : ℕ := (D.m.take i.val).sum

/-- The mixed profile `ξ = (ξ_i)_i` read from a solution vector. -/
noncomputable def NashData.profile (D : NashData) {k : ℕ} (x : Fin k → ℝ) :
    ∀ i : Fin 3, Fin (D.ms i) → ℝ :=
  fun i j => lookup x (D.offset i + j.val)

/-- Binary encoding of a game: the list `[m_1, m_2, m_3]`, then the three payoff tables, every
rational with binary numerator and denominator. -/
def encNashData (D : NashData) : List Sym := fList fNat D.m ++ fList (fList fRat) D.tables

theorem encNashData_injective : Function.Injective encNashData := by
  rintro ⟨m, t⟩ ⟨m', t'⟩ h
  simp only [encNashData] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree.fList h
  have h2 := fRat_prefixFree.fList.fList.injective h
  simp_all

/-- **Three-player Nash equilibrium as a search problem (Definition 2.3; [EY10]).** Input: a
three-player game with rational payoffs, encoded in binary. Output: a mixed-strategy profile
`ξ = (ξ_i)_i`, `ξ_i ∈ Δ_{m_i}`, that is a Nash equilibrium: `U_{ij}(ξ_{−i}) ≤ ∑_t ξ_{it} U_{it}(ξ_{−i})`
for every player `i` and pure strategy `j`. A solution is the vector of the `m_1 + m_2 + m_3`
probabilities, player by player.

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 5, Definition 2.3 and the paragraph after
Definition 2.4 ("Computing a three-player Nash equilibrium is FIXP-complete under these
reductions [EY10]").

**Formalization Note.** The equilibrium condition is the published `AGT.IsMixedNash`: every `ξ_i`
is a probability vector and no player gains by deviating to any other mixed strategy. This is
equivalent to Definition 2.3's pure-deviation form (published as
`FixpNash.DivFree.isMixedNash_iff_purePayoff_le`), since a mixed deviation's payoff is an average
of pure ones. -/
noncomputable def nashProblem : RealSearch where
  Inst := NashInst
  enc := fun I => encNashData I.1
  enc_injective := fun _ _ h => Subtype.ext (encNashData_injective h)
  dim := fun I => I.1.ms 0 + I.1.ms 1 + I.1.ms 2
  Sol := fun I => {x | AGT.IsMixedNash (S := fun i : Fin 3 => Fin (I.1.ms i)) I.1.payoff
    (I.1.profile x)}

end HZFixp.Main


