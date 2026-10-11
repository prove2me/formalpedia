-- Prove2me | solution 1 for Algo2Lean.UnionFind.link_valid
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:56.556538+00:00
-- url     : https://prove2.me/submissions/38d9dd5d-90dd-4d86-b35c-388e0fe4cbb6

import Definitions.Def_Algo2LeanLib_UnionFind


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind













theorem total_update {n : Nat} (f : Fin n → Nat) (index : Fin n) (value : Nat) :
    total (update f index value) + f index = total f + value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [total, update, Fin.succ_ne_zero, Nat.add_comm, Nat.add_left_comm]
    · have next := ih (fun index => f index.succ) index
      simpa [total, update, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero index), Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using! congrArg (fun x => f 0 + x) next









































theorem link_rank_ge {n : Nat} (state : State n) (loser winner vertex : Fin n) :
    state.rank vertex ≤ (link state loser winner).rank vertex := by
  by_cases same : vertex = winner
  · subst vertex
    simp only [link, update_same]
    split <;> omega
  · simp [link, update, same]

theorem link_root_iff {n : Nat} {state : State n}
    (loser winner : Fin n) (different : loser ≠ winner) :
    ∀ vertex, (link state loser winner).parent vertex = vertex ↔
      vertex ≠ loser ∧ state.parent vertex = vertex := by
  intro vertex
  by_cases same : vertex = loser
  · subst vertex
    simp [link, different.symm]
  · simp [link, update, same]

theorem link_mass_total {n : Nat} (state : State n)
    (loser winner : Fin n) (different : loser ≠ winner) :
    total (link state loser winner).mass = total state.mass := by
  have first := total_update state.mass loser 0
  have second := total_update (update state.mass loser 0) winner
    (state.mass loser + state.mass winner)
  rw [update_other state.mass loser winner 0 different.symm] at second
  change total (update (update state.mass loser 0) winner
    (state.mass loser + state.mass winner)) = total state.mass
  omega

/-- Linking roots by rank preserves validity and the fixed mass budget. -/
theorem link_valid {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (different : loser ≠ winner)
    (loserRoot : state.parent loser = loser) (winnerRoot : state.parent winner = winner)
    (ordered : state.rank loser ≤ state.rank winner) : Valid (link state loser winner) := by
  have loserRep := valid.root_representative loser loserRoot
  have winnerRep := valid.root_representative winner winnerRoot
  have winnerFixed : (link state loser winner).parent winner = winner := by
    simp [link, update, different.symm, winnerRoot]
  have winnerRank : state.rank loser < (link state loser winner).rank winner := by
    simp only [link, update_same]
    split <;> omega
  constructor
  · intro vertex
    simp only [link, mergeRepresentative]
    split
    · simpa [link] using winnerFixed
    · rename_i other
      exact (link_root_iff loser winner different _).mpr
        ⟨other, valid.representative_root vertex⟩
  · intro vertex fixed
    obtain ⟨other, oldFixed⟩ := (link_root_iff loser winner different vertex).mp fixed
    simp [link, mergeRepresentative, valid.root_representative vertex oldFixed, other]
  · intro vertex
    by_cases same : vertex = loser
    · subst vertex
      simp [link, update_same, mergeRepresentative, loserRep, winnerRep, different.symm]
    · change mergeRepresentative state.representative loser winner
        (update state.parent loser winner vertex) =
        mergeRepresentative state.representative loser winner vertex
      rw [update_other _ _ _ _ same]
      simp only [mergeRepresentative, valid.parent_representative]
  · intro vertex moving
    by_cases same : vertex = loser
    · subst vertex
      simpa [link, update, different] using winnerRank
    · have oldMoving : state.parent vertex ≠ vertex := by
        simpa [link, update, same] using moving
      have notWinner : vertex ≠ winner := by
        intro equal
        subst vertex
        exact oldMoving winnerRoot
      have rising := valid.parent_rank vertex oldMoving
      have raised := link_rank_ge state loser winner (state.parent vertex)
      change update state.rank winner _ vertex <
        (link state loser winner).rank (update state.parent loser winner vertex)
      rw [update_other _ _ _ _ notWinner, update_other _ _ _ _ same]
      omega
  · intro vertex fixed
    obtain ⟨notLoser, oldFixed⟩ := (link_root_iff loser winner different vertex).mp fixed
    by_cases same : vertex = winner
    · subst vertex
      have massLoser := valid.root_mass loser loserRoot
      have massWinner := valid.root_mass winner winnerRoot
      simp only [link, update_same]
      split
      · rename_i equal
        rw [Nat.pow_succ]
        rw [equal] at massLoser
        omega
      · omega
    · simpa [link, update, same, notLoser] using valid.root_mass vertex oldFixed
  · intro vertex moving
    by_cases same : vertex = loser
    · subst vertex
      simp [link, update, different]
    · have notWinner : vertex ≠ winner := by
        intro equal
        subst vertex
        exact moving winnerFixed
      have oldMoving : state.parent vertex ≠ vertex := by
        simpa [link, update, same] using moving
      simpa [link, update, same, notWinner] using valid.nonroot_mass vertex oldMoving
  · rw [link_mass_total state loser winner different]
    exact valid.mass_budget















end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (loser winner : Fin n),
          Ne.{1} loser winner →
            Eq.{1} (state.parent loser) loser →
              Eq.{1} (state.parent winner) winner →
                LE.le.{0} (state.rank loser) (state.rank winner) →
                  Algo2Lean.UnionFind.Valid (Algo2Lean.UnionFind.link state loser winner) :=
  Algo2Lean.UnionFind.link_valid
