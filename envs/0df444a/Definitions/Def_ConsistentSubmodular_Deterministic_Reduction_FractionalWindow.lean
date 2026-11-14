-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
-- name    : ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:14.410835+00:00
-- url     : https://prove2.me/theorems/6df147cb-3982-457f-b1b0-7051e26596d5
-- title:
--   Certificate families and fractional windows (premise of Theorem 5)
-- statement:
--   Let $f$ be a monotone submodular objective on $[n]$, $\kappa$ a core budget, $\mathrm{opt}_\kappa(N,Q)=f(Q\cup\text{best }\kappa\text{-subset of }N)$ the buffered optimum (`bufferedOptimum`), and recall that a window instance has a set $\mathrm{old}$ of present elements and a nondecreasing family of buffers $Q(t)$ of newly arrived elements.
--
--   - `CertificateFamily`: the premise of Theorem 5. It consists of a level $\alpha$ with $0\le\alpha\le 3/4$ (`level`), a positive segment budget $\mathrm{budget}(m)\in\mathbb N_{>0}$ depending on the last stage $m$, and a proof that every window instance admits clairvoyant certificates (safe polygonal paths in the simplex) of level $\alpha$ with at most $\mathrm{budget}(\text{last stage})$ segments.
--   - `FractionalWindow f old Q hQ κ N T initial terminal α S`: a baseline-compressed window together with a checkpoint and two paths at level $\alpha$ with at most $S$ segments in total. Writing $V=\mathrm{opt}_\kappa(\mathrm{old},\emptyset)$, it consists of
--     - candidate cores $C_0,\dots,C_{3N+1}\subseteq\mathrm{old}$, each of size at most $\kappa$ and value at most $V$, with $C_0=\text{initial}$ and $C_{3N+1}=\text{terminal}$;
--     - retained times $0=r_0\le r_1\le\dots\le r_{3N+1}=T$ such that $C_i$ is optimal for the buffer $Q(r_i)$, i.e. $f(Q(r_i)\cup C_i)=\mathrm{opt}_\kappa(\mathrm{old},Q(r_i))$;
--     - a covering property: for every $t\le T$, either $3V\le f(Q(t))$, or some $i$ has $r_i\le t$ and $f(Q(t))<f(Q(r_i))+V/N$;
--     - a checkpoint point of the simplex on $3N+2$ vertices with multilinear value at least $\alpha\,\mathrm{opt}_\kappa(\mathrm{old},Q(r_i))$ at every retained time, and at least $\alpha\,\mathrm{opt}_\kappa(\mathrm{old},Q(t))-\alpha V/N$ at every time $t\le T$, measured in the compatible profile built from the cores;
--     - an entry polygonal path from vertex $0$ to the checkpoint, safe at level $\alpha\,\mathrm{opt}_\kappa(\mathrm{old},Q(0))$ at time $0$, and an exit polygonal path from the checkpoint to the last vertex, safe at level $\alpha\,\mathrm{opt}_\kappa(\mathrm{old},Q(T))$ at time $T$, with $\mathrm{pieces(entry)}+\mathrm{pieces(exit)}\le S$.
--
--   The file also proves the theorem `Objective.fractional_window`: for every certificate family and every window whose buffers start empty and avoid the old set, and any optimal initial and terminal cores, a fractional window exists with level $\alpha$ and $S=\mathrm{budget}(3N+1)$. The proof compresses the buffer sequence by baseline bins of width $V/N$ and applies the certificates to the compressed window.
--
--   These structures are the interface between the geometric part of the deterministic argument (certificates in the simplex) and the rounding part (turning fractional windows into integral set paths).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FractionalWindow.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BaselineBins
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

/-- The premise of Theorem 5: certificates for every window, at a level
`α ≤ 3/4` and with a positive segment budget depending on the last stage. -/
structure CertificateFamily where
  level : ℝ
  budget : ℕ → ℕ
  level_nonneg : 0 ≤ level
  level_le : level ≤ 3 / 4
  budget_pos : ∀ m, 0 < budget m
  certificates : AdmitsCertificates level budget

/-- A baseline-compressed window together with a checkpoint and two paths at
level `α` and with at most `S` segments in total. -/
structure FractionalWindow {n : ℕ} (f : Objective n) (old : Finset (Fin n))
    (Q : ℕ → Finset (Fin n)) (hQ : Monotone Q) (κ N T : ℕ)
    (initial terminal : Finset (Fin n)) (α : ℝ) (S : ℕ) where
  level_nonneg : 0 ≤ α
  level_le : α ≤ 3 / 4
  cores : Fin (3 * N + 2) → Finset (Fin n)
  core_subset : ∀ i, cores i ⊆ old
  core_card : ∀ i, (cores i).card ≤ κ
  core_value : ∀ i, f.value (cores i) ≤ f.bufferedOptimum old ∅ κ
  core_initial : cores 0 = initial
  core_terminal : cores (Fin.last (3 * N + 1)) = terminal
  retained : Fin (3 * N + 2) → ℕ
  retained_mono : Monotone retained
  retained_initial : retained 0 = 0
  retained_terminal : retained (Fin.last (3 * N + 1)) = T
  retained_bound : ∀ i, retained i ≤ T
  retained_optimal : ∀ i, f.value (Q (retained i) ∪ cores i) = f.bufferedOptimum old (Q (retained i)) κ
  retained_covers : ∀ t, t ≤ T → 3 * f.bufferedOptimum old ∅ κ ≤ f.value (Q t) ∨
    ∃ i, retained i ≤ t ∧ f.value (Q t) < f.value (Q (retained i)) + f.bufferedOptimum old ∅ κ / N
  checkpoint : Point (3 * N + 1)
  entry : PolygonalPath (3 * N + 1)
  exit : PolygonalPath (3 * N + 1)
  simplex : IsSimplex checkpoint
  checkpoint_retained : ∀ i, α * f.bufferedOptimum old (Q (retained i)) κ ≤
    (CompatibleProfile.fromPhysical f cores Q hQ).multilinearValue (retained i) checkpoint
  checkpoint_good : ∀ t, t ≤ T →
    α * f.bufferedOptimum old (Q t) κ - α * (f.bufferedOptimum old ∅ κ / N) ≤
      (CompatibleProfile.fromPhysical f cores Q hQ).multilinearValue t checkpoint
  entry_initial : entry.node 0 = vertex 0
  entry_terminal : entry.node (Fin.last entry.pieces) = checkpoint
  exit_initial : exit.node 0 = checkpoint
  exit_terminal : exit.node (Fin.last exit.pieces) = vertex (Fin.last (3 * N + 1))
  entry_safe : (CompatibleProfile.fromPhysical f cores Q hQ).SafePath 0
    (α * f.bufferedOptimum old (Q 0) κ) entry
  exit_safe : (CompatibleProfile.fromPhysical f cores Q hQ).SafePath T
    (α * f.bufferedOptimum old (Q T) κ) exit
  pieces : entry.pieces + exit.pieces ≤ S

namespace Objective

variable {n : ℕ} (f : Objective n)

/-- Any certificate of the baseline-compressed window yields bounded-complexity
window geometry. No arrival time is omitted from the checkpoint guarantee. -/
theorem fractional_window (O : CertificateFamily) (old : Finset (Fin n))
    (Q : ℕ → Finset (Fin n)) (hQ : Monotone Q) (hQ0 : Q 0 = ∅)
    (hQold : ∀ t, Disjoint (Q t) old) (κ N T : ℕ) (hN : 0 < N)
    (initial terminal : Finset (Fin n))
    (hinit : initial ⊆ old ∧ initial.card ≤ κ ∧ f.value (Q 0 ∪ initial) = f.bufferedOptimum old (Q 0) κ)
    (hterm : terminal ⊆ old ∧ terminal.card ≤ κ ∧ f.value (Q T ∪ terminal) = f.bufferedOptimum old (Q T) κ) :
    Nonempty (FractionalWindow f old Q hQ κ N T initial terminal O.level (O.budget (3 * N + 1))) := by
  classical
  let V := f.bufferedOptimum old ∅ κ
  let times := BaselineBins.retained (fun t => f.value (Q t)) T (V / N) N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hV : 0 ≤ V := f.bufferedOptimum_nonnegative _ _ _
  have hwidth : 0 ≤ V / N := div_nonneg hV hNr.le
  have htimes : Monotone times := BaselineBins.retained_mono _ _ _ N hwidth
  have ht0 : times 0 = 0 := BaselineBins.retained_initial _ _ _ N (f.nonnegative _)
  have htT : times (3 * N + 1) = T := BaselineBins.retained_terminal _ _ _ N
  let cores : Fin (3 * N + 2) → Finset (Fin n) := fun i =>
    if i = 0 then initial else if i = Fin.last (3 * N + 1) then terminal
    else f.bufferedOptimizer old (Q (times i.val)) κ
  have hcore0 : cores 0 = initial := by simp [cores]
  have hcoreT : cores (Fin.last (3 * N + 1)) = terminal := by
    have hn : (Fin.last (3 * N + 1) : Fin (3 * N + 2)) ≠ 0 := by
      intro hh
      have hv := congrArg Fin.val hh
      simp at hv
    simp [cores, hn]
  have hcores (i : Fin (3 * N + 2)) : cores i ⊆ old ∧ (cores i).card ≤ κ ∧
      f.value (Q (times i.val) ∪ cores i) = f.bufferedOptimum old (Q (times i.val)) κ := by
    by_cases hi : i = 0
    · subst i
      simpa only [hcore0, Fin.val_zero, ht0] using hinit
    by_cases hiT : i = Fin.last (3 * N + 1)
    · subst i
      simpa only [hcoreT, Fin.val_last, htT] using hterm
    · simp only [cores, if_neg hi, if_neg hiT]
      exact ⟨(f.bufferedOptimizer_spec _ _ _).1, (f.bufferedOptimizer_spec _ _ _).2.1, rfl⟩
  let R := CompatibleProfile.fromPhysical f cores Q hQ
  -- The compressed window, with the retained buffers as its arrivals.
  let Wc : WindowInstance n := {
    objective := f
    present := old
    coreBudget := κ
    lastStage := 3 * N + 1
    arrivals := fun j => Q (times j.val)
    candidate := cores
    arrivals_zero := by
      change Q (times 0) = ∅
      rw [ht0, hQ0]
    arrivals_mono := fun i j hij => hQ (htimes hij)
    arrivals_disjoint := fun j => hQold _
    candidate_subset := fun i => (hcores i).1
    candidate_card := fun i => (hcores i).2.1
    candidate_optimal := fun j B hB hk => by
      rw [Finset.union_comm B, Finset.union_comm (cores j), (hcores j).2.2]
      exact f.le_bufferedOptimum hB hk }
  obtain ⟨Z⟩ := O.certificates n Wc
  have hstage' (j : Fin (3 * N + 2)) :
      O.level * f.bufferedOptimum old (Q (times j.val)) κ ≤ R.multilinearValue (times j.val) Z.anchor := by
    have hh : O.level * f.value (cores j ∪ Q (times j.val)) ≤ R.multilinearValue (times j.val) Z.anchor :=
      Z.persistence j
    rwa [Finset.union_comm, (hcores j).2.2] at hh
  have hcube : ∀ i, 0 ≤ Z.anchor i ∧ Z.anchor i ≤ 1 :=
    fun i => ⟨Z.anchor_mem.1 i, Z.anchor_mem.coordinate_le_one i⟩
  have hmono : Monotone (fun t => R.multilinearValue t Z.anchor) := by
    intro s t hst
    exact finiteExpectation_mono Z.anchor hcube (fun I => R.values_increase s t hst I)
  have hbase (t : ℕ) : f.value (Q t) ≤ R.multilinearValue t Z.anchor := by
    have hm := finiteExpectation_mono Z.anchor hcube (v := fun _ => f.value (Q t))
      (w := (R.objective t).value) (fun I => f.monotone _ _ Finset.subset_union_left)
    simpa only [CompatibleProfile.multilinearValue, finiteExpectation_const] using hm
  have hα0 := O.level_nonneg
  have hα := O.level_le
  have hgood (t : ℕ) (ht : t ≤ T) :
      O.level * f.bufferedOptimum old (Q t) κ - O.level * (V / N) ≤ R.multilinearValue t Z.anchor := by
    by_cases hlow : f.value (Q t) < 3 * V
    · obtain ⟨j, hjt, hbin⟩ := BaselineBins.approximates (fun t => f.value (Q t)) T N hN V (by linarith [f.nonnegative (Q t)])
        (fun t => f.nonnegative _) t ht hlow
      change times j.val ≤ t at hjt
      change f.value (Q t) < f.value (Q (times j.val)) + V / N at hbin
      have hg := f.bufferedOptimum_growth (N := old) (k := κ) (hQ hjt)
      have hs := (hstage' j).trans (hmono hjt)
      have hd : f.bufferedOptimum old (Q t) κ ≤ f.bufferedOptimum old (Q (times j.val)) κ + V / N := by
        linarith only [hg, hbin]
      have hm := mul_le_mul_of_nonneg_left hd hα0
      linarith only [hm, hs]
    · have hu := f.bufferedOptimum_le old (Q t) κ
      have h0 := f.nonnegative ∅
      have hb := hbase t
      change f.bufferedOptimum old (Q t) κ ≤ f.value (Q t) + V - f.value ∅ at hu
      have hv : f.bufferedOptimum old (Q t) κ ≤ f.value (Q t) + V := by linarith
      have hm := mul_le_mul_of_nonneg_left hv hα0
      have hm' := mul_le_mul_of_nonneg_right hα (show 0 ≤ f.value (Q t) + V by
        linarith [f.nonnegative (Q t)])
      nlinarith only [hm, hm', hb, hlow, mul_nonneg hα0 hwidth]
  have hentry' : R.SafePath 0 (O.level * f.bufferedOptimum old (Q 0) κ) Z.entry := by
    have hh : Z.entry.Along (fun q => IsSimplex q ∧
        O.level * f.value (cores 0 ∪ Q (times 0)) ≤ R.multilinearValue (times 0) q) :=
      Z.entry_mem.and Z.safe_entry
    rw [ht0, Finset.union_comm, hcore0, hinit.2.2] at hh
    exact hh
  have hexit' : R.SafePath T (O.level * f.bufferedOptimum old (Q T) κ) Z.exit := by
    have hh : Z.exit.Along (fun q => IsSimplex q ∧
        O.level * f.value (cores (Fin.last (3 * N + 1)) ∪ Q (times (3 * N + 1))) ≤
          R.multilinearValue (times (3 * N + 1)) q) :=
      Z.exit_mem.and Z.safe_exit
    rw [htT, Finset.union_comm, hcoreT, hterm.2.2] at hh
    exact hh
  refine ⟨{
    level_nonneg := hα0
    level_le := hα
    cores := cores
    core_subset := fun i => (hcores i).1
    core_card := fun i => (hcores i).2.1
    core_value := ?_
    core_initial := hcore0
    core_terminal := hcoreT
    retained := fun i => times i.val
    retained_mono := fun i j hij => htimes hij
    retained_initial := ht0
    retained_terminal := htT
    retained_bound := fun i => BaselineBins.retained_le_terminal _ _ _ _ _
    retained_optimal := fun i => (hcores i).2.2
    retained_covers := ?_
    checkpoint := Z.anchor
    entry := Z.entry
    exit := Z.exit
    simplex := Z.anchor_mem
    checkpoint_retained := hstage'
    checkpoint_good := hgood
    entry_initial := Z.entry_start
    entry_terminal := Z.entry_finish
    exit_initial := Z.exit_start
    exit_terminal := Z.exit_finish
    entry_safe := hentry'
    exit_safe := hexit'
    pieces := Z.segments }⟩
  · intro i
    simpa using f.le_bufferedOptimum (Q := ∅) (hcores i).1 (hcores i).2.1
  · intro t ht
    by_cases hlow : f.value (Q t) < 3 * V
    · right
      exact BaselineBins.approximates (fun t => f.value (Q t)) T N hN V (by linarith [f.nonnegative (Q t)])
        (fun t => f.nonnegative _) t ht hlow
    · exact Or.inl (le_of_not_gt hlow)

end Objective

end ConsistentSubmodular

end


