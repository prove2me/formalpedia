-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
-- name    : BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:16:24.248045+00:00
-- url     : https://prove2.me/theorems/4a074453-a200-4cb4-962d-eb2abd1b57cd
-- title:
--   BCFGJPSSV26.Stable.Alg.ClusterSamplingAnalysis — The analysis of the cluster sampling
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.ClusterSamplingAnalysis` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The cluster-sampling theorem of [BCFGJPSSV26b, Section 4.4] as a process lemma
--   (`BCFGJPSSV26.Stable.Hyp.card_clusterWitness`): given a good outcome `w₁` of the client sampling,
--   at least `q₂^(M₂) K^(M₂)` of the chunk vectors give a good outcome of the cluster sampling
--   (`BCFGJPSSV26.Stable.ClusterWitness`), `q₂ = 1/(12 N³)`.
--
--   Proof: `BCFGJPSSV26.Stable.guided_count` with the invariant `BCFGJPSSV26.Stable.KSData.Inv`, a
--   structure with one field per clause, about ghost data that are functions of the state: the greedy
--   matching of the dummies to clusters of `O_B` sharing a loose satellite with
--   their leader. The good chunks of each mode: `START` skips exactly when the current cost condition
--   holds; `SAMPLE` picks a satellite of an unmatched cluster (phase `0`) or such a satellite or a
--   center outside `LS_X` (phase `1`), of weight at least `ε³ opt` out of at most `6 opt`
--   (`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`); the other modes follow the case analysis of
--   the paper with `BCFGJPSSV26.Stable.Hyp.no_dense_cores` and `BCFGJPSSV26.Stable.Hyp.comparable_per`.
--   A skipped iteration leaves the state unchanged, so the cost condition that made it skip still
--   holds afterwards; the second cost condition is not monotone in the state (deleting centers changes
--   the mixed clusters), so this is what keeps it. The run ends in phase `2`
--   (`BCFGJPSSV26.Stable.ksRun_phase`), where the invariant gives the witness
--   (`BCFGJPSSV26.Stable.KSData.witness`).
--
--   The witness asks for one dummy per matched cluster, all distinct; the dummies of one leader are
--   distinct thanks to the shift of their radii by the number of dummies
--   (`BCFGJPSSV26.Stable.ksRad`, `BCFGJPSSV26.Stable.KSData.ksRad_inj`), also when two clusters are
--   at the same distance from the leader.
--
--   The pieces: the ghost matching and the invariant (`ClusterSamplingGhost`), the exact weights and
--   counting facts (`ClusterSamplingBridge`), one step mode by mode (`ClusterSamplingStep`,
--   `BCFGJPSSV26.Stable.KSData.inv_step`), and the densities (`ClusterSamplingDensity`,
--   `BCFGJPSSV26.Stable.KSData.card_good`).
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.card_clusterWitness` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingAnalysis`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingAnalysis.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.ClusterSamplingAnalysis` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The analysis of the cluster sampling

The cluster-sampling theorem of [BCFGJPSSV26b, Section 4.4] as a process lemma
(`BCFGJPSSV26.Stable.Hyp.card_clusterWitness`): given a good outcome `w₁` of the client sampling,
at least `q₂^(M₂) K^(M₂)` of the chunk vectors give a good outcome of the cluster sampling
(`BCFGJPSSV26.Stable.ClusterWitness`), `q₂ = 1/(12 N³)`.

Proof: `BCFGJPSSV26.Stable.guided_count` with the invariant `BCFGJPSSV26.Stable.KSData.Inv`, a
structure with one field per clause, about ghost data that are functions of the state: the greedy
matching of the dummies to clusters of `O_B` sharing a loose satellite with
their leader. The good chunks of each mode: `START` skips exactly when the current cost condition
holds; `SAMPLE` picks a satellite of an unmatched cluster (phase `0`) or such a satellite or a
center outside `LS_X` (phase `1`), of weight at least `ε³ opt` out of at most `6 opt`
(`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`); the other modes follow the case analysis of
the paper with `BCFGJPSSV26.Stable.Hyp.no_dense_cores` and `BCFGJPSSV26.Stable.Hyp.comparable_per`.
A skipped iteration leaves the state unchanged, so the cost condition that made it skip still
holds afterwards; the second cost condition is not monotone in the state (deleting centers changes
the mixed clusters), so this is what keeps it. The run ends in phase `2`
(`BCFGJPSSV26.Stable.ksRun_phase`), where the invariant gives the witness
(`BCFGJPSSV26.Stable.KSData.witness`).

The witness asks for one dummy per matched cluster, all distinct; the dummies of one leader are
distinct thanks to the shift of their radii by the number of dummies
(`BCFGJPSSV26.Stable.ksRad`, `BCFGJPSSV26.Stable.KSData.ksRad_inj`), also when two clusters are
at the same distance from the leader.

The pieces: the ghost matching and the invariant (`ClusterSamplingGhost`), the exact weights and
counting facts (`ClusterSamplingBridge`), one step mode by mode (`ClusterSamplingStep`,
`BCFGJPSSV26.Stable.KSData.inv_step`), and the densities (`ClusterSamplingDensity`,
`BCFGJPSSV26.Stable.KSData.card_good`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

/-- The run as an iteration of one chunk per step. -/
theorem foldl_range_eq_runFin {σ : Type*} {Kc : ℕ} (f : σ → ℕ → σ) (x₀ : σ) (ch : ℕ → ℕ) :
    ∀ (M : ℕ) (u : Fin M → Fin Kc), (∀ i (h : i < M), ch i = u ⟨i, h⟩) →
      (List.range M).foldl (fun st t ↦ f st (ch t)) x₀ =
        runFin (fun _ st v ↦ f st v.1) x₀ M u
  | 0, _, _ => rfl
  | M + 1, u, hu => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_range_eq_runFin f x₀ ch M (fun i ↦ u i.castSucc) fun i h ↦ hu i (by omega), hu M
        (by omega)]
    rfl

theorem inv_init : K.Inv ksInit := by
  refine Inv.mk_start K (del := []) (D := []) ?_ (by norm_num) (Nat.zero_le _)
    (fun _ h ↦ absurd h List.not_mem_nil) (fun _ _ h ↦ List.not_mem_nil h)
    (fun h ↦ absurd h (by norm_num)) (.inr le_rfl)
  exact ⟨List.nodup_nil, by simp [matched_nil], by simp [matched_nil], List.nodup_nil,
    fun _ h ↦ absurd h List.not_mem_nil⟩

end KSData

end BCFGJPSSV26.Stable


