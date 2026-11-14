-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_WindowCertificates
-- name    : ConsistentSubmodular_Deterministic_Certificates_WindowCertificates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:18:50.107231+00:00
-- url     : https://prove2.me/theorems/162b5a71-f8ae-45fe-ba5c-a26574a960e8
-- title:
--   Window instances as compatible type profiles; certificates from a common checkpoint (Theorem 7)
-- statement:
--   For a window instance $W$ with stages $0,\dots,m$ (arrivals $R_j$, candidates $O_j$, benchmark $P_j = f(O_j \cup R_j)$), the mixture value $H_j(p)$ is identified with the multilinear value of a compatible type profile, so that the finite checkpoint theorem yields certificates.
--
--   - `arrivalsAt t` is $R_{\min(t,m)}$, the arrivals at a natural-number stage, constant after the last stage $m$.
--   - `profile` is the compatible profile on $m+1$ types obtained from $f$, the candidates $O_i$ and the monotone arrivals $t \mapsto R_{\min(t,m)}$: its objective at time $t$ is $A \mapsto f(R_{\min(t,m)} \cup \bigcup_{i\in A} O_i)$ on sets of types.
--   - `certificateOfProfile` builds a `W.Certificate α L` from an anchor $p \in \Delta$, an entry path and an exit path, given: the stage inequalities $\alpha\,(\text{profile objective at } t)(\{t\}) \le$ the profile's multilinear value at $(t,p)$ for all $t$; the endpoint conditions $\mathrm{entry}_0 = \delta_0$, $\mathrm{entry}_{\mathrm{end}} = p = \mathrm{exit}_0$, $\mathrm{exit}_{\mathrm{end}} = \delta_m$; safety of the entry at stage $0$ at level $\alpha$ times the stage-$0$ benchmark and of the exit at stage $m$ at level $\alpha$ times the stage-$m$ benchmark, as profile paths; and $\mathrm{entry.pieces} + \mathrm{exit.pieces} \le L$. The certificate's fields are filled by the identifications $H_j = $ multilinear value of the profile and $P_j = (\text{profile objective at } j)(\{j\})$.
--
--   The file also proves these identifications, monotonicity of `arrivalsAt` and its agreement with $R_j$ at stages $j \le m$, and a lemma that a point supported on at most two labels has two labels carrying all its mass.
--
--   This bridges the abstract window certificates of Section 3.2 and the atomic-profile finite checkpoint theorem, proving that every window instance with stages $0,\dots,m$ admits a $(3/4, m+3)$-certificate (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/WindowCertificates.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_CompletionScaling
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackBeforeHigh
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_VertexCheckpoint
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RollbackCheckpoint
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Plateau

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The arrivals at every natural stage, constant after the last stage. -/
def arrivalsAt (t : ℕ) : Finset (Fin n) :=
  W.arrivals ⟨min t W.lastStage, by omega⟩

theorem arrivalsAt_mono : Monotone W.arrivalsAt := by
  intro s t hst
  apply W.arrivals_mono
  change min s W.lastStage ≤ min t W.lastStage
  exact min_le_min_right _ hst

@[simp] theorem arrivalsAt_stage (j : Fin (W.lastStage + 1)) :
    W.arrivalsAt j.val = W.arrivals j := by
  unfold arrivalsAt
  congr
  have := j.isLt
  omega

/-- The compatible type profile of the window: type `i` is the candidate `O_i`. -/
def profile : CompatibleProfile (W.lastStage + 1) :=
  CompatibleProfile.fromPhysical W.objective W.candidate W.arrivalsAt W.arrivalsAt_mono

theorem mixtureValue_eq_expectation (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.mixtureValue j p = finiteExpectation p
      (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate)) := rfl

theorem mixtureValue_eq_profile (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.mixtureValue j p = W.profile.multilinearValue j.val p := by
  rw [mixtureValue_eq_expectation]
  unfold CompatibleProfile.multilinearValue profile CompatibleProfile.fromPhysical
    Objective.onTypes
  simp only [arrivalsAt_stage]

theorem benchmark_eq_profile (j : Fin (W.lastStage + 1)) :
    W.benchmark j = (W.profile.objective j.val).value {j} := by
  simp [benchmark, profile, CompatibleProfile.fromPhysical, Finset.union_comm]

/-- A common checkpoint of the window's profile, with safe paths for the two
endpoint objectives, is a certificate. -/
def certificateOfProfile {α : ℝ} {L : ℕ} (p : Point W.lastStage)
    (entry exit : PolygonalPath W.lastStage) (hp : IsSimplex p)
    (hstage : ∀ t : Fin (W.lastStage + 1),
      α * (W.profile.objective t.val).value {t} ≤ W.profile.multilinearValue t.val p)
    (he0 : entry.node 0 = vertex 0) (he1 : entry.node (Fin.last entry.pieces) = p)
    (hx0 : exit.node 0 = p)
    (hx1 : exit.node (Fin.last exit.pieces) = vertex (Fin.last W.lastStage))
    (hentry : W.profile.SafePath 0 (α * (W.profile.objective 0).value {0}) entry)
    (hexit : W.profile.SafePath W.lastStage
      (α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage}) exit)
    (hpieces : entry.pieces + exit.pieces ≤ L) : W.Certificate α L where
  anchor := p
  entry := entry
  exit := exit
  anchor_mem := hp
  entry_mem := (show entry.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective 0).value {0} ≤ W.profile.multilinearValue 0 q) from hentry).mono
    (fun _ hq => hq.1)
  exit_mem := (show exit.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage} ≤
        W.profile.multilinearValue W.lastStage q) from hexit).mono (fun _ hq => hq.1)
  entry_start := he0
  entry_finish := he1
  exit_start := hx0
  exit_finish := hx1
  persistence j := by
    rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
    exact hstage j
  safe_entry := (show entry.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective 0).value {0} ≤ W.profile.multilinearValue 0 q) from hentry).mono
    (fun q hq => by
      rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
      exact hq.2)
  safe_exit := (show exit.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage} ≤
        W.profile.multilinearValue W.lastStage q) from hexit).mono
    (fun q hq => by
      rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
      exact hq.2)
  segments := hpieces

end WindowInstance

end ConsistentSubmodular

end


