-- Prove2me | Definitions.Def_DecDynMatch_Supplement_scpcExec
-- name    : DecDynMatch_Supplement_scpcExec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:30:52.595855+00:00
-- url     : https://prove2.me/theorems/73131b27-e94b-4461-baa7-48ad4d53ac79
-- title:
--   The SC-PC execution and its realized matching $M_t$
-- statement:
--   Fix an instance $I$, the arms' private orders, and realized utilities $R_t(i,k)$ (what player $i$ observes if matched with arm $k$ in round $t$) and $S_t(k,i)$ (what arm $k$ observes). In each round $t$: every player applies its round start and chooses its proposal; each arm $k$ receives the **active** players proposing to it and runs one round of Algorithm 3; accepted players observe $R_t(i,k)$ and arms observe $S_t(k,i)$; every player applies its feedback. Players are in their initial state at every round $t\le b_i$; arms start unstarted. The accepted pairs form the realized matching $M_t$.
--
--   SC-PC is deterministic given the observations, so $M_t$ is a function of the instance, the orders and the observation tables.
--
--   **Formalization Note** Observations are full tables (potential outcomes); only matched entries are read, so every adaptive reward process is represented. BUS is arm 0 and PARK arm 1.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithms 2–7, pp.29–35; §2.2, p.4; §5.1, p.12

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_playerRound
import Definitions.Def_DecDynMatch_Supplement_armStep

namespace DecDynMatch.Supplement

open DecDynMatch

/-- The global state of an SC-PC execution: every player's local state and every arm's state
(`none` before its first proposal). -/
structure GState (K : ℕ) (ι : Type*) where
  ps : ι → PState K
  as : Fin K → Option (AState ι)

variable {K : ℕ} {ι : Type*} [Fintype ι]

open Classical in
/-- One global round `t` of SC-PC from global state `g`, with player-side realized utilities
`R t i k` and arm-side realized utilities `S t k i` of each pair: players apply the round-start
checks and choose their proposals; arm `k` receives the active players proposing to it and accepts
by Algorithm 3; accepted players observe `R t i k`, arms observe `S t k i`; players apply feedback.
Returns the new global state and the realized matching `Mₜ`. -/
noncomputable def roundOut (I : Instance K ι) (ord : Fin K → ι → ℕ) (R : ℕ → ι → Fin K → ℝ)
    (S : ℕ → Fin K → ι → ℝ) (t : ℕ) (g : GState K ι) : GState K ι × (ι → Option (Fin K)) :=
  let ch : ι → PState K × Fin K × PType := fun i => pChoose I (pStart (g.ps i))
  let props : Fin K → Finset ι := fun k => (active I t).filter (fun i => (ch i).2.1 = k)
  let arms : Fin K → Option ι × Option (AState ι) :=
    fun k => armStep K (ord k) (g.as k) (props k) (fun i => S t k i)
  let acc : ι → Bool := fun i => decide (i ∈ active I t ∧ (arms (ch i).2.1).1 = some i)
  let M : ι → Option (Fin K) := fun i => if acc i = true then some (ch i).2.1 else none
  let ps' : ι → PState K :=
    fun i => pFinish I (ch i).1 (ch i).2.1 (ch i).2.2 (acc i) (R t i (ch i).2.1)
  (⟨ps', fun k => (arms k).2⟩, M)

/-- Global state before round `t`: players hold `pinit I` in every round `t ≤ bᵢ` (they start
fresh at entry); arms start unstarted. -/
noncomputable def gpre (I : Instance K ι) (ord : Fin K → ι → ℕ) (R : ℕ → ι → Fin K → ℝ)
    (S : ℕ → Fin K → ι → ℝ) : ℕ → GState K ι
  | 0 => ⟨fun _ => pinit I, fun _ => none⟩
  | t + 1 =>
      let g' := (roundOut I ord R S t (gpre I ord R S t)).1
      ⟨fun i => if t + 1 ≤ I.b i then pinit I else g'.ps i, g'.as⟩

/-- **The realized matching of SC-PC.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), App. C.1, pp.29–35 (Algorithms 2–7 and (46)–(51)),
§2.2, p.4 ("The accepted player-arm pairs form the realized matching Mₜ"), and §5.1, p.12.

`Mpc I ord R S t` is the realized matching of round `t` when SC-PC runs on instance `I` with arm
private orders `ord` and realized utilities `R` (players) and `S` (arms). SC-PC is deterministic
given these observations.

**Formalization Note.**
* Arm `k`'s private order `≺` is the injective rank `ord k : ι → ℕ` (`i ≺ j ↔ ord k i < ord k j`).
* The realized utilities are given as full tables `R t i k`, `S t k i` (potential outcomes); only
  the entries of matched pairs are ever read, so every adaptive reward process is such a table.
* BUS = arm 0 and PARK = arm 1, as in SC-DA. Inactive players' states are computed but never reach
  an arm (only active players propose). -/
noncomputable def Mpc (I : Instance K ι) (ord : Fin K → ι → ℕ) (R : ℕ → ι → Fin K → ℝ)
    (S : ℕ → Fin K → ι → ℝ) (t : ℕ) : ι → Option (Fin K) :=
  (roundOut I ord R S t (gpre I ord R S t)).2

end DecDynMatch.Supplement


