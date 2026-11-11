-- Prove2me | Definitions.Def_PCSFBreach_Main_ActiveConn
-- name    : PCSFBreach_Main_ActiveConn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:01.299726+00:00
-- url     : https://prove2.me/theorems/40b15677-154a-4601-9ed3-fa5471e541a0
-- title:
--   Deactivation times, actively connected sets, A_t/𝒮, gain(𝒮) and st(𝒮) (Definitions 1–5)
-- statement:
--   Fix a run of the primal-dual algorithm (§5, pp. 12–13).
--   1. The **deactivation time** $d_u$ of a vertex $u$ is the largest $t$ such that $u$ belongs to a set of $A_{t'}$ for every $0\le t'<t$ (Definition 1).
--   2. Vertices $u,v$ are **actively connected**, $u\sim v$, if at some time $0\le t\le d_u,d_v$ they lie in a common set of $C_t$ (Definition 2); a set $S\subseteq V$ is actively connected if $u\sim v$ for all $u,v\in S$ (Definition 3).
--   3. For a collection $\mathcal S$ of actively connected sets, $A_t/\mathcal S$ arises from $A_t$ by merging (transitively) sets of $A_t$ intersected by a common $S\in\mathcal S$, and
--   $$\mathrm{gain}(\mathcal S)=2\int_0^\infty\big(|A_t|-|A_t/\mathcal S|\big)\,dt \qquad\text{(Definition 4)}.$$
--   4. $\mathrm{st}(S)$ is the minimum cost of an edge set connecting all vertices of $S$ (a minimum Steiner tree; $0$ if $|S|\le 1$) and $\mathrm{st}(\mathcal S)=\sum_{S\in\mathcal S}\mathrm{st}(S)$ (Definition 5).
--
--   These objects drive the contraction algorithm of Lemma 6.
--
--   **Formalization Note** $|A_t/\mathcal S|$ is the number of connected components of the graph on $A_t$ joining two sets met by a common $S$; the integral is the finite sum over the stages of the run, on which $A_t$ is constant. If no edge set connects $S$ (impossible for an actively connected set) $\mathrm{st}(S)$ is $0$.
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), pp. 12–13, §5, Definitions 1–5

import Mathlib
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
set_option autoImplicit false

namespace PCSFBreach.Main

open Finset

namespace Instance

variable (I : Instance)

open scoped Classical in
/-- `st(S)` (Definition 5, p. 13): the minimum cost of an edge set connecting all vertices of `S`
(a minimum Steiner tree; with nonnegative costs a cheapest connecting edge set contains a tree of
the same cost). `0` if `|S| ≤ 1`. If no edge set connects `S` (never the case for an actively
connected set) the value is `0`. -/
noncomputable def st (S : Finset (Fin I.n)) : ℝ :=
  let feas := (univ : Finset (Finset I.Edge)).filter
    (fun F => ∀ u ∈ S, ∀ v ∈ S, I.Connected F u v)
  if h : feas.Nonempty then feas.inf' h I.edgeCost else 0

/-- `st(𝒮) = Σ_{S ∈ 𝒮} st(S)` for a collection `𝒮` of vertex sets (Definition 5). -/
noncomputable def stColl (𝒮 : Finset (Finset (Fin I.n))) : ℝ := ∑ S ∈ 𝒮, I.st S

end Instance

/-- `|A/𝒮|`: the number of sets of `A/𝒮`, which arises from the family `A` by merging (transitively)
sets of `A` intersected by a common `S ∈ 𝒮` (Definition 4, p. 13): the number of connected
components of the graph on `A` joining two members met by a common `S ∈ 𝒮`. -/
noncomputable def quotCount {V : Type} [DecidableEq V] (A : Finset (Finset V))
    (𝒮 : Finset (Finset V)) : ℕ :=
  Nat.card (SimpleGraph.fromRel
    (fun X Y : A => ∃ S ∈ 𝒮, (S ∩ X.1).Nonempty ∧ (S ∩ Y.1).Nonempty)).ConnectedComponent

namespace PDRun

variable {I : Instance} (R : PDRun I)

/-- The **deactivation time** `d_u` (Definition 1, p. 12): the largest `t` such that for every
`0 ≤ t′ < t`, `u` belongs to some set of `A_{t′}`. -/
noncomputable def deact (u : Fin I.n) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ ∀ t' ∈ Set.Ico (0 : ℝ) t, ∃ A ∈ R.activeAt t', u ∈ A}

/-- `u ∼ v`, `u` and `v` are **actively connected** (Definition 2, p. 12): at some time
`0 ≤ t ≤ d_u, d_v`, `u` and `v` lie in a common set of `C_t`. -/
def ActConn (u v : Fin I.n) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ (∃ S ∈ R.moatsAt t, u ∈ S ∧ v ∈ S) ∧ t ≤ R.deact u ∧ t ≤ R.deact v

/-- `S` is an **actively connected set** (Definition 3, p. 13): a subset of one class of `∼`. -/
def IsActConnSet (S : Finset (Fin I.n)) : Prop := ∀ u ∈ S, ∀ v ∈ S, R.ActConn u v

/-- A collection of actively connected sets. -/
def IsActConnColl (𝒮 : Finset (Finset (Fin I.n))) : Prop := ∀ S ∈ 𝒮, R.IsActConnSet S

/-- `gain(𝒮) = 2 ∫₀^∞ (|A_t| − |A_t/𝒮|) dt` (Definition 4, p. 13). `A_t` is constant on each
stage `[t_k, t_{k+1})` and empty from `t_len` on, so the integral is the finite sum over stages. -/
noncomputable def gain (𝒮 : Finset (Finset (Fin I.n))) : ℝ :=
  2 * ∑ k ∈ range R.len, (R.time (k + 1) - R.time k) *
    (((R.active k).card : ℝ) - (quotCount (R.active k) 𝒮 : ℝ))

end PDRun

end PCSFBreach.Main


