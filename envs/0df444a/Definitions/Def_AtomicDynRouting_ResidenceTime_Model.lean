-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Model
-- name    : AtomicDynRouting_ResidenceTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:37.520576+00:00
-- url     : https://prove2.me/theorems/9d5cec82-0d9b-4119-9551-0852e4fbb46f
-- title:
--   §2.2–2.5, (A1)–(A2), Definition 1, §3, §3.1, pp. 5–7 — atomic dynamic routing runs, exit times, Gζ, A_{ζ,p}, B_{ζ,p}(r0), exiting Gζ
-- statement:
--   This file fixes the atomic dynamic routing (ADR) model of Cao, Chen, Chen and Wang (§2.2–2.5) on a unit-length, unit-capacity network $G$, and the objects of §3.1 attached to a focal agent $\zeta$.
--
--   **Agents and runs.** Time starts at $0$. $\Delta$ is the set of agents; it may be infinite. Agent $i$ enters $G$ at an integer time $r_i$ at his origin $o_i$ and follows his route, a nonempty $o_i$-$d_i$ path $(e^i_0,\dots,e^i_{m_i-1})$ to his destination $d_i$. At each integer time finitely many agents enter. A run records, for each agent $i$ and each position $j$ on his route, the integer time $\ell_i(j)$ at which $i$ leaves the buffer of $e^i_j$, or $\ell_i(j)=\infty$ if he never leaves it.
--
--   **Dynamics.** Each edge has a buffer at its tail (A1). Agent $i$ enters the buffer of $e^i_0$ at time $a_i(0)=r_i$. If he leaves the buffer of $e^i_j$ at time $\ell_i(j)$, he traverses $e^i_j$ in one time unit and enters the buffer of the next edge at once, so $a_i(j+1)=\ell_i(j)+1$. He is in the buffer of $e^i_j$ at every integer time $s$ with $a_i(j)\le s\le \ell_i(j)$, and $a_i(j)\le \ell_i(j)$. Buffer regulation (A2) with unit capacity: at every integer time $s$, whenever the buffer of an edge $e$ contains an agent, **exactly one** agent leaves it at time $s$. No rule says which agent leaves: every choice consistent with (A2) is a run.
--
--   **Exit and residence times.** Agent $i$ exits $G$ at time $t_i=\ell_i(m_i-1)+1$, when he reaches $d_i$ (§2.5), and is *inside* $G$ at the integer times $s$ with $r_i\le s<t_i$. His residence time (Definition 1) is $t_i-r_i$.
--
--   **The focal agent.** Fix $\zeta\in\Delta$ with entry time $r$ (§3).
--
--   1. $G_\zeta$ is the subnetwork composed of all $o_\zeta$-$d_\zeta$ paths of $G$ (its edge set).
--   2. $A_{\zeta,p}$ is the set of agents who enter $G$ after time $r$ and use at least one edge of $G_\zeta$.
--   3. For an integer time $r_0$, $B_{\zeta,p}(r_0)$ is the set of agents $i\ne\zeta$ who enter $G$ no later than $r$, are still inside $G$ at time $r_0$, and use at least one edge of $G_\zeta$.
--   4. An agent $i$ using an edge of $G_\zeta$ *exits $G_\zeta$* when he reaches the head of the last edge of his route lying in $G_\zeta$, the sink of the path "route of $i$ $\cap$ $G_\zeta$" (§3.1, p. 7).
--
--   The model is shared by every statement of the mission.
--
--   **Formalization Note.** `RunData` holds the raw data (entry times, routes, origins, destinations, leave times in $\mathbb N\cup\{\infty\}$ as `ℕ∞`), and `IsADR N R` states that they form a run: routes are nonempty origin-destination paths, finitely many agents enter per time, $a_i(j)\le\ell_i(j)$, and (A2) as unique existence of the leaver of each nonempty buffer at each time. Since $\ell_i(j)=s$ forces $i$ to be in the buffer at $s$, nobody leaves an empty buffer, so at most one agent leaves a buffer at any time (unit capacity). Leave times may be $\infty$, so a run need not serve every agent, as in the paper (p. 7: an agent "may be delayed by an infinite number of later coming agents"); then exit times are $\infty$ too. Route positions are $0$-based. Routes are nonempty: an agent whose origin is his destination never uses an edge.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), pp. 5–7 (PDF 6–8), §2.2–2.5, (A1), (A2), Definition 1, §3 (Gζ), §3.1 (Aζ,p, Bζ,p(r0), exiting Gζ)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

namespace AtomicDynRouting.ResidenceTime

/-- The raw data of an atomic dynamic routing (§2.2–2.5, pp. 5–6) with agent set `ι` (the set `Δ`,
of any cardinality):
* `entry i` is the integer time at which agent `i` enters `G` at his origin;
* `route i` is his route (OD path) as a list of edges, `orig i` and `dest i` his origin and
  destination;
* `leave i j` is the integer time at which `i` leaves the buffer of the `j`-th edge of his route
  (`j` is `0`-based; only `j < (route i).length` is meaningful), or `⊤` if he never leaves it: the
  model does not force an agent to be served (§3.1, p. 7: without the hypothesis of Theorem 1 "the
  focal agent ζ may be delayed by an infinite number of later coming agents").
Which of these data form an ADR profile is the predicate `IsADR`. -/
structure RunData (ι E V : Type) where
  entry : ι → ℕ
  route : ι → List E
  orig : ι → V
  dest : ι → V
  leave : ι → ℕ → ℕ∞

namespace RunData

variable {ι E V : Type} (R : RunData ι E V)

/-- The time agent `i` enters the buffer of the `j`-th edge of his route: his entry time for the
first edge (§2.5, first bullet), and otherwise one unit after he left the previous buffer (unit
transit time, §2.5 second bullet, and (A1): he enters the next buffer immediately); `⊤` if he
never left the previous buffer. -/
def arrive (i : ι) (j : ℕ) : ℕ∞ :=
  if j = 0 then (R.entry i : ℕ∞) else R.leave i (j - 1) + 1

/-- Agent `i` is in the buffer of the `j`-th edge of his route at the integer time `s`: from the
time he enters it up to and including the time he leaves it (§2.5, p. 6: "when i leaves a buffer at
time r, he is also in the buffer at time r"). -/
def inBuf (i : ι) (j s : ℕ) : Prop :=
  j < (R.route i).length ∧ R.arrive i j ≤ (s : ℕ∞) ∧ (s : ℕ∞) ≤ R.leave i j

/-- The exit time of agent `i`: he leaves the buffer of the last edge of his route at
`leave i (len - 1)`, reaches its head, his destination, one unit later and exits `G` at once
(§2.5, second and fourth bullets); `⊤` if he never exits. -/
def exitTime (i : ι) : ℕ∞ :=
  R.leave i ((R.route i).length - 1) + 1

/-- The residence time of agent `i` (Definition 1, p. 6): total transit plus waiting time, i.e. the
difference between his exit and entry times (§2.5). -/
def residenceTime (i : ι) : ℕ∞ :=
  R.exitTime i - (R.entry i : ℕ∞)

/-- Agent `i` is inside `G` at time `t`: `t ∈ [s, t_exit)` (§2.5, p. 6). -/
def inside (i : ι) (t : ℕ) : Prop :=
  R.entry i ≤ t ∧ (t : ℕ∞) < R.exitTime i

end RunData

variable {ι E V : Type}

/-- `IsADR N R`: the data `R` form an atomic dynamic routing on the unit-length, unit-capacity
network `N` (§2.2–2.5, pp. 5–6):
1. every route is a nonempty `orig i`-`dest i` path of `N`;
2. finitely many agents enter at each integer time (§2.2);
3. an agent leaves a buffer no earlier than he enters it;
4. (A2) with unit capacity (§2.3–2.4): at each integer time `s`, whenever the buffer of an edge `e`
   is nonempty, exactly one agent leaves it at time `s`. No rule selects the leaver.
Unit transit times and (A1) are built into `RunData.arrive`. -/
def IsADR (N : Network V E) (R : RunData ι E V) : Prop :=
  (∀ i, N.IsPathFrom (R.orig i) (R.dest i) (R.route i) ∧ R.route i ≠ []) ∧
  (∀ t : ℕ, {i | R.entry i = t}.Finite) ∧
  (∀ i j, j < (R.route i).length → R.arrive i j ≤ R.leave i j) ∧
  (∀ (e : E) (s : ℕ), (∃ i j, R.inBuf i j s ∧ (R.route i)[j]? = some e) →
    ∃! p : ι × ℕ, p.2 < (R.route p.1).length ∧ (R.route p.1)[p.2]? = some e ∧
      R.leave p.1 p.2 = (s : ℕ∞))

/-- `Gζ` (§3, p. 7): the subnetwork of `G` composed of all `oζ`-`dζ` paths, as its edge set. -/
def Gz (N : Network V E) (R : RunData ι E V) (ζ : ι) : Set E :=
  {e | ∃ P : List E, N.IsPathFrom (R.orig ζ) (R.dest ζ) P ∧ e ∈ P}

/-- Agent `i` uses at least one edge of `Gζ`. -/
def usesGz (N : Network V E) (R : RunData ι E V) (ζ i : ι) : Prop :=
  ∃ e ∈ R.route i, e ∈ Gz N R ζ

/-- `A_{ζ,p}` (§3.1, p. 7): the agents who enter `G` later than `ζ` and use an edge of `Gζ`. -/
def Aset (N : Network V E) (R : RunData ι E V) (ζ : ι) : Set ι :=
  {i | R.entry ζ < R.entry i ∧ usesGz N R ζ i}

/-- `B_{ζ,p}(r0)` (§3.1, p. 7): the agents other than `ζ` who enter `G` no later than `ζ`, are
still inside `G` at time `r0`, and use an edge of `Gζ`. -/
def Bset (N : Network V E) (R : RunData ι E V) (ζ : ι) (r0 : ℕ) : Set ι :=
  {i | i ≠ ζ ∧ R.entry i ≤ R.entry ζ ∧ R.inside i r0 ∧ usesGz N R ζ i}

/-- The time agent `i` exits `Gζ` (§3.1, p. 7): he reaches the sink of the path
`route i ∩ Gζ`, i.e. the head of the last edge of his route lying in `Gζ`, one unit after he leaves
its buffer. Meaningful when `i` uses an edge of `Gζ`; for `ζ` himself it is `exitTime ζ`. -/
noncomputable def exitGz (N : Network V E) (R : RunData ι E V) (ζ i : ι) : ℕ∞ :=
  R.leave i (sSup {j : ℕ | j < (R.route i).length ∧ ∃ e, (R.route i)[j]? = some e ∧ e ∈ Gz N R ζ}) + 1

end AtomicDynRouting.ResidenceTime


