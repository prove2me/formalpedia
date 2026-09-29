-- Prove2me | Definitions.Def_CompetitivePaging_Marking_markingAlgorithm
-- name    : CompetitivePaging_Marking_markingAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:08:43.496266+00:00
-- url     : https://prove2.me/theorems/6ed5307d-fddb-4c1a-9188-ea741eb901f0
-- title:
--   The marking algorithm for the uniform $k$-server problem, its expected cost, and its phases
-- statement:
--   This file defines the randomized **marking algorithm** of Fiat, Karp, Luby, McGeoch, Sleator and Young for the uniform $k$-server (paging) problem, its expected cost on a request sequence, the phases into which it divides a request sequence, and lazy off-line schedules.
--
--   **Setting.** The vertex set $M$ has $n$ elements, enumerated as $e : \{0,\dots,n-1\} \to M$; the "vertices $1, 2, \dots, k$" of the paper are $e(0), \dots, e(k-1)$. The **initial configuration** $C_0$ puts server $i$ on $e(i)$ for $i < k$, and $V = \{e(0), \dots, e(k-1)\}$ is the set of initially covered vertices.
--
--   **The algorithm.** A state is a pair $(\mathrm{cov}, \mathrm{mk})$ of finite sets of vertices: the covered vertices and the marked vertices. Initially $\mathrm{cov} = \mathrm{mk} = V$. On a request to a vertex $r$:
--
--   1. *Marking.* The new mark set is $\mathrm{mk}' = \{r\}$ if $\mathrm{mk} \cup \{r\}$ has $k+1$ elements, and $\mathrm{mk}' = \mathrm{mk} \cup \{r\}$ otherwise: $r$ is marked, and the moment $k+1$ vertices are marked all marks except the one on $r$ are erased.
--   2. *Serving.* If $r \in \mathrm{cov}$, no server moves. Otherwise a vertex $v$ is drawn uniformly at random from $\mathrm{cov} \setminus \mathrm{mk}'$ (the covered unmarked vertices) and its server is moved to $r$, giving $\mathrm{cov}' = (\mathrm{cov} \setminus \{v\}) \cup \{r\}$.
--
--   The marks are updated before the server is chosen. The law of the state after a list $\ell$ of requests is obtained by composing these one-step transition laws. The **fault probability** $P_\ell(r)$ is the probability that $r \notin \mathrm{cov}$ after serving $\ell$, and the **expected cost** of the marking algorithm on $\sigma = (\sigma(0), \dots, \sigma(T-1))$ is
--   $$C_M(\sigma) = \sum_{t=0}^{T-1} P_{\sigma(0..t-1)}\big(\sigma(t)\big).$$
--
--   **Phases.** The marks evolve deterministically. Write $\mathrm{mk}_t$ for the mark set after the first $t$ requests. Request $t$ **starts a phase** if $\mathrm{mk}_t \cup \{\sigma(t)\}$ has $k+1$ elements; the requests $i, \dots, i'-1$ form a **complete phase** if $i < i'$ are consecutive phase starts. For indices $i \le t$, $R(i,t)$ is the set of vertices requested at indices $i, \dots, t-1$, and the expected cost of the marking algorithm on requests $i, \dots, i'-1$ is the corresponding partial sum of fault probabilities. The first phase starts at the first request outside $\{e(0),\dots,e(k-1)\}$, and a phase ends at the request before the one that brings the number of distinct vertices requested in the phase to $k+1$.
--
--   **Lazy schedules.** An off-line schedule $S$ gives the configuration $S_j$ of the $k$ labelled servers just before request $j$. It is **lazy** on $\sigma$ if no server moves when $\sigma(j)$ is covered by $S_j$, and exactly one server, moved to $\sigma(j)$, changes position when it is not.
--
--   These are the objects of Theorem 1 of the paper and of the claims inside its proof.
--
--   **Formalization Note.** The expected cost is the sum of fault probabilities. This equals the expected number of server moves because the algorithm is lazy: one move (of cost $1$ in the uniform metric) per fault, none otherwise. The transition has a third branch, for an uncovered request with no covered unmarked vertex, in which the state keeps its servers; this branch is never reached from the initial state when $k \ge 1$, and it is there only so that the definition is total. Probabilities are in $[0,\infty]$ (`ℝ≥0∞`) and are converted to reals for the cost.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 3, §3 (definition of the marking algorithm); p. 4, proof of Theorem 1 (phases); p. 4, proof of Theorem 1 (lazy algorithms)

import Mathlib
import Definitions.Def_KServer_model

open scoped ENNReal

namespace CompetitivePaging.Marking

/-- The initial server configuration of the marking algorithm on the vertex set `M`,
enumerated as `e : Fin n ≃ M`: server `i` (for `i < k`) sits on the vertex `e i`, i.e. the
servers are on the vertices "1, 2, …, k" of the paper. -/
def initConfig {n k : ℕ} {M : Type*} (e : Fin n ≃ M) (hkn : k ≤ n) : KServer.Config k M :=
  fun i => e (Fin.castLE hkn i)

/-- The set of vertices covered by the initial configuration, `{e 0, …, e (k-1)}`. -/
def initVertices {n k : ℕ} {M : Type*} [DecidableEq M] (e : Fin n ≃ M) (hkn : k ≤ n) :
    Finset M :=
  Finset.univ.image (initConfig e hkn)

/-- A state of the marking algorithm: `covered` is the set of vertices covered by servers and
`marked` is the set of marked vertices. -/
structure State (M : Type*) where
  covered : Finset M
  marked : Finset M

/-- The mark update on a request to `r` (the "Marking" rule): `r` is marked, and the moment
`k + 1` vertices are marked, every mark except the one on `r` is erased. -/
def marksAfter {M : Type*} [DecidableEq M] (k : ℕ) (mk : Finset M) (r : M) : Finset M :=
  if (insert r mk).card = k + 1 then {r} else insert r mk

/-- One step of the marking algorithm on a request to `r`, as a probability distribution
over the next state. The marks are updated first; then (the "Serving" rule) if `r` is
covered no server moves, and otherwise a server is chosen uniformly at random among the
covered unmarked vertices `covered \ mk'` and moved to `r`.
The last branch (`r` uncovered and no covered unmarked vertex) is never reached from the
initial state when `1 ≤ k`; it is given explicitly only to make the definition total, and
there the state keeps its servers. -/
noncomputable def step {M : Type*} [DecidableEq M] (k : ℕ) (s : State M) (r : M) :
    PMF (State M) :=
  let mk' := marksAfter k s.marked r
  if r ∈ s.covered then PMF.pure ⟨s.covered, mk'⟩
  else if h : (s.covered \ mk').Nonempty then
    (PMF.uniformOfFinset (s.covered \ mk') h).map (fun v => ⟨insert r (s.covered.erase v), mk'⟩)
  else PMF.pure ⟨s.covered, mk'⟩

/-- The law of the marking algorithm's state after serving the request list `l`, starting
from the state in which the covered vertices and the marked vertices are both `V`. -/
noncomputable def lawAfter {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (l : List M) :
    PMF (State M) :=
  l.foldl (fun p r => p.bind (fun s => step k s r)) (PMF.pure ⟨V, V⟩)

/-- The probability that the marking algorithm (started with covered = marked = `V`) has no
server on `r` after serving the request list `l`, i.e. the probability that a subsequent
request to `r` is a fault. -/
noncomputable def faultProb {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (l : List M)
    (r : M) : ℝ≥0∞ :=
  (lawAfter k V l).toOuterMeasure {s | r ∉ s.covered}

/-- The expected cost `C_M(σ)` of the marking algorithm on the request sequence `σ`: the sum
over the requests `σ(t)` of the probability that `σ(t)` is not covered just before it is
served. This equals the expected number of server moves because the algorithm is lazy: it
moves exactly one server (at cost `1` in the uniform metric) on an uncovered request and
none on a covered one. -/
noncomputable def markingExpCost {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M)
    (σ : List M) : ℝ :=
  ∑ t : Fin σ.length, (faultProb k V (σ.take t) (σ.get t)).toReal

/-- The marked set after the first `t` requests of `σ` (starting from the marked set `V`).
The marks evolve deterministically: they do not depend on the random choices. -/
def marksAt {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M) (t : ℕ) :
    Finset M :=
  (σ.take t).foldl (marksAfter k) V

/-- Request `t` (0-indexed) of `σ` starts a phase: it is the request at which `k + 1`
vertices become marked, so the marks are reset. -/
def IsPhaseStart {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M) (t : ℕ) :
    Prop :=
  ∃ ht : t < σ.length, (insert (σ.get ⟨t, ht⟩) (marksAt k V σ t)).card = k + 1

/-- The requests with indices `i, i+1, …, i'-1` form a complete phase: `i` and `i'` are
consecutive phase starts. -/
def IsCompletePhase {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (i i' : ℕ) : Prop :=
  IsPhaseStart k V σ i ∧ IsPhaseStart k V σ i' ∧ i < i' ∧
    ∀ u, i < u → u < i' → ¬ IsPhaseStart k V σ u

/-- The set of vertices requested at the indices `i, i+1, …, t-1` of `σ`. -/
def phaseRequested {M : Type*} [DecidableEq M] (σ : List M) (i t : ℕ) : Finset M :=
  ((σ.drop i).take (t - i)).toFinset

/-- The expected cost of the marking algorithm on the requests with indices
`i, i+1, …, i'-1` of `σ`. -/
noncomputable def markingPhaseCost {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M)
    (σ : List M) (i i' : ℕ) : ℝ :=
  ∑ t : Fin σ.length,
    if i ≤ t.val ∧ t.val < i' then (faultProb k V (σ.take t) (σ.get t)).toReal else 0

/-- An (off-line) schedule `S` of `k` servers is lazy on `σ`: `S j` is the configuration just
before request `j`, and at each request no server moves if the requested vertex is covered,
while exactly one server moves, to the requested vertex, if it is not. -/
def IsLazySchedule {k : ℕ} {M : Type*} (σ : List M) (S : ℕ → KServer.Config k M) : Prop :=
  ∀ j : Fin σ.length,
    ((∃ i, S j i = σ.get j) → S (j + 1) = S j) ∧
    ((¬ ∃ i, S j i = σ.get j) → ∃ i, S (j + 1) = Function.update (S j) i (σ.get j))

end CompetitivePaging.Marking


