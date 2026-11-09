-- Prove2me | Definitions.Def_PagingDelay_PMD_Algorithm
-- name    : PagingDelay_PMD_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:19.206718+00:00
-- url     : https://prove2.me/theorems/b7f6a0b1-a2cd-4d4a-abd9-6148fbe20b90
-- title:
--   PMD: critical and preemptive services and finite trace
-- statement:
--   The state contains time, antimass, claims and one budget for each dyadic level. It starts with $x_i=\delta$ on the initial cache, $x_{i_0}=(k+1)\delta$ on an arbitrary designated page outside it, and $x_i=1$ elsewhere; claims and budgets start at zero.
--
--   The next critical time is the minimum of the page-specific infima of rule (5), with state and claims frozen and future arrivals joining the pending requests. Pages already at $\delta$ serve arrivals immediately. Equal infima use the arbitrary page order $\pi$. Critical service claims the prescribed proportional overshoot, deposits the path's band lengths, follows the explicit path and resets the served page's claim.
--
--   After critical service, levels are processed in increasing order. A preemptive service opens a hole of mass $1-\delta$, reserves its closing cost, orders pending eligible pages by their effective deadlines (6), and performs round trips while its budget is at least $W$. All temporary states, budget updates and claim resets are recorded, followed by restoration of the starting antimass. Deadline ties use $\pi$.
--
--   The run performs at most $|\sigma|+1$ next-event iterations. This fuel does not assume termination or service: Lemma 2 asks for these properties of this explicit construction. Fractional fetch cost sums weighted positive antimass decreases along the trace. Critical fetch and total critical length select its critical moves. Fractional delay is
--
--   $$C_{\rm delay}=\sum_r\alpha_r d_r(\tau_r-a_r),\qquad
--   \alpha_r=x_{p_r}(a_r^-)-\delta.$$
--
--   Absent serving times have infinite delay, and the mass at arrival is evaluated before all algorithm moves at that instant. Excess uses the offline cache after its entire walk at the same time. The definitions impose no cost bounds and do not require that requests are served.
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Algorithm 1, p. 7; §3, pp. 7–10, (5)–(6); Definitions 4, 8, 16, pp. 11, 13, 17; initialization, p. 27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

noncomputable section

namespace PagingDelay.PMD
open scoped BigOperators Classical

/-- State at the end of one discrete move; claims and budgets are part of the trace. -/
structure Snapshot (n : ℕ) where
  time : ℝ
  x : Fin n → ℝ
  claims : Fin n → ℝ
  budget : ℕ → ℝ

inductive MoveKind (n : ℕ) where
  | critical (p : Fin n)
  | openHole (j : ℕ)
  | visit (p : Fin n)
  | returnTrip (p : Fin n)
  | closeHole (j : ℕ)

structure Move (n : ℕ) where
  before : Snapshot n
  after : Snapshot n
  kind : MoveKind n

structure Execution (n : ℕ) where
  initial : Snapshot n
  current : Snapshot n
  moves : List (Move n)

def initialX {n : ℕ} (k : ℕ) (O₀ : Finset (Fin n)) (i₀ : Fin n) (i : Fin n) : ℝ :=
  if i ∈ O₀ then delta k else if i = i₀ then (k + 1 : ℝ) * delta k else 1

def start {n : ℕ} (k : ℕ) (O₀ : Finset (Fin n)) (i₀ : Fin n) : Execution n :=
  let s : Snapshot n := ⟨0, initialX k O₀ i₀, fun _ => 0, fun _ => 0⟩
  ⟨s, s, []⟩

def push {n : ℕ} (e : Execution n) (s : Snapshot n) (kind : MoveKind n) : Execution n :=
  ⟨e.initial, s, e.moves ++ [⟨e.current, s, kind⟩]⟩

def fractionalBefore {n : ℕ} (e : Execution n) (t : ℝ) : Fin n → ℝ :=
  (((e.moves.filter (fun m => m.after.time < t)).map (fun m => m.after.x)).getLastD e.initial.x)

def fractionalService {n : ℕ} (k : ℕ) (e : Execution n) (r : Request n) : Option ℝ :=
  firstTime ((if fractionalBefore e r.arrival r.page = delta k then [r.arrival] else []) ++
    ((e.moves.filter (fun m => r.arrival ≤ m.after.time ∧ m.after.x r.page = delta k)).map
      (fun m => m.after.time)))

/-- While waiting, future arrivals join; pages held at δ are served immediately.
Existing service times are derived from the actual finite trace, not assumed. -/
def pending {n : ℕ} (k : ℕ) (e : Execution n) (σ : Instance n) (t : ℝ) : Instance n :=
  σ.filter (fun r => r.arrival ≤ t ∧ fractionalService k e r = none)

def pageDelay {n : ℕ} (rs : Instance n) (q : Fin n) (t : ℝ) : ℝ :=
  ((rs.filter (fun r => r.page = q)).map (fun r => (r.delay (Real.toNNReal (t - r.arrival)) : ℝ))).sum

def overshoot {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (e : Execution n)
    (σ : Instance n) (t : ℝ) (q : Fin n) : ℝ :=
  max 0 (pageDelay (pending k e σ t) q t - e.current.claims q - w q)

/-- Rule (5), with x and claims frozen until the next critical service. -/
def CriticalAt {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (e : Execution n)
    (σ : Instance n) (p : Fin n) (t : ℝ) : Prop :=
  e.current.time ≤ t ∧ 0 < overshoot k w e σ t p ∧
    pathLength k w e.current.x p / logFactor k ≤
      ∑ q ∈ Finset.univ.filter (fun q => w q ≤ w p), overshoot k w e σ t q

def nextPageTime {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (e : Execution n)
    (σ : Instance n) (p : Fin n) : Option ℝ :=
  if Set.Nonempty {t | CriticalAt k w e σ p t} then
    some (sInf {t | CriticalAt k w e σ p t}) else none

/-- Earliest page-specific infimum; simultaneous infima are resolved by arbitrary π. -/
def nextEvent {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n)
    (e : Execution n) (σ : Instance n) : Option (ℝ × Fin n) :=
  (((Finset.univ.toList.filterMap (fun p => (nextPageTime k w e σ p).map (fun t => (t,p)))).mergeSort
    (fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ π a.2 ≤ π b.2))))).head?

/-- Equation (6), only the currently pending requests. none is +∞ for empty input. -/
def effectiveDeadline {n : ℕ} (w : Fin n → ℝ) (rs : Instance n) (q : Fin n)
    (t : ℝ) : Option ℝ :=
  if Set.Nonempty {u | t ≤ u ∧ w q < pageDelay rs q u} then
    some (sInf {u | t ≤ u ∧ w q < pageDelay rs q u}) else none

def deadlineLE (a b : Option ℝ) : Prop :=
  match a, b with
  | _, none => True
  | none, some _ => False
  | some u, some v => u ≤ v

/-- CriticalService, including claims, all budget deposits, state change and claim reset.
Division is guarded outside the valid reachable domain; no positivity is assumed. -/
def criticalService {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (σ : Instance n)
    (e : Execution n) (t : ℝ) (p : Fin n) : Execution n :=
  let len := pathLength k w e.current.x p
  let o := overshoot k w e σ t
  let denom := ∑ q ∈ Finset.univ.filter (fun q => w q ≤ w p), o q
  let θ := if denom = 0 then 0 else (len / logFactor k) / denom
  let s : Snapshot n := ⟨t, pathEnd k w e.current.x p,
    fun q => if q = p then 0 else e.current.claims q + (if w q ≤ w p then θ * o q else 0),
    fun j => e.current.budget j + (if w p ≤ level j then bandLength k len (level j) else 0)⟩
  push e s (.critical p)

/-- Round-trip loop. The eligible list is fixed after opening the hole. -/
def roundTrips {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (j : ℕ) :
    List (Fin n) → Execution n → Execution n
  | [], e => e
  | q :: qs, e =>
    if e.current.budget j ≥ level j then
      let saved := e.current.x
      let s : Snapshot n := { e.current with
        x := Function.update saved q (delta k)
        claims := Function.update e.current.claims q 0
        budget := Function.update e.current.budget j
          (e.current.budget j - w q * (saved q - delta k)) }
      let served := push e s (.visit q)
      let returned := push served { s with x := saved } (.returnTrip q)
      roundTrips k w j qs returned
    else e

/-- PreemptiveService(W) from Algorithm 1, including every transient configuration. -/
def preemptiveService {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n)
    (σ : Instance n) (j : ℕ) (e : Execution n) : Execution n :=
  let W := level j
  let xstart := e.current.x
  let mass := ∑ i ∈ Finset.univ.filter (fun i => w i ≤ W), (1 - xstart i)
  if e.current.budget j ≥ 4 * W ∧ mass ≥ 1 - delta k then
    let rs := pending k e σ e.current.time
    let θ := if mass = 0 then 0 else (1 - delta k) / mass
    let s : Snapshot n := { e.current with
      x := fun i => if w i ≤ W then xstart i + θ * (1 - xstart i) else xstart i
      budget := Function.update e.current.budget j (e.current.budget j - W * (1 - delta k)) }
    let E := (Finset.univ.toList.filter (fun q => w q ≤ W ∧ ∃ r ∈ rs, r.page = q)).mergeSort
      (fun p q => decide (
        let a := effectiveDeadline w rs p e.current.time
        let b := effectiveDeadline w rs q e.current.time
        deadlineLE a b ∧ (a ≠ b ∨ π p ≤ π q)))
    let opened := push e s (.openHole j)
    let trips := roundTrips k w j E opened
    push trips { trips.current with x := xstart } (.closeHole j)
  else e

/-- Each next event is a critical service followed by one increasing pass over levels.
Fuel is a construction device; termination and full service are conclusions of Lemma 2. -/
def runFuel {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (π : Fin n ≃ Fin n) (σ : Instance n) :
    ℕ → Execution n → Execution n
  | 0, e => e
  | fuel + 1, e => match nextEvent k w π e σ with
    | none => e
    | some (t,p) =>
      let crit := criticalService k w σ e t p
      let block := (levels w).foldl (fun a j => preemptiveService k w π σ j a) crit
      runFuel k w π σ fuel block

def run {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (O₀ : Finset (Fin n))
    (i₀ : Fin n) (π : Fin n ≃ Fin n) (σ : Instance n) : Execution n :=
  runFuel k w π σ (σ.length + 1) (start k O₀ i₀)

def stepFetch {n : ℕ} (w : Fin n → ℝ) (m : Move n) : ℝ :=
  ∑ i, w i * max 0 (m.before.x i - m.after.x i)

def fractionalFetch {n : ℕ} (w : Fin n → ℝ) (e : Execution n) : ℝ :=
  (e.moves.map (stepFetch w)).sum

def criticalMoves {n : ℕ} (e : Execution n) : List (Move n) :=
  e.moves.filter (fun m => match m.kind with | .critical _ => true | _ => false)

def criticalFetch {n : ℕ} (w : Fin n → ℝ) (e : Execution n) : ℝ :=
  ((criticalMoves e).map (stepFetch w)).sum

def criticalLength {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (e : Execution n) : ℝ :=
  (e.moves.map (fun m => match m.kind with
    | .critical p => pathLength k w m.before.x p | _ => 0)).sum

/-- Definition 8. An unserved request has infinite delay; no real sInf default is used. -/
def fractionalDelay {n : ℕ} (k : ℕ) (e : Execution n) (σ : Instance n) : ENNReal :=
  (σ.map (fun r => ENNReal.ofReal (fractionalBefore e r.arrival r.page - delta k) *
    requestDelay r (fractionalService k e r))).sum

/-- Definition 16; offline cache is evaluated after all its moves at the same instant. -/
def excess {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (O₀ : Finset (Fin n))
    (O : Schedule n) (e : Execution n) : ℝ :=
  (e.moves.map (fun m => match m.kind with
    | .critical p =>
      let c := cacheAfter O₀ O m.after.time
      if p ∈ c then 0 else serviceExcess k w m.before.x p c
    | _ => 0)).sum

end PagingDelay.PMD


