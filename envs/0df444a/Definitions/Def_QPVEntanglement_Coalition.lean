-- Prove2me | Definitions.Def_QPVEntanglement_Coalition
-- name    : QPVEntanglement_Coalition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:22.746868+00:00
-- url     : https://prove2.me/theorems/37a2d719-a8f8-4bbc-addc-fcdd46c98289
-- title:
--   Adversarial station coalitions (pinned-down Adversary Model)
-- statement:
--   This definition is the **operator-requested pinned-down version** of the paper's operational adversary model (§4, pp.28–29), choices P5–P10 of the mission description.
--
--   A **coalition** against a schedule consists of $n$ **stations** at pairwise distinct positions $\mathrm{pos}_a$ (co-located adversaries are one station). Station $a$ holds $q_a$ qubits and has $N_a$ **events** at times $t_{a,0}\le t_{a,1}\le\cdots$. Event $(a,i)$ has $K_{a,i}\ge1$ outcomes; given the verifier draw $\xi$ and an outcome assignment $\omega$ (one outcome per event), it applies a complete Kraus family $\{K_o\}$ ($\sum_o K_o^\dagger K_o=I$) on the station's qubits and then, for its outcome $o$, an **action**: idle; *absorb* $(h,j)$, which swaps the passing carrier of label $h$ into local qubit $j$; or *launch* $(c,j)$, which swaps local qubit $j$ into a fresh channel qubit travelling to $V_c$. The stations share an arbitrary initial density matrix $\rho_0$.
--
--   **Outgoing registers.** After a launch of qubit $j$ toward $V_c$ at time $t_{a,i}$, no later event of station $a$ before the arrival time $t_{a,i}+|\mathrm{pos}_a-v_c|$ acts on qubit $j$ (its instrument is $M'\otimes I_j$ and its action names another qubit): the launched qubit's register stays unavailable until the verifier receives it (p.29).
--
--   **Causality.** The instrument and the action of $(a,i)$ depend on $(\xi,\omega)$ only through its light-cone **view**: the instructions $(b_k,i_k,r_k)$ whose emission at $T_{k,i_k}-d_{b_k}$ from $v_{b_k}$ has reached $\mathrm{pos}_a$ by $t_{a,i}$; the outcomes of the earlier events of the same station; and the outcomes of the events $(b,i')$ of other stations with $t_{b,i'}+|\mathrm{pos}_a-\mathrm{pos}_b|\le t_{a,i}$.
--
--   This is the class of coalitions over which every protocol-level statement of the mission quantifies.
--
--   **Formalization Note** Adaptive timing is represented by fixed event times with view-dependent operations that may be the identity; every outcome is visible to every other station at light speed (free classical communication); quantum messages between stations are impossible; "no station at the claimed location" is a hypothesis of each theorem, not part of the definition.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §4 Adversary Model, clauses 1–6, pp.28–29; footnotes 21, 24

import Mathlib
import Definitions.Def_QPVEntanglement_Draw

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- The action an event of a station takes after its local operation (pinned model P8–P10).
`absorb h j` swaps the passing verifier carrier of label `h` into local qubit `j`
(P9; "If an incoming verifier qubit is kept, we represent this by swapping the incoming
register with an available reset register", p.29); `launch c j` swaps local qubit `j` into a
fresh channel qubit travelling to `V_c` (P10). -/
inductive Action (L q : ℕ) where
  | idle
  | absorb (h : Fin L) (j : Fin q)
  | launch (c : Fin 2) (j : Fin q)
  deriving DecidableEq

namespace Action

/-- The action names local qubit `j` (absorbs into it or launches it). -/
def Touches {L q : ℕ} (j : Fin q) : Action L q → Prop
  | .idle => False
  | .absorb _ j' => j' = j
  | .launch _ j' => j' = j

end Action

/-- A local operator `M` on `q` qubits acts trivially on qubit `j`, i.e. `M = M' ⊗ I_j`. -/
def ActsTriviallyOn {q : ℕ} (j : Fin q) (M : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ) : Prop :=
  ∀ x y, M x y = if x j = y j then M (Function.update x j 0) (Function.update y j 0) else 0

/-- The events of a coalition: station `a` and the index `i` of one of its events. -/
abbrev Ev {n : ℕ} (N : Fin n → ℕ) : Type := Σ a : Fin n, Fin (N a)

/-- An outcome assignment: one outcome for every event of the whole coalition. -/
abbrev Outcomes {n : ℕ} (N : Fin n → ℕ) (K : (a : Fin n) → Fin (N a) → ℕ) : Type :=
  (e : Ev N) → Fin (K e.1 e.2)

/-- What a station can see of the verifiers' instructions: for each round `k`, `some (b_k, i_k,
r_k)` once the instruction `"challenge, r_k"` emitted by `V_{b_k}` at `T k i_k − d_{b_k}` has
reached position `p` at speed `1` (by time `τ`), `none` before (pinned model P5). -/
noncomputable def instrView {G : Geometry} {m RH s : ℕ} (S : Schedule G m RH s)
    (ξ : Draw m RH s) (p τ : ℝ) : Fin m → Option (Fin 2 × Fin s × Option (Fin (NL m RH))) :=
  open Classical in
  fun k => if S.emit k (ξ.b k) (ξ.i k) + |p - G.v (ξ.b k)| ≤ τ then some (ξ.b k, ξ.i k, ξ.req k)
    else none

/-- The **light-cone view** of event `(a, i)` (pinned model P8, causality): the verifier
instructions that have reached `pos a` by `t a i`, the outcomes of the earlier events of the
same station (`i' < i`), and the outcomes of the events `(b, i')` of other stations with
`t b i' + |pos a − pos b| ≤ t a i` (outcomes broadcast at speed `1`). Nothing else: not the
BB84 descriptions, not round outcomes, not instructions still in flight. -/
noncomputable def view {G : Geometry} {m RH s n : ℕ} (S : Schedule G m RH s)
    (pos : Fin n → ℝ) {N : Fin n → ℕ} (t : (a : Fin n) → Fin (N a) → ℝ)
    {K : (a : Fin n) → Fin (N a) → ℕ} (a : Fin n) (i : Fin (N a)) (ξ : Draw m RH s)
    (ω : Outcomes N K) :
    (Fin m → Option (Fin 2 × Fin s × Option (Fin (NL m RH)))) × ((e : Ev N) → Option (Fin (K e.1 e.2))) :=
  open Classical in
  (instrView S ξ (pos a) (t a i),
    fun e => if (e.1 = a ∧ e.2.val < i.val) ∨ (e.1 ≠ a ∧ t e.1 e.2 + |pos a - pos e.1| ≤ t a i)
      then some (ω e) else none)

/-- **A coalition of adversarial stations** against the protocol with schedule `S` (Adversary
Model, clauses 1–6, pp.28–29), in the operator-requested pinned-down model P6–P10. Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), §4 "Adversary Model", pp.28–29.

* `n` stations at pairwise distinct fixed positions `pos a` (clause 1; co-located adversaries
  are merged into one station, P6);
* station `a` holds `q a` qubits, the matrix index `Fin (q a) → Fin 2` (clause 3, P7);
* station `a` has `N a` events at times `t a i`, nondecreasing in `i` (events at the same time
  happen in list order; "Local quantum operations are instantaneous", clause 4);
* event `(a, i)` has `K a i ≥ 1` outcomes; given the verifier draw `ξ` and the outcome
  assignment `ω` it applies the local instrument `kraus a i ξ ω` (a complete Kraus family on
  `H_a`, one Kraus operator per recorded outcome, footnote 24) and then the action
  `act a i ξ ω o` for its outcome `o`;
* the stations share an arbitrary initial density matrix `ρ₀` on all their qubits (clause 5);
* **outgoing registers stay occupied until received** (clause 6, p.29): after a launch of qubit
  `j` toward `V_c` at time `t a i`, no later event of station `a` before the arrival time
  `t a i + |pos a − v_c|` acts on qubit `j` (its instrument is `M' ⊗ I_j` and its action names
  another qubit); qubit `j` *is* the outgoing register of that launch;
* **causality**: `kraus a i` and `act a i` depend on `(ξ, ω)` only through the light-cone view
  of `(a, i)` (clause 4; "Every wire goes from an earlier operation to a later one", p.28).

**Formalization Note.** Adaptive timing (p.29) is represented by fixed event times with
view-dependent operations that may be the identity (P8a; "An unused operation acts as the
identity"); classical communication is free and every outcome is visible to every other station
at light speed (P8b); classical registers are free and are the outcome records; quantum
messages between stations are impossible (only absorb/launch touch carriers and channels). The
hypothesis "no adversary at the claimed location" is *not* a field: it is a hypothesis of each
theorem. Outcome sets are `Fin (K a i)` (any finite nonempty set). -/
structure Coalition {G : Geometry} {m RH s : ℕ} (S : Schedule G m RH s) where
  /-- number of stations -/
  n : ℕ
  /-- station positions -/
  pos : Fin n → ℝ
  pos_injective : Function.Injective pos
  /-- number of qubits of each station -/
  q : Fin n → ℕ
  /-- number of events of each station -/
  N : Fin n → ℕ
  /-- event times -/
  t : (a : Fin n) → Fin (N a) → ℝ
  t_mono : ∀ a, Monotone (t a)
  /-- number of outcomes of each event -/
  K : (a : Fin n) → Fin (N a) → ℕ
  K_pos : ∀ a i, 0 < K a i
  /-- shared initial state of all station qubits -/
  ρ₀ : Matrix ((Σ a : Fin n, Fin (q a)) → Fin 2) ((Σ a : Fin n, Fin (q a)) → Fin 2) ℂ
  ρ₀_density : ρ₀.PosSemidef ∧ ρ₀.trace = 1
  /-- the local instrument of each event -/
  kraus : (a : Fin n) → (i : Fin (N a)) → Draw m RH s → Outcomes N K → Fin (K a i) →
    Matrix (Fin (q a) → Fin 2) (Fin (q a) → Fin 2) ℂ
  kraus_complete : ∀ a i ξ ω, ∑ o, (kraus a i ξ ω o)ᴴ * kraus a i ξ ω o = 1
  /-- the action of each event, given its own outcome -/
  act : (a : Fin n) → (i : Fin (N a)) → Draw m RH s → Outcomes N K → Fin (K a i) →
    Action (NL m RH) (q a)
  /-- a launched qubit's register is unavailable until the verifier receives it (p.29: "Every
  outgoing quantum register from an adversary remains included in the sending adversary's
  quantum-register size and unavailable for reuse until the verifier receives or discards its
  state") -/
  launch_locked : ∀ (a : Fin n) (i i' : Fin (N a)) (ξ : Draw m RH s) (ω : Outcomes N K) (c : Fin 2)
    (j : Fin (q a)), act a i ξ ω (ω ⟨a, i⟩) = .launch c j → i < i' →
      t a i' < t a i + |pos a - G.v c| →
      ∀ o, ActsTriviallyOn j (kraus a i' ξ ω o) ∧ ¬ (act a i' ξ ω o).Touches j
  /-- causality: equal light-cone views give equal instruments and actions -/
  causal : ∀ a i ξ ξ' (ω ω' : Outcomes N K), view S pos t a i ξ ω = view S pos t a i ξ' ω' →
    kraus a i ξ ω = kraus a i ξ' ω' ∧ act a i ξ ω = act a i ξ' ω'

end QPVEntanglement


