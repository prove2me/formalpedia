-- Prove2me | Definitions.Def_QPVEntanglement_Supplement_CoalitionD
-- name    : QPVEntanglement_Supplement_CoalitionD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:17:52.060206+00:00
-- url     : https://prove2.me/theorems/54cf401d-6fa9-4745-a531-48830e2c96a3
-- title:
--   A coalition of adversarial stations in $\mathbb R^d$
-- statement:
--   This definition belongs to the **operator-requested pinned-down model** of the mission (choices P6–P10 of the mission description). It carries the model from the line $\mathbb R$ to $\mathbb R^d$ and changes nothing else.
--
--   Fix a $d$-dimensional mobile-verifier geometry ($\iota$, verifiers at $\iota(v_0),\iota(v_1)$) and a schedule $S$ of the protocol of Figure 3. A **coalition in $\mathbb R^d$** consists of:
--
--   1. $n$ stations at pairwise distinct positions $\mathrm{pos}_a\in\mathbb R^d$, anywhere in space, off the verifier axis included;
--   2. for each station $a$, a register of $q_a$ qubits and $N_a$ events at nondecreasing times $t_{a,0}\le t_{a,1}\le\cdots$;
--   3. for each event $(a,i)$, a number $K_{a,i}\ge1$ of outcomes. Given the verifiers' random draw $\xi$ and an assignment $\omega$ of outcomes to all events, the event applies a complete family of Kraus operators $\{M^{a,i}_o(\xi,\omega)\}_{o}$ on its station's register, $\sum_o M_o^\dagger M_o=I$. Its outcome $o$ then selects an action: stay idle, absorb a passing verifier carrier into a local qubit, or launch a local qubit to a verifier $V_c$;
--   4. an arbitrary shared initial density matrix $\rho_0$ on all station qubits;
--   5. **launched registers stay occupied**: after a launch of qubit $j$ toward $V_c$ at time $t$, no later event of the station before the arrival time $t+\|\mathrm{pos}_a-\iota(v_c)\|_2$ acts on qubit $j$;
--   6. **causality**: the instrument and the action of event $(a,i)$ depend on $(\xi,\omega)$ only through its light-cone view. The view consists of the verifier instructions that can have reached $\mathrm{pos}_a$ by $t_{a,i}$ at speed $1$ in the Euclidean distance, the outcomes of the station's earlier events, and the outcomes of other stations' events $(b,i')$ with $t_{b,i'}+\|\mathrm{pos}_a-\mathrm{pos}_b\|_2\le t_{a,i}$.
--
--   This is the class of coalitions in the paper's mobile-verifier security notion (Definition 2: "every finite coalition of adversaries having some fixed locations in $\mathbb R^d$"), against the $d$-dimensional version of the protocol (Definition 4).
--
--   **Formalization Note** Field for field the published one-dimensional `QPVEntanglement.Coalition`, with positions in `EuclideanSpace ℝ (Fin d)` and every travel time the Euclidean distance. Instructions are visible at every point once they can have arrived from the issuing verifier at light speed. In the paper the instruction travels along the axis (p.48), so this gives the coalition more information. "No station at the claimed location" is a hypothesis of each theorem, not a field.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §4 Adversary Model, clauses 1–6, pp.28–29; Definition 2, p.28; Definition 4, p.29; Theorem 8, p.46

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition
import Definitions.Def_QPVEntanglement_Supplement_GeometryD

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement.Supplement

open QPVEntanglement

/-- What a station at `p ∈ ℝ^d` can see of the verifiers' instructions: for each round `k`,
`some (b_k, i_k, r_k)` once the instruction emitted by `V_{b_k}` (at `ι (v_{b_k})`) at time
`T k i_k − d_{b_k}` can have reached `p` at speed `1` in the Euclidean distance (by time `τ`),
`none` before. The `d`-dimensional version of the published `QPVEntanglement.instrView`. -/
noncomputable def instrViewD {d : ℕ} (GD : GeometryD d) {m RH s : ℕ}
    (S : Schedule GD.G m RH s) (ξ : Draw m RH s) (p : EuclideanSpace ℝ (Fin d)) (τ : ℝ) :
    Fin m → Option (Fin 2 × Fin s × Option (Fin (NL m RH))) :=
  open Classical in
  fun k => if S.emit k (ξ.b k) (ξ.i k) + dist p (GD.verifier (ξ.b k)) ≤ τ then
    some (ξ.b k, ξ.i k, ξ.req k) else none

/-- The **light-cone view** of event `(a, i)` in `ℝ^d`: the verifier instructions that can have
reached `pos a` by `t a i`, the outcomes of the earlier events of the same station (`i' < i`),
and the outcomes of the events `(b, i')` of other stations with
`t b i' + dist (pos a) (pos b) ≤ t a i`. The `d`-dimensional version of the published
`QPVEntanglement.view` (Euclidean distance in place of `|·|`). -/
noncomputable def viewD {d : ℕ} (GD : GeometryD d) {m RH s n : ℕ} (S : Schedule GD.G m RH s)
    (pos : Fin n → EuclideanSpace ℝ (Fin d)) {N : Fin n → ℕ} (t : (a : Fin n) → Fin (N a) → ℝ)
    {K : (a : Fin n) → Fin (N a) → ℕ} (a : Fin n) (i : Fin (N a)) (ξ : Draw m RH s)
    (ω : Outcomes N K) :
    (Fin m → Option (Fin 2 × Fin s × Option (Fin (NL m RH)))) ×
      ((e : Ev N) → Option (Fin (K e.1 e.2))) :=
  open Classical in
  (instrViewD GD S ξ (pos a) (t a i),
    fun e => if (e.1 = a ∧ e.2.val < i.val) ∨ (e.1 ≠ a ∧ t e.1 e.2 + dist (pos a) (pos e.1) ≤ t a i)
      then some (ω e) else none)

/-- **A coalition of adversarial stations in `ℝ^d`** against the `d`-dimensional mobile-verifier
version (Definition 4, p.29) of the protocol with schedule `S` (Adversary Model, clauses 1–6,
pp.28–29), in the operator-requested pinned-down model P6–P10 of the mission. Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Definition 2 ("every finite coalition of adversaries
`(P₁, …, P_n)` having some fixed locations in `ℝ^d \ {x}`"), p.28, §4 "Adversary Model",
pp.28–29, and Theorem 8, p.46.

Field for field the published one-dimensional `QPVEntanglement.Coalition`, with station
positions `pos a ∈ ℝ^d` (pairwise distinct) and every travel time the Euclidean distance (speed
of light `1`):
* station `a` holds `q a` qubits and has `N a` events at nondecreasing times `t a i`;
* event `(a, i)` has `K a i ≥ 1` outcomes; given the verifier draw `ξ` and the outcome
  assignment `ω` it applies the complete Kraus family `kraus a i ξ ω` on its qubits and then
  the action `act a i ξ ω o` (idle, absorb a passing carrier, or launch a qubit to `V_c`);
* the stations share an arbitrary initial density matrix `ρ₀`;
* **outgoing registers stay occupied until received**: after a launch of qubit `j` toward `V_c`
  at time `t a i`, no later event of station `a` before the arrival time
  `t a i + dist (pos a) (ι (v_c))` acts on qubit `j`;
* **causality**: `kraus a i` and `act a i` depend on `(ξ, ω)` only through the light-cone view
  `viewD` of `(a, i)`.

**Formalization Note.** The same modelling choices as the published one-dimensional model
(P6–P10): adaptive timing by fixed event times with view-dependent operations; classical
communication free, every outcome visible at light speed; no quantum messages between stations.
Stations may sit anywhere in `ℝ^d`, off the verifier axis included; "no adversary at the claimed
location" is a hypothesis of the theorem, not a field. Instructions are visible at every point at
Euclidean light speed from the issuing verifier (the paper's instructions travel along the axis,
p.48; seeing them earlier only helps the coalition). -/
structure CoalitionD {d : ℕ} (GD : GeometryD d) {m RH s : ℕ} (S : Schedule GD.G m RH s) where
  /-- number of stations -/
  n : ℕ
  /-- station positions in `ℝ^d` -/
  pos : Fin n → EuclideanSpace ℝ (Fin d)
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
  /-- a launched qubit's register is unavailable until the verifier receives it (p.29) -/
  launch_locked : ∀ (a : Fin n) (i i' : Fin (N a)) (ξ : Draw m RH s) (ω : Outcomes N K) (c : Fin 2)
    (j : Fin (q a)), act a i ξ ω (ω ⟨a, i⟩) = .launch c j → i < i' →
      t a i' < t a i + dist (pos a) (GD.verifier c) →
      ∀ o, ActsTriviallyOn j (kraus a i' ξ ω o) ∧ ¬ (act a i' ξ ω o).Touches j
  /-- causality: equal light-cone views give equal instruments and actions -/
  causal : ∀ a i ξ ξ' (ω ω' : Outcomes N K), viewD GD S pos t a i ξ ω = viewD GD S pos t a i ξ' ω' →
    kraus a i ξ ω = kraus a i ξ' ω' ∧ act a i ξ ω = act a i ξ' ω'

end QPVEntanglement.Supplement


