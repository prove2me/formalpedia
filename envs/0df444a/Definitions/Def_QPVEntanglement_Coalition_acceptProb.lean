-- Prove2me | Definitions.Def_QPVEntanglement_Coalition_acceptProb
-- name    : QPVEntanglement_Coalition_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:46.747462+00:00
-- url     : https://prove2.me/theorems/d4fe417d-e9a6-45e7-86ee-822a9aa6b542
-- title:
--   Acceptance probability of a coalition
-- statement:
--   This definition is part of the **operator-requested pinned-down model** (choice P11).
--
--   Fix a draw $\xi$ and an outcome assignment $\omega$. The global state starts as $\rho_0\otimes\bigotimes_h|\psi_h\rangle\langle\psi_h|\otimes|0\cdots0\rangle\langle0\cdots0|$ (stations, carriers, channel qubits). Events are processed in order of (time, station, index): each applies the Kraus operator of its recorded outcome on its station, then its action. An absorption of carrier $h$ is **effective** iff the station lies on the closed segment between the verifiers, the event happens exactly when the carrier (sent by $V_0$ at its send time, speed $1$ toward $V_1$) passes it, and $h$ was not absorbed before. The path is **accepting** iff (A1) every carrier is effectively absorbed and (A2) every round $k$ has exactly one **warranted response** (a launch to $V_{b_k}$ arriving exactly at $T_{k,i_k}+d_{b_k}$) and every launch arriving by $T_{\mathrm{end}}$ is a warranted response. Its weight is $\mathrm{Re}\,\mathrm{tr}(P\rho_{\mathrm{init}}P^\dagger)$, where $P$ is the product of the processed operators followed by the projector onto $|\psi_{r_k}\rangle$ on the channel qubit of each round's warranted response. Then
--
--   $$\Pr[\text{accept}]=\frac1{|\Xi|}\sum_\xi\sum_\omega[\text{accepting}]\cdot\mathrm{Re}\,\mathrm{tr}(P\rho_{\mathrm{init}}(\xi)P^\dagger).$$
--
--   **Formalization Note** The verifiers never announce an abort (footnote 23: the experiment continues and outputs $1$ iff every round passes); arrivals after $T_{\mathrm{end}}$ are ignored; the literal BB84 description of Figure 3 is used.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Figure 3, p.31; protocol rules 1–5, pp.30–32; footnote 23, p.37

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- The rank-one projector `|v⟩⟨v|` on `ℂ²`. -/
noncomputable def proj (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec v (star v)

namespace Coalition

variable {G : Geometry} {m RH s : ℕ} {S : Schedule G m RH s} (C : Coalition S)

/-- The qubit wires of an execution: the stations' qubits, one carrier qubit per BB84 label,
and one channel qubit per event (the qubit a launch at that event sends). -/
abbrev Wire : Type := (Σ a : Fin C.n, Fin (C.q a)) ⊕ (Fin (NL m RH) ⊕ Ev C.N)

/-- Computational-basis configurations of all wires: the matrix index of the global state. -/
abbrev Config : Type := C.Wire → Fin 2

/-- Qubit `j` of station `a`. -/
def stQ (a : Fin C.n) (j : Fin (C.q a)) : C.Wire := Sum.inl ⟨a, j⟩
/-- The carrier qubit of label `h`. -/
def carrier (h : Fin (NL m RH)) : C.Wire := Sum.inr (Sum.inl h)
/-- The channel qubit of event `e`. -/
def chan (e : Ev C.N) : C.Wire := Sum.inr (Sum.inr e)

/-- A local operator on station `a`'s register `H_a`, tensored with the identity on every
other wire. -/
noncomputable def liftStation (a : Fin C.n)
    (M : Matrix (Fin (C.q a) → Fin 2) (Fin (C.q a) → Fin 2) ℂ) : Matrix C.Config C.Config ℂ :=
  open Classical in
  fun x y => if ∀ w, (∀ j, w ≠ C.stQ a j) → x w = y w then
    M (fun j => x (C.stQ a j)) (fun j => y (C.stQ a j)) else 0

/-- A one-qubit operator on wire `w`, tensored with the identity on every other wire. -/
noncomputable def liftWire (w : C.Wire) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix C.Config C.Config ℂ :=
  open Classical in
  fun x y => if ∀ w', w' ≠ w → x w' = y w' then M (x w) (y w) else 0

/-- The SWAP of two wires (a permutation matrix). -/
noncomputable def swapOp (w₁ w₂ : C.Wire) : Matrix C.Config C.Config ℂ :=
  open Classical in
  fun x y => if x = y ∘ Equiv.swap w₁ w₂ then 1 else 0

/-- The initial global state `ρ₀ ⊗ ⨂_h |ψ_h⟩⟨ψ_h| ⊗ |0…0⟩⟨0…0|` (pinned model P11): the shared
station state, every carrier in its BB84 state, every channel qubit in `|0⟩`. -/
noncomputable def initState (ξ : Draw m RH s) : Matrix C.Config C.Config ℂ :=
  open Classical in
  fun x y => C.ρ₀ (fun w => x (Sum.inl w)) (fun w => y (Sum.inl w)) *
    (∏ h, ξ.psi h (x (C.carrier h)) * star (ξ.psi h (y (C.carrier h)))) *
    (if ∀ e, x (C.chan e) = 0 ∧ y (C.chan e) = 0 then 1 else 0)

/-- Processing order of events: by time, then station, then index. -/
def Before (e e' : Ev C.N) : Prop :=
  C.t e.1 e.2 < C.t e'.1 e'.2 ∨
    (C.t e.1 e.2 = C.t e'.1 e'.2 ∧ (e.1 < e'.1 ∨ (e.1 = e'.1 ∧ e.2.val ≤ e'.2.val)))

/-- All events, listed in processing order. -/
noncomputable def order : List (Ev C.N) :=
  open Classical in
  (Finset.univ : Finset (Ev C.N)).toList.mergeSort (fun e e' => decide (C.Before e e'))

/-- An absorption of carrier `h` at event `e` is possible iff the station lies on the closed
segment between the verifiers and the event happens exactly when the carrier, sent by `V₀` at
`sendTime h` toward `V₁` at speed `1`, passes it (pinned model P9). -/
def CanAbsorb (e : Ev C.N) (h : Fin (NL m RH)) : Prop :=
  G.OnSegment (C.pos e.1) ∧ C.t e.1 e.2 = S.sendTime h + |C.pos e.1 - G.v 0|

/-- One event: apply the Kraus operator of its recorded outcome on its station, then its action:
an effective absorption swaps the carrier into the local qubit (only if possible and the carrier
was not absorbed before), a launch swaps the local qubit into the event's channel qubit. The
state is the operator product so far and the set of absorbed carriers. -/
noncomputable def step (ξ : Draw m RH s) (ω : Outcomes C.N C.K)
    (st : Matrix C.Config C.Config ℂ × Finset (Fin (NL m RH))) (e : Ev C.N) :
    Matrix C.Config C.Config ℂ × Finset (Fin (NL m RH)) :=
  open Classical in
  let Kop := C.liftStation e.1 (C.kraus e.1 e.2 ξ ω (ω e))
  match C.act e.1 e.2 ξ ω (ω e) with
  | .idle => (Kop * st.1, st.2)
  | .absorb h j =>
      if C.CanAbsorb e h ∧ h ∉ st.2 then
        (C.swapOp (C.carrier h) (C.stQ e.1 j) * Kop * st.1, insert h st.2)
      else (Kop * st.1, st.2)
  | .launch _ j => (C.swapOp (C.stQ e.1 j) (C.chan e) * Kop * st.1, st.2)

/-- The whole execution on the path `(ξ, ω)`: the product of all event operators (in processing
order) and the set of effectively absorbed carriers. -/
noncomputable def run (ξ : Draw m RH s) (ω : Outcomes C.N C.K) :
    Matrix C.Config C.Config ℂ × Finset (Fin (NL m RH)) :=
  C.order.foldl (C.step ξ ω) (1, ∅)

/-- The verifier targeted by a launch at event `e` on the path `(ξ, ω)`, if any. -/
def launchTarget (e : Ev C.N) (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Option (Fin 2) :=
  match C.act e.1 e.2 ξ ω (ω e) with
  | .launch c _ => some c
  | _ => none

/-- Arrival time at `V_c` of a qubit launched at event `e`. -/
noncomputable def arrival (e : Ev C.N) (c : Fin 2) : ℝ := C.t e.1 e.2 + |C.pos e.1 - G.v c|

/-- Event `e` is a **warranted response** for round `k`: a launch to the selected verifier
`V_{b_k}` arriving exactly at the deadline `T k i_k + d_{b_k}` (rules 3–4). -/
def Warranted (k : Fin m) (e : Ev C.N) (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Prop :=
  C.launchTarget e ξ ω = some (ξ.b k) ∧ C.arrival e (ξ.b k) = S.deadline k (ξ.b k) (ξ.i k)

/-- The **accepting** paths (pinned model P11): (A1) every carrier is effectively absorbed
(rule 2: "If `V₁` receives any of these qubits, the verifiers abort"); (A2) every round has
exactly one warranted response and every launch arriving by the end of the experiment is a
warranted response (rule 4). -/
def Accepting (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Prop :=
  (C.run ξ ω).2 = Finset.univ ∧ (∀ k, ∃! e, C.Warranted k e ξ ω) ∧
    ∀ e c, C.launchTarget e ξ ω = some c → C.arrival e c ≤ S.Tend → ∃ k, C.Warranted k e ξ ω

/-- The verifiers' projection tests: for each round `k`, the projector onto `|ψ_{r_k}⟩` on the
channel qubit of the round's warranted response (Figure 3: "perform the projection test onto
`H^{θ_{r_k}}|x_{r_k}⟩`"). -/
noncomputable def testOp (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Matrix C.Config C.Config ℂ :=
  open Classical in
  ((List.finRange m).map fun k =>
    if h : ∃ e, C.Warranted k e ξ ω then
      match ξ.req k with
      | some l => C.liftWire (C.chan (Classical.choose h)) (proj (ξ.psi l))
      | none => 0
    else 0).prod

/-- Probability weight of the path `(ξ, ω)` with all projection tests passing:
`Re tr(P ρ_init(ξ) P†)`, `P = (tests) · (event operators)`. -/
noncomputable def weight (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : ℝ :=
  let P := C.testOp ξ ω * (C.run ξ ω).1
  (P * C.initState ξ * Pᴴ).trace.re

/-- **Acceptance probability** of the coalition (pinned model P11; Figure 3: "Output of the
experiment is 1 if and only if the outcome of every round is 1"). Behera–Goyal, arXiv:2609.39234
(sha256 bdf2928d…), Figure 3, p.31; protocol rules 1–5, pp.30–32.

`acceptProb = (1/|Ξ|) Σ_ξ Σ_ω [accepting] · Re tr(P ρ_init(ξ) P†)`.

**Formalization Note.** The verifiers never announce an abort: the experiment runs to the end
and outputs `1` iff every round passes (footnote 23, p.37); arrivals after the end of the
experiment are ignored; the literal BB84 description of Figure 3 is used. The channel qubit of
a launch is never touched again, so testing at the end is testing at arrival. -/
noncomputable def acceptProb : ℝ :=
  open Classical in
  (Fintype.card (Draw m RH s) : ℝ)⁻¹ *
    ∑ ξ : Draw m RH s, ∑ ω : Outcomes C.N C.K, if C.Accepting ξ ω then C.weight ξ ω else 0

end Coalition

end QPVEntanglement


