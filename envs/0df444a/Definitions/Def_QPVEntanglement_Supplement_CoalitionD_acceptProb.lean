-- Prove2me | Definitions.Def_QPVEntanglement_Supplement_CoalitionD_acceptProb
-- name    : QPVEntanglement_Supplement_CoalitionD_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:18:52.84037+00:00
-- url     : https://prove2.me/theorems/a4ae96a3-6369-451d-901d-adb9b51df60c
-- title:
--   Acceptance probability of a coalition in $\mathbb R^d$
-- statement:
--   This definition belongs to the **operator-requested pinned-down model** of the mission (choice P11 of the mission description), carried from $\mathbb R$ to $\mathbb R^d$.
--
--   The execution of a coalition in $\mathbb R^d$ against the $d$-dimensional version of the protocol of Figure 3 is the same as in one dimension, with two changes. First, a carrier (a BB84 qubit sent by $V_0$ toward $V_1$ along the verifier segment) can be absorbed only by a station that sits on the segment, at a point $\iota(r)$ with $r$ between $v_0$ and $v_1$, and only at the moment $\sigma_h+|r-v_0|$ at which the carrier passes. Second, a qubit launched at time $t$ from $\mathrm{pos}_a$ reaches $V_c$ at $t+\|\mathrm{pos}_a-\iota(v_c)\|_2$. A path $(\xi,\omega)$ is **accepting** when
--
--   1. (A1) every carrier is absorbed, and
--   2. (A2) every round $k$ has exactly one launch to the selected verifier $V_{b_k}$ arriving exactly at the deadline $T_{k,i_k}+d_{b_k}$, and every launch arriving by the end of the experiment is such a response.
--
--   The **acceptance probability** is
--
--   $$\Pr[\text{accept}]=\frac1{|\Xi|}\sum_{\xi\in\Xi}\ \sum_{\omega}\ [\text{accepting}]\cdot\operatorname{Re}\operatorname{tr}\big(P\,\rho_{\mathrm{init}}(\xi)\,P^\dagger\big),$$
--
--   where $P$ is the product of the event operators in processing order, followed by the verifiers' projection tests onto $|\psi_{r_k}\rangle$ on each round's response.
--
--   **Formalization Note** Word for word the published one-dimensional `QPVEntanglement.Coalition.acceptProb` (no abort announcement, output $1$ iff every round passes, arrivals after the end ignored), with absorption restricted to the verifier segment (condition 1, p.46) and Euclidean arrival times.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Figure 3, p.31; protocol rules 1–5, pp.30–32; Definition 4, p.29; conditions 1–2, p.46

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_acceptProb
import Definitions.Def_QPVEntanglement_Supplement_CoalitionD

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement.Supplement

open QPVEntanglement

namespace CoalitionD

variable {d : ℕ} {GD : GeometryD d} {m RH s : ℕ} {S : Schedule GD.G m RH s} (C : CoalitionD GD S)

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

/-- A local operator on station `a`'s register, tensored with the identity on every other wire. -/
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

/-- The initial global state `ρ₀ ⊗ ⨂_h |ψ_h⟩⟨ψ_h| ⊗ |0…0⟩⟨0…0|`. -/
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
verifier segment, at the point `ι r` with axis coordinate `r` (`G.OnSegment r`), and the event
happens exactly when the carrier, sent by `V₀` at `sendTime h` along the segment toward `V₁` at
speed `1`, passes it (condition 1, p.46: "Each initialization or replacement qubit sent by `V₀`
is sent along the fixed one-way path from `V₀`, through the claimed location, to `V₁`"). A station
off the segment can never touch a carrier. -/
def CanAbsorb (e : Ev C.N) (h : Fin (NL m RH)) : Prop :=
  ∃ r : ℝ, GD.G.OnSegment r ∧ C.pos e.1 = GD.embed r ∧
    C.t e.1 e.2 = S.sendTime h + |r - GD.G.v 0|

/-- One event: apply the Kraus operator of its recorded outcome on its station, then its action
(an effective absorption swaps the carrier into the local qubit, only if possible and the carrier
was not absorbed before; a launch swaps the local qubit into the event's channel qubit). -/
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

/-- Arrival time at `V_c` of a qubit launched at event `e`: its time plus the Euclidean distance
from the station to `ι (v_c)`. -/
noncomputable def arrival (e : Ev C.N) (c : Fin 2) : ℝ :=
  C.t e.1 e.2 + dist (C.pos e.1) (GD.verifier c)

/-- Event `e` is a **warranted response** for round `k`: a launch to the selected verifier
`V_{b_k}` arriving exactly at the deadline `T k i_k + d_{b_k}`. -/
def Warranted (k : Fin m) (e : Ev C.N) (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Prop :=
  C.launchTarget e ξ ω = some (ξ.b k) ∧ C.arrival e (ξ.b k) = S.deadline k (ξ.b k) (ξ.i k)

/-- The **accepting** paths: (A1) every carrier is effectively absorbed; (A2) every round has
exactly one warranted response and every launch arriving by the end of the experiment is a
warranted response. -/
def Accepting (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Prop :=
  (C.run ξ ω).2 = Finset.univ ∧ (∀ k, ∃! e, C.Warranted k e ξ ω) ∧
    ∀ e c, C.launchTarget e ξ ω = some c → C.arrival e c ≤ S.Tend → ∃ k, C.Warranted k e ξ ω

/-- The verifiers' projection tests: for each round `k`, the projector onto `|ψ_{r_k}⟩` on the
channel qubit of the round's warranted response. -/
noncomputable def testOp (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : Matrix C.Config C.Config ℂ :=
  open Classical in
  ((List.finRange m).map fun k =>
    if h : ∃ e, C.Warranted k e ξ ω then
      match ξ.req k with
      | some l => C.liftWire (C.chan (Classical.choose h)) (proj (ξ.psi l))
      | none => 0
    else 0).prod

/-- Probability weight of the path `(ξ, ω)` with all projection tests passing. -/
noncomputable def weight (ξ : Draw m RH s) (ω : Outcomes C.N C.K) : ℝ :=
  let P := C.testOp ξ ω * (C.run ξ ω).1
  (P * C.initState ξ * Pᴴ).trace.re

/-- **Acceptance probability** of a `d`-dimensional coalition against the `d`-dimensional
mobile-verifier version (Definition 4, p.29) of the protocol of Figure 3 (p.31; protocol rules
1–5, pp.30–32). Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Figure 3, p.31; Definition 4,
p.29; conditions 1–2, p.46.

`acceptProb = (1/|Ξ|) Σ_ξ Σ_ω [accepting] · Re tr(P ρ_init(ξ) P†)`, word for word the published
one-dimensional `QPVEntanglement.Coalition.acceptProb`, with absorption possible only on the
verifier segment and launch arrival times given by the Euclidean distance.

**Formalization Note.** Same conventions as the published one-dimensional definition: no abort
announcement, output `1` iff every round passes (footnote 23, p.37); arrivals after the end of
the experiment are ignored; the channel qubit of a launch is never touched again, so testing at
the end is testing at arrival. -/
noncomputable def acceptProb : ℝ :=
  open Classical in
  (Fintype.card (Draw m RH s) : ℝ)⁻¹ *
    ∑ ξ : Draw m RH s, ∑ ω : Outcomes C.N C.K, if C.Accepting ξ ω then C.weight ξ ω else 0

end CoalitionD

end QPVEntanglement.Supplement


