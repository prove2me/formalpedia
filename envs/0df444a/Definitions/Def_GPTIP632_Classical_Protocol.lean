-- Prove2me | Definitions.Def_GPTIP632_Classical_Protocol
-- name    : GPTIP632_Classical_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:21.882364+00:00
-- url     : https://prove2.me/theorems/d4cd5324-1e39-48bb-93a9-4c004dc7623e
-- title:
--   Verifiers, prover strategies, acceptance probability, value, and the classes $\mathsf{GIP}$, $\mathsf{GIP}_{\mathrm{cl}}$ and its public-coin subclass
-- statement:
--   An **$r$-round verifier** $V$ for a theory $\mathcal G$ is a polynomial-time uniform family of adaptive circuits built from the gate set. On input $x$ of length $n$ the verifier holds a register of elementary wires, initially empty. A deterministic polynomial-time machine, given $x$, the stage index and the outcomes recorded so far, names the next step: halt the stage, or apply a gate $g$ to named wires; every gate outcome is recorded. In round $i$ the stage-$i$ circuit ends with the outgoing message $Q_i$ as its last wires; $Q_i$ is handed to the prover and the returned $A_i$ is appended. After $r(n)$ rounds a final stage runs, and the verifier accepts iff its last recorded outcome is $1$. There are at most $p(n)$ gate applications and at most $p(n)$ wires, the message types are computed from $(x,i)$ in polynomial time, and the circuit is valid on every record.
--
--   A gate outcome map acts as $M\otimes\mathrm{id}$ on the untouched wires and on the prover's system, so that the probability of an outcome record is $u(M_L\cdots M_1\omega_0)$ (eq. (2)).
--
--   A **prover strategy** consists of arbitrary systems $P_0,P_1,\dots$ of $\mathcal G$, a state $\tau_0\in\Omega_{P_0}$, and allowed channels $\Pi_i\in\mathrm{Chan}_{\mathcal G}(Q_iP_{i-1},A_iP_i)$. The interaction is one closed circuit; $\Pr[V_x\leftrightarrow P\text{ accepts}]$ is the total probability of the accepting records, and
--
--   $$
--   \mathrm{val}_{\mathcal G}(V_x)=\sup_P\Pr[V_x\leftrightarrow P\text{ accepts}].
--   $$
--
--   A promise problem $L=(L_{\rm yes},L_{\rm no})$ is in $\mathsf{GIP}(\mathcal G)$ if some verifier has $\mathrm{val}_{\mathcal G}(V_x)\ge2/3$ for $x\in L_{\rm yes}$ and $\le1/3$ for $x\in L_{\rm no}$. It is in $\mathsf{GIP}_{\mathrm{cl}}(\mathcal G)$ if moreover every message is a register of classical bits $\Delta_2$; the parties may still use arbitrary systems internally. It is in the **public-coin subclass** if, moreover, every question is a string of fresh fair-coin outcomes sent unchanged.
--
--   These are the classes of Theorem 1.1.
--
--   **Formalization Note** Registers are lists of elementary wires; coordinates are lists of wire coordinates. Named wires are removed and the gate's output wires appended. A message all of whose wires are classical bits is read out when sent and when received, and its value is recorded; this is the normal form the paper assumes for classical messages (pp.24–25) and does not change any acceptance probability. `prob` is the probability of a record `(ws, q, a)` (gate outcomes by stage, recorded questions, recorded answers); `PrV` is $\Pr_V[z\mid a]$, the verifier alone with the answers fixed on its wires. Public coin is structural: the last $|Q_i|$ gate applications of every stage $i<r$ are a fair-coin gate creating the question wires.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.20–22 (PDF pp.22–24), §C, eq. (2), Definition C.1, Definitions D.1–D.3; pp.24–26 (PDF pp.26–28), §E.1 readout of classical registers and the definition of public coin

import Mathlib
import Definitions.Def_GPTIP632_Classical_Theory
import Definitions.Def_KTUnitary_Synth_PromiseProblem

/-!
# Verifiers, prover strategies, the value of a protocol, and the classes GIP, GIP_cl

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), §C and Definition C.1 (pp.20–21, PDF
pp.22–23), Definitions D.1–D.3 (pp.21–22, PDF pp.23–24), §E.1 (pp.24–25, PDF pp.26–27), §E.2
(p.26, PDF p.28).

**Circuits.** A register is a list of elementary wires. The uniformity machine, given `x`, the stage
index and the outcomes recorded so far, names the next step: halt, or apply gate `g` to the wires at
positions `ws` (distinct, of the types `ins g`). The named wires are removed and the gate's output
wires `outs g` are appended at the end of the register. Gate `g` with outcome `o` acts as its
outcome map tensored with the identity on the untouched wires, in product coordinates (eq. (2)).

**Interaction.** In round `i` (0-based) the verifier's stage-`i` circuit runs; when it halts the last
`|Q_i|` wires are the message `Q_i`, sent to the prover, and the answer wires `A_i` are appended.
Stage `r` (the `(r+1)`-st) produces the decision: the verifier accepts iff the last outcome recorded
in that stage is `1`. The joint state of the verifier's register and the prover's system is one
unnormalised vector in product coordinates; a verifier outcome map acts as `M ⊗ id_P` and the
prover's channel acts on `Q_i P_{i-1}`. A message all of whose wires are classical bits is read out
(recorded) when sent and when received; reading a classical register does not disturb it (p.24),
and the questions and answers so recorded are part of the record.
-/

noncomputable section

namespace GPTIP632.Classical

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
attribute [local instance] _root_.Classical.propDecidable

/-! ### Lists of outcomes and strings -/

/-- All lists of length at most `n` with entries `< K`. -/
def natLists : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | n + 1, K => insert [] ((Finset.range K ×ˢ natLists n K).image fun p => p.1 :: p.2)

/-- All bit strings of length exactly `m`. -/
def strings (m : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin m → Bool)).image List.ofFn

/-- All bit strings of length at most `n`. -/
def boolLists (n : ℕ) : Finset (List Bool) :=
  (Finset.range (n + 1)).biUnion strings

/-- A finite family indexed by `Fin n`, extended by `d` to all of `ℕ`. -/
def extend {α : Type} (d : α) {n : ℕ} (f : Fin n → α) : ℕ → α :=
  fun j => if h : j < n then f ⟨j, h⟩ else d

/-- Remove the entries at the positions `ws`. -/
def removeAt {α : Type} (ws : List ℕ) (xs : List α) : List α :=
  (xs.zipIdx.filter fun p => p.2 ∉ ws).map Prod.fst

/-- The entries at the positions `ws`, in the order of `ws`. -/
def pick {α : Type} (ws : List ℕ) (xs : List α) : List α := ws.filterMap fun j => xs[j]?

/-- A self-delimiting encoding of a list of natural numbers (binary, `Nat.bits`). -/
def encNats (z : List ℕ) : Str := tup (z.map Nat.bits)

/-! ### Steps, verifiers -/

/-- A step named by the uniformity machine: halt the current stage, or apply a gate to wires. -/
inductive Step (G : Theory) where
  | halt : Step G
  | apply (g : G.Gate) (ws : List ℕ) : Step G

/-- The encoding of a step, given an encoding `gc` of the gate set. -/
def encStep {G : Theory} (gc : G.Gate → ℕ) : Step G → Str
  | .halt => []
  | .apply g ws => tup (Nat.bits (gc g) :: ws.map Nat.bits)

/-- The data of an `r`-round verifier (Definition D.1, p.21): the number of rounds `r(n)`, a
polynomial `bound` on the number of gate applications and of wires, the message types
`Q x i`, `A x i` of round `i` (lists of elementary wires, fixed by `x`), and the step function of
the uniformity machine: `next x i z` is the step of stage `i` after the outcomes `z` recorded so
far (over the whole interaction). -/
structure VData (G : Theory) where
  r : Polynomial ℕ
  bound : Polynomial ℕ
  Q : Str → ℕ → List G.C.Elem
  A : Str → ℕ → List G.C.Elem
  next : Str → ℕ → List ℕ → Step G

/-- Result of running a circuit along a prescribed outcome record: `ok`, `mismatch` (the record does
not fit the circuit: too short, too long, or an outcome out of range), or `invalid` (the machine
named an impossible gate application, or exceeded the gate or wire bound, or a message has the
wrong type). -/
inductive Res (α : Type) where
  | ok (a : α) : Res α
  | mismatch : Res α
  | invalid : Res α

namespace VData

variable {G : Theory} (V : VData G)

/-- The number of rounds on input `x`. -/
def R (x : Str) : ℕ := V.r.eval x.length

/-- The bound `p(|x|)`. -/
def B (x : Str) : ℕ := V.bound.eval x.length

/-- Gate `g` can be applied to the wires `ws` of the register `l`: distinct positions, of the
gate's input types. -/
def ValidAt (g : G.Gate) (ws : List ℕ) (l : List G.C.Elem) : Prop :=
  ws.Nodup ∧ ws.map (fun j => l[j]?) = (G.ins g).map some

/-- The register after applying gate `g` to the wires `ws`. -/
def newReg (g : G.Gate) (ws : List ℕ) (l : List G.C.Elem) : List G.C.Elem :=
  removeAt ws l ++ G.outs g

/-- The kernel of outcome `o` of gate `g` on wires `ws`: `M_o ⊗ id` on raw coordinates. -/
def stepKer (g : G.Gate) (ws : List ℕ) (o : ℕ) (k' k : List G.C.Wire) : ℝ :=
  if k'.take (removeAt ws k).length = removeAt ws k then
    G.gk g o (k'.drop (removeAt ws k).length) (pick ws k)
  else 0

/-- One stage of the verifier's adaptive circuit, acting on the verifier's register `l` (with the
untouched coordinates `X` of the other party), along the prescribed outcomes `w` of this stage.
`budget` is the number of gate applications still allowed; `z` is the record so far. -/
def stageRun (x : Str) (i : ℕ) {X : Type} :
    (budget : ℕ) → (z : List ℕ) → (l : List G.C.Elem) → (List G.C.Wire → X → ℝ) → List ℕ →
      Res (ℕ × List G.C.Elem × (List G.C.Wire → X → ℝ))
  | 0, z, l, ψ, w =>
      match V.next x i z with
      | .halt => match w with
        | [] => .ok (0, l, ψ)
        | _ :: _ => .mismatch
      | .apply _ _ => .invalid
  | b + 1, z, l, ψ, w =>
      match V.next x i z with
      | .halt => match w with
        | [] => .ok (b + 1, l, ψ)
        | _ :: _ => .mismatch
      | .apply g ws =>
        if ValidAt g ws l ∧ (newReg g ws l).length ≤ V.B x then
          match w with
          | [] => .mismatch
          | o :: w' =>
            if o < G.nout g then
              stageRun x i b (z ++ [o]) (newReg g ws l)
                (fun k' p => ∑ k ∈ G.C.coords l, stepKer g ws o k' k * ψ k p) w'
            else .mismatch
        else .invalid

/-- The outcomes recorded in round `j`: the stage-`j` gate outcomes `ws j`, then the recorded
question bits `q j` and answer bits `a j` (as outcomes `0`, `1`). -/
def roundRecord (ws : ℕ → List ℕ) (q a : ℕ → List Bool) (j : ℕ) : List ℕ :=
  ws j ++ (q j).map Bool.toNat ++ (a j).map Bool.toNat

/-- The record before stage `i`. -/
def hist (ws : ℕ → List ℕ) (q a : ℕ → List Bool) (i : ℕ) : List ℕ :=
  ((List.range i).map (roundRecord ws q a)).flatten

/-- The state at the start of stage `i`, after `i` message exchanges, along the record
`(ws, q, a)`: remaining gate budget, register, joint vector. `H i l₀ ψ` is the exchange of round
`i` on the register `l₀ ++ Q_i`, returning the vector on `l₀ ++ A_i`. -/
def preStage (x : Str) {X : ℕ → Type} (ψ₀ : List G.C.Wire → X 0 → ℝ)
    (H : (i : ℕ) → List G.C.Elem → (List G.C.Wire → X i → ℝ) → (List G.C.Wire → X (i + 1) → ℝ))
    (ws : ℕ → List ℕ) (q a : ℕ → List Bool) :
    (i : ℕ) → Res (ℕ × List G.C.Elem × (List G.C.Wire → X i → ℝ))
  | 0 => .ok (V.B x, [], ψ₀)
  | i + 1 =>
    match preStage x ψ₀ H ws q a i with
    | .ok (b, l, ψ) =>
      match V.stageRun x i b (hist ws q a i) l ψ (ws i) with
      | .ok (b', l', ψ') =>
        if l'.drop (l'.length - (V.Q x i).length) = V.Q x i ∧
            (l'.take (l'.length - (V.Q x i).length) ++ V.A x i).length ≤ V.B x then
          .ok (b', l'.take (l'.length - (V.Q x i).length) ++ V.A x i,
            H i (l'.take (l'.length - (V.Q x i).length)) ψ')
        else .invalid
      | .mismatch => .mismatch
      | .invalid => .invalid
    | .mismatch => .mismatch
    | .invalid => .invalid

/-- The final state: after the `R` exchanges, the last stage (the `(R+1)`-st) runs. -/
def finalRun (x : Str) {X : ℕ → Type} (ψ₀ : List G.C.Wire → X 0 → ℝ)
    (H : (i : ℕ) → List G.C.Elem → (List G.C.Wire → X i → ℝ) → (List G.C.Wire → X (i + 1) → ℝ))
    (ws : ℕ → List ℕ) (q a : ℕ → List Bool) :
    Res (List G.C.Elem × (List G.C.Wire → X (V.R x) → ℝ)) :=
  match V.preStage x ψ₀ H ws q a (V.R x) with
  | .ok (b, l, ψ) =>
    match V.stageRun x (V.R x) b (hist ws q a (V.R x)) l ψ (ws (V.R x)) with
    | .ok (_, l', ψ') => .ok (l', ψ')
    | .mismatch => .mismatch
    | .invalid => .invalid
  | .mismatch => .mismatch
  | .invalid => .invalid

/-- The verifier accepts on the record `ws` iff the last outcome recorded in the final stage is
`1` (the bit `acc` among its recorded outcomes, Definition D.1). -/
def accepts (x : Str) (ws : ℕ → List ℕ) : Prop := (ws (V.R x)).getLast? = some 1

/-- The coordinate of a bit string on a message register all of whose wires are classical bits;
`none` if some wire is not a classical bit or the lengths differ. -/
noncomputable def msgCoord : List G.C.Elem → List Bool → Option (List G.C.Wire)
  | [], [] => some []
  | a :: l, b :: s =>
      if h : G.C.elem a = G.C.cl 1 then (msgCoord l s).map (G.C.bitWire a h b :: ·) else none
  | _, _ => none

/-- Whether every wire of a message is a classical bit `Δ_2` (such a message is read out). -/
def AllBits (l : List G.C.Elem) : Prop := ∀ a ∈ l, G.C.elem a = G.C.cl 1

/-- The readout of a message register: on a message of classical bits, the indicator that its
coordinate is that of the recorded string `s`; on any other message, nothing is read and the
recorded string must be empty. -/
noncomputable def readout (M : List G.C.Elem) (s : List Bool) (kM : List G.C.Wire) : ℝ :=
  if AllBits M then (if msgCoord M s = some kM then 1 else 0) else (if s = [] then 1 else 0)

/-- The prover's channel `Π` as a kernel on raw coordinates `(k_A, p') ← (k_Q, p)`. -/
noncomputable def chanKer {Qm Am : List G.C.Elem} {P P' : G.C.Sys}
    (Φ : Matrix (G.C.sys (G.C.comp (G.C.reg Am) P')).ι (G.C.sys (G.C.comp (G.C.reg Qm) P)).ι ℝ)
    (kA : List G.C.Wire) (p' : (G.C.sys P').ι) (kQ : List G.C.Wire) (p : (G.C.sys P).ι) : ℝ :=
  match G.C.regIdx Am kA, G.C.regIdx Qm kQ with
  | some i, some j => Φ ((G.C.compEquiv _ _).symm (i, p')) ((G.C.compEquiv _ _).symm (j, p))
  | _, _ => 0

end VData

/-- **Definition D.2 (Prover)**, p.22: a prover strategy for the verifier `V` on input `x`: systems
`P_0, P_1, …` of the theory (arbitrary, with no dimension bound), a state `τ_0 ∈ Ω_{P_0}`, and
allowed channels `Π_i ∈ Chan_G(Q_i P_i, A_i P_{i+1})` for the rounds `i < r(|x|)` (0-based). -/
structure Prover {G : Theory} (V : VData G) (x : Str) where
  P : ℕ → G.C.Sys
  τ0 : (G.C.sys (P 0)).ι → ℝ
  τ0_state : τ0 ∈ (G.C.sys (P 0)).states
  ch : (i : ℕ) → Matrix (G.C.sys (G.C.comp (G.C.reg (V.A x i)) (P (i + 1)))).ι
    (G.C.sys (G.C.comp (G.C.reg (V.Q x i)) (P i))).ι ℝ
  ch_allowed : ∀ i, i < V.R x → ch i ∈ G.C.chan _ _

namespace VData

variable {G : Theory} (V : VData G)

/-- The exchange of round `i` with the prover: read out `Q_i` (if classical), apply `Π_i` to
`Q_i P_i`, read out `A_i` (if classical). -/
noncomputable def proverExchange (x : Str) (P : Prover V x) (q a : ℕ → List Bool) (i : ℕ)
    (l₀ : List G.C.Elem) (ψ : List G.C.Wire → (G.C.sys (P.P i)).ι → ℝ) :
    List G.C.Wire → (G.C.sys (P.P (i + 1))).ι → ℝ :=
  fun k' p' => readout (V.A x i) (a i) (k'.drop l₀.length) *
    ∑ kQ ∈ G.C.coords (V.Q x i), ∑ p : (G.C.sys (P.P i)).ι,
      chanKer (P.ch i) (k'.drop l₀.length) p' kQ p * readout (V.Q x i) (q i) kQ *
        ψ (k'.take l₀.length ++ kQ) p

/-- The probability `Pr[(ws, q, a)]` that the interaction of `V_x` with `P` produces the record of
gate outcomes `ws`, recorded questions `q` and recorded answers `a`: the joint unit of the final
vector (`0` if the record does not fit). -/
noncomputable def prob (x : Str) (P : Prover V x) (ws : ℕ → List ℕ) (q a : ℕ → List Bool) : ℝ :=
  match V.finalRun x (X := fun i => (G.C.sys (P.P i)).ι)
      (fun k p => (if k = [] then 1 else 0) * P.τ0 p) (V.proverExchange x P q a) ws q a with
  | .ok (l, ψ) => ∑ k ∈ G.C.coords l, ∑ p, G.C.rawUnit k * (G.C.sys (P.P (V.R x))).unit p * ψ k p
  | _ => 0

/-- The number of outcomes of the largest gate. -/
def maxOut : ℕ := Finset.univ.sup G.nout

/-- The sum of `F` over all records that can occur on input `x`: stage records of length at most
`p(|x|)` with entries `< maxOut`, and recorded question and answer strings of length at most
`p(|x|)` (every other record has probability `0`). -/
noncomputable def recordSum (x : Str) (F : (ℕ → List ℕ) → (ℕ → List Bool) → (ℕ → List Bool) → ℝ) : ℝ :=
  ∑ f ∈ Fintype.piFinset (fun _ : Fin (V.R x + 1) => natLists (V.B x) (maxOut (G := G))),
    ∑ fq ∈ Fintype.piFinset (fun _ : Fin (V.R x) => boolLists (V.B x)),
      ∑ fa ∈ Fintype.piFinset (fun _ : Fin (V.R x) => boolLists (V.B x)),
        F (extend [] f) (extend [] fq) (extend [] fa)

/-- `Pr[V_x ↔ P accepts]`: the total probability of the accepting records. -/
noncomputable def accProb (x : Str) (P : Prover V x) : ℝ :=
  V.recordSum x fun ws q a => if V.accepts x ws then V.prob x P ws q a else 0

/-- **Definition D.3 (Value)**, p.22: `val_G(V_x) = sup_P Pr[V_x ↔ P accepts]`, over all prover
strategies in `G`. -/
noncomputable def val (x : Str) : ℝ := sSup {t | ∃ P : Prover V x, V.accProb x P = t}

/-- The exchange of round `i` for the verifier alone with the answers `a` supplied as fixed
classical inputs: read out `Q_i`, discard it, and prepare `A_i` in the state `δ_{a_i}`. -/
noncomputable def fixedExchange (x : Str) (q a : ℕ → List Bool) (i : ℕ) (l₀ : List G.C.Elem)
    (ψ : List G.C.Wire → Unit → ℝ) : List G.C.Wire → Unit → ℝ :=
  fun k' _ => readout (V.A x i) (a i) (k'.drop l₀.length) *
    ∑ kQ ∈ G.C.coords (V.Q x i), G.C.rawUnit kQ * readout (V.Q x i) (q i) kQ * ψ (k'.take l₀.length ++ kQ) ()

/-- `Pr_V[(ws, q) | a]` (eq. (2), p.20): the probability of the record (gate outcomes `ws`,
recorded questions `q`) in the verifier's circuit with the answers `a` fixed on the wires `A_i`. -/
noncomputable def PrV (x : Str) (a : ℕ → List Bool) (ws : ℕ → List ℕ) (q : ℕ → List Bool) : ℝ :=
  match V.finalRun x (X := fun _ => Unit) (fun k _ => if k = [] then 1 else 0)
      (V.fixedExchange x q a) ws q a with
  | .ok (l, ψ) => ∑ k ∈ G.C.coords l, G.C.rawUnit k * ψ k ()
  | _ => 0

/-- **Definition C.1 (uniformity)**, p.20: a polynomial-time machine, given `x`, the stage index
and the outcomes recorded so far, outputs the next gate and its wires or halts; a second one, given
`x` and `i`, outputs the message types of round `i`. Machines are clocked deterministic machines
(run with the empty oracle), outputs read off the work tape; gates and elementary systems are
encoded by injective numberings. -/
def Uniform : Prop :=
  ∃ (gc : G.Gate → ℕ) (ec : G.C.Elem → ℕ), Function.Injective gc ∧ Function.Injective ec ∧
    (∃ (M : OTM) (c : Polynomial ℕ), ∀ (x : Str) (i : ℕ) (z : List ℕ),
      M.output O₀ (tup [x, unary i, encNats z]) (c.eval (tup [x, unary i, encNats z]).length) =
        encStep gc (V.next x i z)) ∧
    (∃ (M : OTM) (c : Polynomial ℕ), ∀ (x : Str) (i : ℕ),
      M.output O₀ (tup [x, unary i]) (c.eval (tup [x, unary i]).length) =
        tup [encNats ((V.Q x i).map ec), encNats ((V.A x i).map ec)])

/-- The circuit is well formed on every record: the uniformity machine never names an impossible
gate application, never exceeds `p(|x|)` gate applications or `p(|x|)` wires, and the registers at
the end of each stage end with the message wires of their declared types. -/
def WellFormed : Prop :=
  ∀ (x : Str) (ws : ℕ → List ℕ) (q a : ℕ → List Bool),
    V.finalRun x (X := fun _ => Unit) (fun k _ => if k = [] then 1 else 0)
      (V.fixedExchange x q a) ws q a ≠ .invalid

/-- **Definition D.1 (Verifier)**, p.21: an `r`-round verifier for `G` is a polynomial-time uniform
family of adaptive circuits with the structure above. -/
def IsVerifier : Prop := V.Uniform ∧ V.WellFormed

/-- **GIP_cl** (Definition D.3, p.22): all message systems `Q_i`, `A_i` are registers of
designated standard classical bits `Δ_2`. -/
def ClassicalMessages : Prop :=
  ∀ (x : Str) (i : ℕ), i < V.R x → AllBits (G := G) (V.Q x i ++ V.A x i)

/-- The steps the machine takes in stage `i` from the record `z`, along the stage outcomes `w`,
up to and including the halting step (`none` if `w` does not fit or the budget `b` runs out). -/
def stageSteps (x : Str) (i : ℕ) : (b : ℕ) → List ℕ → List ℕ → Option (List (Step G))
  | 0, z, w => match V.next x i z, w with
    | .halt, [] => some [.halt]
    | _, _ => none
  | b + 1, z, w => match V.next x i z, w with
    | .halt, [] => some [.halt]
    | .apply g ws, o :: w' => (stageSteps x i b (z ++ [o]) w').map (.apply g ws :: ·)
    | _, _ => none

/-- **Public coin** (p.26): every question `Q_i` is a string of fresh fair-coin outcomes, sent to the
prover unchanged. There is a fair-coin gate `g` (no input, output one classical bit wire `a`, one
outcome, kernel `1/2` on both values) such that, in every round `i < r(|x|)`, `Q_i` consists of
`m` wires of type `a`, and, started from any record of the earlier rounds, the last `m` gate
applications of stage `i` before it halts are `g` with no input wires (so the question wires, the
last `m` wires of the register, are its fresh outputs and no gate acts on them afterwards; their
values are recorded when they are sent). -/
def PublicCoin : Prop :=
  ∃ (g : G.Gate) (a : G.C.Elem) (h : G.C.elem a = G.C.cl 1),
    G.ins g = [] ∧ G.outs g = [a] ∧ G.nout g = 1 ∧
    (∀ b : Bool, G.gk g 0 [G.C.bitWire a h b] [] = 1 / 2) ∧
    ∀ (x : Str) (i : ℕ), i < V.R x →
      V.Q x i = List.replicate (V.Q x i).length a ∧
      ∀ (ws : ℕ → List ℕ) (q a : ℕ → List Bool) (b : ℕ) (w : List ℕ) (s : List (Step G)),
        V.stageSteps x i b (hist ws q a i) w = some s →
        (s.dropLast).drop (s.dropLast.length - (V.Q x i).length) =
          List.replicate (V.Q x i).length (.apply g [])

end VData

/-- **GIP(G)** (Definition D.3, p.22): the promise problems `L` with a verifier `V` for `G` such
that `val_G(V_x) ≥ 2/3` for `x ∈ L_yes` and `val_G(V_x) ≤ 1/3` for `x ∈ L_no`. -/
def GIP (G : Theory) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData G, V.IsVerifier ∧
    (∀ x ∈ L.1, (2 : ℝ) / 3 ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ 1 / 3)}

/-- **GIP_cl(G)** (Definition D.3, p.22): as `GIP G`, with all messages classical registers. -/
def GIPcl (G : Theory) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData G, V.IsVerifier ∧ V.ClassicalMessages ∧
    (∀ x ∈ L.1, (2 : ℝ) / 3 ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ 1 / 3)}

/-- The **public-coin subclass of GIP_cl(G)** (p.26). -/
def GIPclPublicCoin (G : Theory) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData G, V.IsVerifier ∧ V.ClassicalMessages ∧ V.PublicCoin ∧
    (∀ x ∈ L.1, (2 : ℝ) / 3 ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ 1 / 3)}

end GPTIP632.Classical

end


