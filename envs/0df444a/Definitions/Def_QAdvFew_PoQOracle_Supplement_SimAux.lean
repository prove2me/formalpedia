-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_SimAux
-- name    : QAdvFew_PoQOracle_Supplement_SimAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:19:21.198885+00:00
-- url     : https://prove2.me/theorems/6739a9ec-a40a-45b8-9a77-8582e8c12998
-- title:
--   The simulator setting of Theorem 5.2: $\mathrm{aux}_{\mathrm{RO}_n}$, simulators and acceptance probabilities
-- statement:
--   For level $n$ of $\mathcal D$ and a number $L$ of samples, $\mathrm{aux}_{\mathrm{RO}_n}$ is the average over $K=(k_1,\dots,k_L)\leftarrow(\{0,1\}^n)^L$ and $J_x=(y_{x,1},\dots,y_{x,L})\leftarrow(\{0,1\}^{4n})^L$ (one list for each $x$) of the state
--
--   $$
--   \bigotimes_i|k_i\rangle\ \otimes\ \bigotimes_x\bigotimes_i|y_{x,i}\rangle|c_{x,y_{x,i}}\rangle\ \otimes\ |K\rangle\otimes\bigotimes_{k\in K^*}\bigotimes_y|\mathrm{RO}_n(k,y)\rangle ,
--   $$
--
--   where $K^*$ is the set of distinct entries of $K$. A **stateful simulator** has an internal register, initialized with $\mathrm{aux}_{\mathrm{RO}_n}$ and further zero qubits, and answers each query (and inverse or controlled query) to a component by a fixed unitary on the query register and its internal register; it has no efficiency bound and does not depend on the sampled oracle. The circuits of Theorem 5.2 take the whole truth table of $\mathrm{RO}_n$ as input and query level $n$ of $\mathrm{SG},\mathrm{Expand},\mathrm{Mix}$ and the PSPACE oracle; the module defines their acceptance probability with the real oracle and with a simulator.
--
--   **Formalization Note** $\bigotimes_{k\in K^*}|\beta_k\rangle$ is stored in $L$ slots, slot $i$ holding $|\beta_{k_i}\rangle$ if $i$ is the first occurrence of $k_i$ in $K$ and zeros otherwise; since $|K\rangle$ is part of the state this is a fixed-size encoding. Every quantum channel is a unitary on a larger register with fresh ancillas, so unitary simulators lose no generality.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §5.2, pp. 33–34 (PDF pp. 35–36), and Theorem 5.2, p. 34 (PDF p. 36)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_oracleD

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- The length `2^{5n} · 12n` of the truth table of `RO_n`. -/
def ttLen (n : ℕ) : ℕ := 2 ^ (n + 4 * n) * (6 * n + 6 * n)

/-- The **truth table of `RO_n`** as a bit string (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 5.2, p. 34 (PDF p. 36): "`RO_n`
corresponds to the entire truth table of the random function `RO_n` used by the oracle"): position
`a · 12n + j` holds bit `j` of `u_{x,y} v_{x,y}`, where `(x, y)` are the `5n` low binary digits of
`a` (`x` first). -/
def ttBits {n : ℕ} (RO : Bits n × Bits (4 * n) → Bits (6 * n) × Bits (6 * n)) : Bits (ttLen n) :=
  fun pos =>
    let a := (pos : ℕ) / (6 * n + 6 * n)
    let j := (pos : ℕ) % (6 * n + 6 * n)
    let xy : Bits (n + 4 * n) := natToBits _ a
    if h : j < 6 * n + 6 * n then Fin.append (RO (lft xy, rgt xy)).1 (RO (lft xy, rgt xy)).2 ⟨j, h⟩
    else false

/-- The number of qubits of `aux_{RO_n}` with `L` samples: `aux_SG` (`Ln`), `aux_Expand`
(`2^n · L · 10n`), and `aux_Mix` (`|K⟩`, `Ln`, and `L` slots of `2^{4n} · 12n` qubits). -/
def auxLen (n L : ℕ) : ℕ :=
  L * n + 2 ^ n * (L * (4 * n + 6 * n)) + (L * n + L * (2 ^ (4 * n) * (6 * n + 6 * n)))

/-- The pure state of which `aux_{RO_n}` is the average (§5.2, pp. 33–34 (PDF pp. 35–36)), for
the sampled lists `K = (k_1, …, k_L)` and `J_x = (y_{x,1}, …, y_{x,L})`:
`aux_SG = ⊗_i |k_i⟩`; `aux_Expand = ⊗_x |α_x⟩` with `|α_x⟩ = ⊗_i |y_{x,i}⟩|c_{x,y_{x,i}}⟩`;
`aux_Mix = |K⟩ ⊗ ⊗_{k ∈ K^*} |β_k⟩` with `|β_k⟩ = ⊗_y |RO_n(k, y)⟩`.

**Formalization Note** Layout, in order: `aux_SG` (slot `i` at `in`); `aux_Expand` (block
`(x, i)` at `Ln + (⟦x⟧L + i)·10n`, `⟦x⟧ = bitsToNat x`: `4n` bits `y_{x,i}` then `6n` qubits of the
claw state); `|K⟩` (`Ln` bits); then `L` slots of `2^{4n}·12n` qubits, slot `i` holding
`|β_{k_i}⟩` (entry `y` at offset `⟦y⟧·12n`) if `i` is the first occurrence of `k_i` in `K`, and
zeros otherwise. Since `|K⟩` is part of the state, this is a fixed-size encoding of
`⊗_{k ∈ K^*} |β_k⟩`. -/
noncomputable def auxPure {n : ℕ} (s : DSample n) (L : ℕ) (K : Fin L → Bits n)
    (J : Bits n → Fin L → Bits (4 * n)) : QState (auxLen n L) :=
  fun z =>
    let oE := L * n
    let oK := L * n + 2 ^ n * (L * (4 * n + 6 * n))
    let oB := oK + L * n
    let S := 2 ^ (4 * n) * (6 * n + 6 * n)
    (∏ i : Fin L, if rd z (i * n) n = K i then (1 : ℂ) else 0) *
    (∏ x : Bits n, ∏ i : Fin L,
      ((if rd z (oE + (bitsToNat x * L + i) * (4 * n + 6 * n)) (4 * n) = J x i then (1 : ℂ) else 0) *
        clawD s x (J x i) (rd z (oE + (bitsToNat x * L + i) * (4 * n + 6 * n) + 4 * n) (6 * n)))) *
    (∏ i : Fin L, if rd z (oK + i * n) n = K i then (1 : ℂ) else 0) *
    (∏ i : Fin L,
      if ∀ j : Fin L, j < i → K j ≠ K i then
        ∏ y : Bits (4 * n),
          if rd z (oB + i * S + bitsToNat y * (6 * n + 6 * n)) (6 * n + 6 * n) =
              Fin.append (s.1 (K i, y)).1 (s.1 (K i, y)).2 then (1 : ℂ) else 0
      else if rd z (oB + i * S) S = (fun _ => false) then (1 : ℂ) else 0)

/-- A **stateful simulator** for level `n` of `O` that receives `aux_{RO_n}` (Theorem 5.2, p. 34; the
proof's `Sim_Init`, `Sim_SG`, `Sim_Expand`, `Sim_Mix`, p. 34): an internal register of
`auxLen n (L n) + w n` qubits, initialized to `aux_{RO_n} ⊗ |0^{w n}⟩`; an initialization unitary on
it; and, for each component `i`, level `t` and direction (`inv`), a unitary on the query register
and the internal register (`q`), and one on control qubit, query register and internal register
for controlled queries (`cq`).

**Formalization Note** "`Sim_aux` itself is inefficient": no size bound. Every quantum channel,
including the stateful channels and the internal Haar sampling of the proof, is a unitary on a
larger register with fresh `|0⟩` ancillas followed by discarding them (Stinespring); the work qubits
`w n` provide those ancillas, so unitaries lose no generality. The simulator is a fixed object: it
does not depend on the sampled oracle, only on `n` (and is chosen after `p`, `q`). -/
structure Simulator (L : ℕ → ℕ) where
  w : ℕ → ℕ
  init : (n : ℕ) → Matrix.unitaryGroup (Bits (auxLen n (L n) + w n)) ℂ
  q : (n i t : ℕ) → Bool → Matrix.unitaryGroup (Bits (arD i t) × Bits (auxLen n (L n) + w n)) ℂ
  cq : (n i t : ℕ) → Bool →
    Matrix.unitaryGroup (Bool × Bits (arD i t) × Bits (auxLen n (L n) + w n)) ℂ

/-- A circuit for Theorem 5.2 at security parameter `n` (p. 34: "Let `A^{(·),PSPACE}` be any oracle
circuit … `A^{SG_n,Expand_n,Mix_n,PSPACE}(RO_n)`"): `anc` ancillas beyond a mandatory output wire,
an oracle circuit on `ttLen n + (anc + 1)` wires whose first `ttLen n` wires hold the truth table
of `RO_n`, and an output wire. -/
structure TTCirc (n : ℕ) where
  anc : ℕ
  circ : UCirc arD (ttLen n + (anc + 1))
  out : Fin (ttLen n + (anc + 1))

namespace TTCirc

variable {n : ℕ}

/-- Its unitary-oracle queries are to level `n` of the components `SG, Expand, Mix` only. -/
def Valid (A : TTCirc n) : Prop :=
  ∀ g ∈ A.circ, (∀ t, g.level? = some t → t = n) ∧ (∀ i, g.comp? = some i → i < 3)

/-- The input state `|RO_n, 0…0⟩`. -/
def inputState (A : TTCirc n) (RO : Bits n × Bits (4 * n) → Bits (6 * n) × Bits (6 * n)) :
    QState (ttLen n + (A.anc + 1)) :=
  basisState fun k => if h : (k : ℕ) < ttLen n then ttBits RO ⟨k, h⟩ else false

end TTCirc

/-- A fixed sample used for the levels other than `n`, which a valid `TTCirc n` never queries. -/
def dfltSample (t : ℕ) : DSample t := (fun _ => (fun _ => false, fun _ => false), 1, fun _ => 1, fun _ => 1)

/-- `Pr[A^{SG_n,Expand_n,Mix_n,PSPACE}(RO_n) → 1]` for a level-`n` sample `s` and the classical
oracle `C` (the fixed PSPACE oracle). -/
noncomputable def realAcc {n : ℕ} (s : DSample n) (C : Oracle) (A : TTCirc n) : ℝ :=
  probOne (A.circ.run (oracleD (Function.update dfltSample n s)) C (A.inputState s.1)) A.out

/-- One instruction of an oracle circuit run against a simulator: states are amplitude vectors on
(circuit wires) × (simulator register `h`); Clifford+T and classical-oracle gates act on the
circuit wires, a query to `(i, t)` applies the simulator's unitary on the query wires (and control)
and the simulator register. -/
noncomputable def UInstr.applySim {m h : ℕ} (C : Oracle)
    (qU : (i t : ℕ) → Bool → Matrix (Bits (arD i t) × Bits h) (Bits (arD i t) × Bits h) ℂ)
    (cqU : (i t : ℕ) → Bool →
      Matrix (Bool × Bits (arD i t) × Bits h) (Bool × Bits (arD i t) × Bits h) ℂ) :
    UInstr arD m → (Bits m × Bits h → ℂ) → (Bits m × Bits h → ℂ)
  | .gate g => fun ψ p => g.apply C (fun y => ψ (y, p.2)) p.1
  | .uq i t inv none ws _ _ => fun ψ p =>
      ∑ z : Bits (arD i t), ∑ h' : Bits h,
        qU i t inv (p.1 ∘ ws, p.2) (z, h') * ψ (Function.extend ws z p.1, h')
  | .uq i t inv (some c) ws _ _ => fun ψ p =>
      ∑ bc : Bool, ∑ z : Bits (arD i t), ∑ h' : Bits h,
        cqU i t inv (p.1 c, p.1 ∘ ws, p.2) (bc, z, h') *
          ψ (Function.update (Function.extend ws z p.1) c bc, h')

/-- `Pr[A^{Sim_aux(aux_{RO_n}),PSPACE}(RO_n) → 1]`: the average, over the uniformly random lists
`K ∈ ({0,1}^n)^L` and `(J_x)_x ∈ (({0,1}^{4n})^L)^{\{0,1\}^n}`, of the probability that the output
wire reads `1` when the simulator register starts in `init (auxPure ⊗ |0⟩)` and every query is
answered by the simulator (§5.2: "The mixed state `aux_{RO_n}` is the average of
`aux_SG ⊗ aux_Expand ⊗ aux_Mix` over the joint sampling above"). -/
noncomputable def simAcc {n : ℕ} {L : ℕ → ℕ} (s : DSample n) (C : Oracle) (Sim : Simulator L)
    (A : TTCirc n) : ℝ :=
  ∑ K : Fin (L n) → Bits n, ∑ J : Bits n → Fin (L n) → Bits (4 * n),
    ((Fintype.card (Fin (L n) → Bits n) : ℝ)⁻¹ *
      (Fintype.card (Bits n → Fin (L n) → Bits (4 * n)) : ℝ)⁻¹) *
    let reg0 : QState (auxLen n (L n) + Sim.w n) :=
      ((Sim.init n).1 : Matrix (Bits (auxLen n (L n) + Sim.w n)) (Bits (auxLen n (L n) + Sim.w n)) ℂ).mulVec
        (tensorState (auxPure s (L n) K J) (basisState fun _ => false))
    let ψ0 : Bits (ttLen n + (A.anc + 1)) × Bits (auxLen n (L n) + Sim.w n) → ℂ :=
      fun p => A.inputState s.1 p.1 * reg0 p.2
    let ψ := A.circ.foldl
      (fun st g => UInstr.applySim C (fun i t b => (Sim.q n i t b).1)
        (fun i t b => (Sim.cq n i t b).1) g st) ψ0
    ∑ p : Bits (ttLen n + (A.anc + 1)) × Bits (auxLen n (L n) + Sim.w n),
      if p.1 A.out then ‖ψ p‖ ^ 2 else 0

end QAdvFew.PoQOracle.Supplement


