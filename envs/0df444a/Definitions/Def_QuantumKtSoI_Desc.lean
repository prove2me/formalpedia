-- Prove2me | Definitions.Def_QuantumKtSoI_Desc
-- name    : QuantumKtSoI_Desc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:13.693225+00:00
-- url     : https://prove2.me/theorems/1ee38dfe-f5d7-4c6d-a1ec-dc53ad1f7834
-- title:
--   Descriptions and their machines $M(e)$ (Definition 3.6)
-- statement:
--   The **descriptions** of Definition 3.6 are built from $\mathrm{BASE}(A)$ for a machine $A$, $\mathrm{LIT}(d)$ for a string $d$, $\mathrm{SEQ}_g(e_1,e_2)$ for a glue mode $g$, and $\mathrm{AMP}(r,e)$ for an integer $r\ge1$. Their binary strings are
--   $$\mathrm{BASE}(A)=000\,\overline{\ulcorner A\urcorner},\quad \mathrm{LIT}(d)=001\,\bar d,\quad \mathrm{SEQ}_g(e_1,e_2)=t_g\,e_1e_2\ (t_{\mathrm{feed}}=010,\ t_{\mathrm{cat}}=011,\ t_{\mathrm{pair}}=100),\quad \mathrm{AMP}(r,e)=101\,\bar r\,e .$$
--   Each description denotes a machine $M(e)$ (p.25), given glue routines $G$:
--   1. $M(\mathrm{BASE}(A))=A$;
--   2. $M(\mathrm{LIT}(d))$ writes $d$ on its output tape in $|d|+1$ steps and halts;
--   3. $M(\mathrm{SEQ}_g(e_1,e_2))$ runs $M(e_1)$ on private copies of its tapes (sharing the input tape), then the routine writing $\alpha_g(x,u)$ on the input tape of a private copy of $M(e_2)$, then $M(e_2)$, then the routine writing $\beta_g(x,u,v)$ on its output tape, and halts; an initially final component takes no steps;
--   4. $M(\mathrm{AMP}(r,e))$ is the halting machine if the initial state of $M(e)$ is final; otherwise it loads its input onto $r$ private copies of $M(e)$ in one sweep, runs them round robin, and when copy $i$ halts compares its output with that of every halted copy; if more than $r/2$ halted copies share copy $i$'s output it copies that output and halts, and if all copies have halted without such a majority it halts with empty output.
--
--   $P_e(x;t,w)$ denotes $P_{M(e)}(x;t,w)$.
--
--   **Formalization Note** Descriptions form an inductive type charged by the length of their strings; by Lemma 3.7 this is the paper's set $E$. The loading, comparison and copy routines of AMP are fixed by the paper only by behaviour (pp.25–26, p.29); they are pinned here (the two comparison heads return to cell $0$ together; the copy routine returns copy $i$'s output head, then copies in one sweep; copies are indexed from $0$). Routine moves of a copy's classical head are given to the qubit heads having that tape as companion.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 3.6, p.24; pp.25–26; p.29

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Machine
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_GlueRoutines

open Classical

noncomputable section

namespace QuantumKtSoI

/-- **Descriptions** (Definition 3.6, p.24): `BASE(A)` for every machine `A` (a valid coded
machine), `LIT(d)` for every string `d`, `SEQ_g(e₁, e₂)` for every glue mode `g`, and
`AMP(r, e)` for every integer `r ≥ 1`. The binary string of a description is `Desc.bits`.

**Formalization Note** The paper's set `E` is the set of the binary strings `bits e`; by
Lemma 3.7 (unique parsing) each such string has exactly one parse, so ranging over `Desc` and
charging `|bits e|` is ranging over `E`. -/
inductive Desc
  | base (A : {A : CodedMachine // A.Valid})
  | lit (d : List Bool)
  | seq (g : Glue) (e₁ e₂ : Desc)
  | amp (r : ℕ+) (e : Desc)

/-- The binary string of a description (Definition 3.6, p.24): `BASE(A) = 000⌜A⌝‾`,
`LIT(d) = 001 d̄`, `SEQ_g(e₁,e₂) = t_g e₁ e₂` with `t_feed = 010`, `t_cat = 011`, `t_pair = 100`,
and `AMP(r,e) = 101 r̄ e`. -/
def Desc.bits : Desc → List Bool
  | .base A => [false, false, false] ++ sd A.1.encode
  | .lit d => [false, false, true] ++ sd d
  | .seq .feed e₁ e₂ => [false, true, false] ++ e₁.bits ++ e₂.bits
  | .seq .cat e₁ e₂ => [false, true, true] ++ e₁.bits ++ e₂.bits
  | .seq .pair e₁ e₂ => [true, false, false] ++ e₁.bits ++ e₂.bits
  | .amp r e => [true, false, true] ++ sdNat r ++ e.bits

/-- `true` iff the symbol is a bit. -/
def Sym.isBit (a : Sym) : Bool := decide (a = Sym.b0 ∨ a = Sym.b1)

/-! ### `M(LIT(d))` -/

/-- The machine `M(LIT(d))` (p.25): only its input tape (`false`) and output tape (`true`);
classical states `q₀, …, q_{|d|}` (`some i`) and one final state `q_fin` (`none`); the only active
tape is the output tape. In `q₀` it writes back the scanned symbol, moves the output head right,
and enters `q₁`, or `q_fin` if `d = ε`; in `qᵢ`, `1 ≤ i ≤ |d|`, it writes `dᵢ` if the scanned
symbol is not `⊢` and writes back `⊢` otherwise, moves right, and enters `q_{i+1}`, or `q_fin` if
`i = |d|`. -/
def litMachine (d : List Bool) : Machine where
  Q := Option (Fin (d.length + 1))
  T := Bool
  kind := fun _ => TapeKind.classical
  alph := fun _ => ioAlph
  inT := false
  outT := true
  companion := id
  init := some 0
  isFinal := fun q => q.isNone
  isGate := fun _ => false
  act := fun _ => {true}
  δ := fun q σ =>
    match q with
    | none => (none, σ, fun _ => Move.N)
    | some i =>
        let nxt : Option (Fin (d.length + 1)) :=
          if h : i.val + 1 ≤ d.length then some ⟨i.val + 1, by omega⟩ else none
        let w : Sym :=
          if i.val = 0 then σ true
          else if σ true = Sym.mark then Sym.mark else Sym.ofBit (d.getD (i.val - 1) false)
        (nxt, fun t => if t then w else σ t, fun t => if t then Move.R else Move.N)
  gate := fun _ => Gate.X
  gtapes := fun _ _ => false
  gnext := id
  gmove := fun _ _ => Move.N

/-! ### `M(SEQ_g(e₁, e₂))` -/

section Seq

variable (M₁ M₂ : Machine) (α : Routine 2) (β : Routine 3)

/-- Tapes of the composite: its own input and output tapes, a private copy of every tape of `M₁`
except its input tape, a private copy of every tape of `M₂`, and the work tapes of the two glue
routines (p.25). -/
abbrev SeqT : Type :=
  Unit ⊕ Unit ⊕ {t : M₁.T // t ≠ M₁.inT} ⊕ M₂.T ⊕ Fin α.nWork ⊕ Fin β.nWork

/-- States of the composite: the nonfinal states of `M₁` (phase 1), the states of the `α`
routine (phase 2), the nonfinal states of `M₂` (phase 3), the states of the `β` routine
(phase 4), and the final state. -/
abbrev SeqQ : Type :=
  {q : M₁.Q // M₁.isFinal q = false} ⊕ α.R ⊕ {q : M₂.Q // M₂.isFinal q = false} ⊕ β.R ⊕ Unit

variable {M₁ M₂ α β}

/-- The composite's own input tape (also the input tape of `M₁`). -/
def SeqT.inp : SeqT M₁ M₂ α β := Sum.inl ()
/-- The composite's own output tape. -/
def SeqT.out : SeqT M₁ M₂ α β := Sum.inr (Sum.inl ())

variable (M₁ M₂ α β)

/-- The tape of the composite standing for a tape of `M₁`. -/
def seqE₁ (t : M₁.T) : SeqT M₁ M₂ α β :=
  if h : t = M₁.inT then SeqT.inp else Sum.inr (Sum.inr (Sum.inl ⟨t, h⟩))

/-- The tape of the composite standing for a tape of `M₂`. -/
def seqE₂ (t : M₂.T) : SeqT M₁ M₂ α β := Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))

/-- The tape of `M₁` a tape of the composite stands for, if any. -/
def seqP₁ : SeqT M₁ M₂ α β → Option M₁.T
  | Sum.inl _ => some M₁.inT
  | Sum.inr (Sum.inr (Sum.inl t)) => some t.1
  | _ => none

/-- The tape of `M₂` a tape of the composite stands for, if any. -/
def seqP₂ : SeqT M₁ M₂ α β → Option M₂.T
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => some t
  | _ => none

/-- The tapes of the `α` routine: sources `x` (input tape) and `u` (copy of `M₁`'s output tape),
target the copy of `M₂`'s input tape, and its own work tapes. -/
def seqEα : RTape 2 α.nWork → SeqT M₁ M₂ α β
  | .src i => ![SeqT.inp, seqE₁ M₁ M₂ α β M₁.outT] i
  | .tgt => seqE₂ M₁ M₂ α β M₂.inT
  | .wk i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))

/-- The tapes of the `β` routine: sources `x`, `u` and `v` (copy of `M₂`'s output tape), target
the composite's output tape, and its own work tapes. -/
def seqEβ : RTape 3 β.nWork → SeqT M₁ M₂ α β
  | .src i => ![SeqT.inp, seqE₁ M₁ M₂ α β M₁.outT, seqE₂ M₁ M₂ α β M₂.outT] i
  | .tgt => SeqT.out
  | .wk i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))

/-- Kinds of the composite's tapes. -/
def seqKind : SeqT M₁ M₂ α β → TapeKind
  | Sum.inr (Sum.inr (Sum.inl t)) => M₁.kind t.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => M₂.kind t
  | _ => TapeKind.classical

/-- Companions of the composite's tapes: the copy of a qubit tape's companion (p.26). -/
def seqCompanion : SeqT M₁ M₂ α β → SeqT M₁ M₂ α β
  | Sum.inr (Sum.inr (Sum.inl t)) => seqE₁ M₁ M₂ α β (M₁.companion t.1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => seqE₂ M₁ M₂ α β (M₂.companion t)
  | t => t

/-- The state entered when `M₁` would enter `q`: `q` itself if nonfinal, else the start of
phase 2. -/
def seqν₁ (q : M₁.Q) : SeqQ M₁ M₂ α β :=
  if h : M₁.isFinal q = false then Sum.inl ⟨q, h⟩ else Sum.inr (Sum.inl α.start)

/-- The state entered when `M₂` would enter `q`: `q` itself if nonfinal, else the start of
phase 4. -/
def seqν₂ (q : M₂.Q) : SeqQ M₁ M₂ α β :=
  if h : M₂.isFinal q = false then Sum.inr (Sum.inr (Sum.inl ⟨q, h⟩))
  else Sum.inr (Sum.inr (Sum.inr (Sum.inl β.start)))

/-- A step of a component inside a larger machine: the component's transition on the copies of
its tapes (through the embedding `e` with inverse `pre`); other tapes keep their symbols and do
not move; the next state is relabelled by `ν`. -/
def compδ {T Q : Type} (M : Machine) (e : M.T → T) (pre : T → Option M.T) (ν : M.Q → Q)
    (q : M.Q) (σ : T → Sym) : Q × (T → Sym) × (T → Move) :=
  let out := M.δ q (M.mask q (σ ∘ e))
  (ν out.1, fun t => match pre t with | some s => out.2.1 s | none => σ t,
    fun t => match pre t with | some s => out.2.2 s | none => Move.N)

/-- A step of a glue routine inside a larger machine: the routine's transition on its tapes
(through `e` with inverse `pre`); every qubit tape whose companion is a routine tape receives the
same move (p.24); the next state is `wrap r'`, or `exit` when the routine exits. -/
def routineδ {T Q : Type} {n : ℕ} (ρ : Routine n) (e : RTape n ρ.nWork → T)
    (pre : T → Option (RTape n ρ.nWork)) (isQubit : T → Bool) (comp : T → T)
    (wrap : ρ.R → Q) (exit : Q) (r : ρ.R) (σ : T → Sym) : Q × (T → Sym) × (T → Move) :=
  let out := ρ.δ r (ρ.mask r (σ ∘ e))
  (match out.1 with | some r' => wrap r' | none => exit,
    fun t => match pre t with | some s => out.2.1 s | none => σ t,
    fun t => match pre t with
      | some s => out.2.2 s
      | none =>
          if isQubit t then (match pre (comp t) with | some s => out.2.2 s | none => Move.N)
          else Move.N)

/-- The inverse of an embedding, chosen classically. -/
def preOf {A T : Type} (e : A → T) (t : T) : Option A :=
  if h : ∃ a, e a = t then some h.choose else none

/-- The machine `M(SEQ_g(e₁, e₂))` (p.25) for components `M₁ = M(e₁)`, `M₂ = M(e₂)` and the glue
routines `α = α_g`, `β = β_g`. Phase 1 runs `M₁` on its copies (sharing the input tape); when
`M₁` would enter a final state, phase 2 runs `α`, which writes `α_g(x,u)` on the copy of `M₂`'s
input tape and returns its heads to cell `0`; then phase 3 runs `M₂` from its initial state;
when `M₂` would enter a final state, phase 4 runs `β`, which writes `β_g(x,u,v)` on the output
tape, and the machine enters its final state. An initially final component takes no steps. -/
def seqMachine : Machine where
  Q := SeqQ M₁ M₂ α β
  T := SeqT M₁ M₂ α β
  kind := seqKind M₁ M₂ α β
  alph := fun t =>
    match t with
    | Sum.inr (Sum.inr (Sum.inl t)) => M₁.alph t.1
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => M₂.alph t
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => α.walph i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))) => β.walph i
    | _ => ioAlph
  inT := SeqT.inp
  outT := SeqT.out
  companion := seqCompanion M₁ M₂ α β
  init := seqν₁ M₁ M₂ α β M₁.init
  isFinal := fun q => match q with | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => true | _ => false
  isGate := fun q =>
    match q with
    | Sum.inl q => M₁.isGate q.1
    | Sum.inr (Sum.inr (Sum.inl q)) => M₂.isGate q.1
    | _ => false
  act := fun q =>
    match q with
    | Sum.inl q => (M₁.act q.1).image (seqE₁ M₁ M₂ α β)
    | Sum.inr (Sum.inl r) => (α.act r).image (seqEα M₁ M₂ α β)
    | Sum.inr (Sum.inr (Sum.inl q)) => (M₂.act q.1).image (seqE₂ M₁ M₂ α β)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) => (β.act r).image (seqEβ M₁ M₂ α β)
    | _ => ∅
  δ := fun q σ =>
    match q with
    | Sum.inl q =>
        compδ M₁ (seqE₁ M₁ M₂ α β) (seqP₁ M₁ M₂ α β) (seqν₁ M₁ M₂ α β) q.1 σ
    | Sum.inr (Sum.inl r) =>
        routineδ α (seqEα M₁ M₂ α β) (preOf (seqEα M₁ M₂ α β))
          (fun t => decide (seqKind M₁ M₂ α β t = TapeKind.qubit)) (seqCompanion M₁ M₂ α β)
          (fun r' => Sum.inr (Sum.inl r')) (seqν₂ M₁ M₂ α β M₂.init) r σ
    | Sum.inr (Sum.inr (Sum.inl q)) =>
        compδ M₂ (seqE₂ M₁ M₂ α β) (seqP₂ M₁ M₂ α β) (seqν₂ M₁ M₂ α β) q.1 σ
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) =>
        routineδ β (seqEβ M₁ M₂ α β) (preOf (seqEβ M₁ M₂ α β))
          (fun t => decide (seqKind M₁ M₂ α β t = TapeKind.qubit)) (seqCompanion M₁ M₂ α β)
          (fun r' => Sum.inr (Sum.inr (Sum.inr (Sum.inl r'))))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) r σ
    | q => (q, σ, fun _ => Move.N)
  gate := fun q =>
    match q with
    | Sum.inl q => M₁.gate q.1
    | Sum.inr (Sum.inr (Sum.inl q)) => M₂.gate q.1
    | _ => Gate.X
  gtapes := fun q =>
    match q with
    | Sum.inl q => seqE₁ M₁ M₂ α β ∘ M₁.gtapes q.1
    | Sum.inr (Sum.inr (Sum.inl q)) => seqE₂ M₁ M₂ α β ∘ M₂.gtapes q.1
    | _ => fun _ => SeqT.inp
  gnext := fun q =>
    match q with
    | Sum.inl q => seqν₁ M₁ M₂ α β (M₁.gnext q.1)
    | Sum.inr (Sum.inr (Sum.inl q)) => seqν₂ M₁ M₂ α β (M₂.gnext q.1)
    | q => q
  gmove := fun q t =>
    match q with
    | Sum.inl q => (match seqP₁ M₁ M₂ α β t with | some s => M₁.gmove q.1 s | none => Move.N)
    | Sum.inr (Sum.inr (Sum.inl q)) =>
        (match seqP₂ M₁ M₂ α β t with | some s => M₂.gmove q.1 s | none => Move.N)
    | _ => Move.N

end Seq

/-! ### `M(AMP(r, e))` -/

/-- The machine with one state, which is initial and final (p.25: "If the initial state of
`M(e)` is final, the initial state of `M(AMP(r,e))` is final"); it halts at deadline `0` with
empty output. -/
def haltMachine : Machine where
  Q := Unit
  T := Bool
  kind := fun _ => TapeKind.classical
  alph := fun _ => ioAlph
  inT := false
  outT := true
  companion := id
  init := ()
  isFinal := fun _ => true
  isGate := fun _ => false
  act := fun _ => ∅
  δ := fun q σ => (q, σ, fun _ => Move.N)
  gate := fun _ => Gate.X
  gtapes := fun _ _ => false
  gnext := id
  gmove := fun _ _ => Move.N

section Amp

variable (M : Machine) (r : ℕ+)

/-- Tapes of `M(AMP(r, e))`: its own input and output tapes and `r` private copies of all tapes
of `M`, each copy with its own input tape (p.25). -/
abbrev AmpT : Type := Unit ⊕ Unit ⊕ (Fin r × M.T)

/-- States of `M(AMP(r, e))`:
* `Sum.inl k`, `k ∈ {0, 1, 2}`: the three states of the loading sweep;
* `run (i, cs, H)`: pointer `i`, current states `cs` of the copies, halted set `H`;
* `cmp (i, cs, H, j, count, agree, phase)`: comparison of the output of the halted copy `i` with
  that of copy `j`, phases `0` (return), `1` (scan), `2` (return);
* `copy (i, scanning)`: copying the output of copy `i` to the output tape;
* the final state. -/
abbrev AmpQ : Type :=
  Fin 3 ⊕ (Fin r × (Fin r → M.Q) × Finset (Fin r)) ⊕
    (Fin r × (Fin r → M.Q) × Finset (Fin r) × Fin r × Fin (r + 1) × Bool × Fin 3) ⊕
    (Fin r × Bool) ⊕ Unit

variable {M r}

/-- The state `run (i, cs, H)`. -/
def ampRun (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) : AmpQ M r :=
  Sum.inr (Sum.inl (i, cs, H))

/-- The state `cmp (i, cs, H, j, count, agree, phase)`. -/
def ampCmp (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (j : Fin r) (cnt : ℕ)
    (agree : Bool) (ph : Fin 3) : AmpQ M r :=
  Sum.inr (Sum.inr (Sum.inl (i, cs, H, j, ⟨min cnt r, by omega⟩, agree, ph)))

/-- The state `copy (i, scanning)`. -/
def ampCopy (i : Fin r) (scanning : Bool) : AmpQ M r := Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, scanning))))

/-- The final state. -/
def ampFin : AmpQ M r := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

/-- The next index after `i`, cyclically, that is not in `H` (it can be `i` itself). -/
def nextPtr (i : Fin r) (H : Finset (Fin r)) : Fin r :=
  (((List.range r).map fun o => (⟨((i : ℕ) + 1 + o) % r, Nat.mod_lt _ r.pos⟩ : Fin r)).find?
    (fun j => decide (j ∉ H))).getD i

/-- The decision after the comparisons of the newly halted copy `i` (count `cnt` of halted copies
with the output of copy `i`, copy `i` included): copy that output if `cnt > r/2`; otherwise enter
the final state with empty output if every copy has halted; otherwise move the pointer. -/
def ampDecide (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (cnt : ℕ) : AmpQ M r :=
  if (r : ℕ) < 2 * cnt then ampCopy i false
  else if H = Finset.univ then ampFin
  else ampRun (nextPtr i H) cs H

/-- The comparison stage entered for copy `i` with halted set `H`, from the copy `j₀` on: the next
comparison partner in `H \ {i}` at least `j₀` in increasing order, or the decision. -/
def ampNextCmp (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (lo : Option (Fin r))
    (cnt : ℕ) : AmpQ M r :=
  let rest := (H.erase i).filter fun j => match lo with | none => True | some j₀ => j₀ < j
  if h : rest.Nonempty then ampCmp i cs H (rest.min' h) cnt true 0
  else ampDecide i cs H cnt

/-- The state entered after copy `i` takes a step into the state `q'` (p.25): if `q'` is nonfinal,
the pointer moves to the next running copy; otherwise `i` is added to the halted set and the
comparison routine starts with count `1`. -/
def ampAfter (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (q' : M.Q) : AmpQ M r :=
  let cs' := Function.update cs i q'
  if M.isFinal q' = false then ampRun (nextPtr i H) cs' H
  else ampNextCmp i cs' (insert i H) none 1

variable (M r)

/-- The copy tapes. -/
def ampCp (i : Fin r) (t : M.T) : AmpT M r := Sum.inr (Sum.inr (i, t))

/-- The tape of a copy a tape stands for. -/
def ampPre : AmpT M r → Option (Fin r × M.T)
  | Sum.inr (Sum.inr p) => some p
  | _ => none

/-- A routine move `d` given to the classical tapes selected by `sel`, extended to every qubit copy
tape whose companion (in its copy) is selected (p.25: "Whenever the loading or comparison routine
moves a classical head, it gives the same move to every qubit head having that tape as its
companion"). -/
def ampMoves (d : AmpT M r → Move) : AmpT M r → Move
  | Sum.inr (Sum.inr (i, t)) =>
      if M.kind t = TapeKind.qubit then d (ampCp M r i (M.companion t)) else d (ampCp M r i t)
  | t => d t

/-- The input tape. -/
def ampIn : AmpT M r := Sum.inl ()
/-- The output tape. -/
def ampOut : AmpT M r := Sum.inr (Sum.inl ())

/-- The transition of a classical state of `M(AMP(r,e))` that is not a copy step. -/
def ampRoutineδ (q : AmpQ M r) (σ : AmpT M r → Sym) :
    AmpQ M r × (AmpT M r → Sym) × (AmpT M r → Move) :=
  let isLoad : AmpT M r → Prop := fun t =>
    t = ampIn M r ∨ ∃ i, t = ampCp M r i M.inT
  let allMove : Move → AmpT M r → Move := fun d t => if isLoad t then d else Move.N
  match q with
  | Sum.inl k =>
      if k = 0 then (Sum.inl 1, σ, ampMoves M r (allMove Move.R))
      else if k = 1 then
        (if Sym.isBit (σ (ampIn M r)) then
          (Sum.inl 1, fun t => if t = ampIn M r then σ t else σ (ampIn M r),
            ampMoves M r (allMove Move.R))
        else (Sum.inl 2, σ, ampMoves M r (allMove Move.L)))
      else
        (if σ (ampIn M r) = Sym.mark then (ampRun ⟨0, r.pos⟩ (fun _ => M.init) ∅, σ, fun _ => Move.N)
        else (Sum.inl 2, σ, ampMoves M r (allMove Move.L)))
  | Sum.inr (Sum.inr (Sum.inl (i, cs, H, j, cnt, agree, ph))) =>
      let ti := ampCp M r i M.outT
      let tj := ampCp M r j M.outT
      let a := σ ti
      let b := σ tj
      let back : AmpT M r → Move := fun t =>
        if (t = ti ∧ a ≠ Sym.mark) ∨ (t = tj ∧ b ≠ Sym.mark) then Move.L else Move.N
      let both : Move → AmpT M r → Move := fun d t => if t = ti ∨ t = tj then d else Move.N
      if ph = 0 then
        (if a = Sym.mark ∧ b = Sym.mark then
          (ampCmp i cs H j cnt true 1, σ, ampMoves M r (both Move.R))
        else (ampCmp i cs H j cnt agree 0, σ, ampMoves M r back))
      else if ph = 1 then
        (if Sym.isBit a ∧ Sym.isBit b then
          (ampCmp i cs H j cnt (agree && decide (a = b)) 1, σ, ampMoves M r (both Move.R))
        else
          (ampCmp i cs H j (cnt + if agree ∧ ¬ Sym.isBit a ∧ ¬ Sym.isBit b then 1 else 0) agree 2,
            σ, ampMoves M r (both Move.L)))
      else
        (if a = Sym.mark ∧ b = Sym.mark then (ampNextCmp i cs H (some j) cnt, σ, fun _ => Move.N)
        else (ampCmp i cs H j cnt agree 2, σ, ampMoves M r back))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, scanning)))) =>
      let ti := ampCp M r i M.outT
      let a := σ ti
      if scanning = false then
        (if a = Sym.mark then
          (ampCopy i true, σ,
            ampMoves M r fun t => if t = ti ∨ t = ampOut M r then Move.R else Move.N)
        else (ampCopy i false, σ, ampMoves M r fun t => if t = ti then Move.L else Move.N))
      else
        (if Sym.isBit a then
          (ampCopy i true, fun t => if t = ampOut M r then a else σ t,
            ampMoves M r fun t => if t = ti ∨ t = ampOut M r then Move.R else Move.N)
        else (ampFin, σ, fun _ => Move.N))
  | q => (q, σ, fun _ => Move.N)

/-- The machine `M(AMP(r, e))` for `M = M(e)` with nonfinal initial state (pp.25–26, p.29).

* **Loading** (`2|x| + 3` steps, p.29): at cell `0` write back and move the input head and the `r`
  copy input heads right; while the input tape scans a bit `s`, write `s` on every copy input tape
  and move all right; at the first non-bit move all left; move all left until the input tape
  scans `⊢`, then enter `run (1, init, ∅)` without moving.
* **Round robin**: in `run (i, cs, H)` the machine performs one step of copy `i` (its kind, gate
  and active tapes are those of `cs i` on copy `i`'s tapes); if copy `i` enters a nonfinal state
  the pointer moves to the next index after `i`, cyclically, not in `H`.
* **Comparison** (pp.25–26): when copy `i` halts, `i` is added to `H`, the count is set to `1`,
  and for each `j ∈ H \ {i}` in increasing order the two output heads return to cell `0`, move
  right together until one of them scans, from cell `1` on, a symbol outside `{0,1}` (adding `1`
  to the count if both do so at the same cell and all earlier scanned pairs agreed), and return to
  cell `0`. If the count exceeds `r/2` the machine copies the output of copy `i` to its own output
  tape and enters its final state; otherwise, if `H = [r]` it enters its final state with empty
  output; otherwise the pointer moves to the next index not in `H`. Pointer moves and decisions are
  made by the transition that ends the step of copy `i` or the comparison.

Every routine move of a copy's classical head is given to the qubit heads having that tape as
their companion.

**Formalization Note** The paper fixes the loading, comparison and copy routines only by this
behaviour ("We fix these routines once and for all", p.26); the formalization pins them as above:
the two comparison heads return simultaneously, and the copy routine returns copy `i`'s output
head and then copies in one sweep. The copies are indexed `0, …, r−1` and the pointer starts at
`0`. The counts live in the finite control, so there are no work tapes. -/
def ampCore : Machine where
  Q := AmpQ M r
  T := AmpT M r
  kind := fun t => match t with | Sum.inr (Sum.inr (_, t)) => M.kind t | _ => TapeKind.classical
  alph := fun t => match t with | Sum.inr (Sum.inr (_, t)) => M.alph t | _ => ioAlph
  inT := ampIn M r
  outT := ampOut M r
  companion := fun t =>
    match t with | Sum.inr (Sum.inr (i, t)) => ampCp M r i (M.companion t) | t => t
  init := Sum.inl 0
  isFinal := fun q => match q with | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => true | _ => false
  isGate := fun q =>
    match q with
    | Sum.inr (Sum.inl (i, cs, _)) => M.isGate (cs i) && !M.isFinal (cs i)
    | _ => false
  act := fun q =>
    match q with
    | Sum.inl _ => insert (ampIn M r) (Finset.univ.image fun i => ampCp M r i M.inT)
    | Sum.inr (Sum.inl (i, cs, _)) =>
        if M.isFinal (cs i) then ∅ else (M.act (cs i)).image (ampCp M r i)
    | Sum.inr (Sum.inr (Sum.inl (i, _, _, j, _, _, _))) => {ampCp M r i M.outT, ampCp M r j M.outT}
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, _)))) => {ampCp M r i M.outT, ampOut M r}
    | _ => ∅
  δ := fun q σ =>
    match q with
    | Sum.inr (Sum.inl (i, cs, H)) =>
        if M.isFinal (cs i) then (ampFin, σ, fun _ => Move.N)
        else compδ M (ampCp M r i)
          (fun t => match ampPre M r t with | some (j, s) => if j = i then some s else none | none => none)
          (ampAfter i cs H) (cs i) σ
    | q => ampRoutineδ M r q σ
  gate := fun q => match q with | Sum.inr (Sum.inl (i, cs, _)) => M.gate (cs i) | _ => Gate.X
  gtapes := fun q =>
    match q with
    | Sum.inr (Sum.inl (i, cs, _)) => ampCp M r i ∘ M.gtapes (cs i)
    | _ => fun _ => ampIn M r
  gnext := fun q =>
    match q with
    | Sum.inr (Sum.inl (i, cs, H)) => ampAfter i cs H (M.gnext (cs i))
    | q => q
  gmove := fun q t =>
    match q with
    | Sum.inr (Sum.inl (i, cs, _)) =>
        (match ampPre M r t with
          | some (j, s) => if j = i then M.gmove (cs i) s else Move.N
          | none => Move.N)
    | _ => Move.N

/-- The machine `M(AMP(r, e))` for `M = M(e)`: the one-state halting machine when the initial state
of `M` is final, and `ampCore M r` otherwise (p.25). -/
def ampMachine : Machine :=
  if M.isFinal M.init then haltMachine else ampCore M r

end Amp

/-- The machine `M(e)` denoted by a description (p.25), for a fixed set `G` of glue routines:
`M(BASE(A)) = A`, `M(LIT(d))`, `M(SEQ_g(e₁, e₂))` and `M(AMP(r, e))` as constructed above. -/
def Desc.machine (G : GlueRoutines) : Desc → Machine
  | .base A => A.1.toMachine
  | .lit d => litMachine d
  | .seq g e₁ e₂ => seqMachine (e₁.machine G) (e₂.machine G) (G.α g) (G.β g)
  | .amp r e => ampMachine (e.machine G) r

/-- `P_e(x; t, w) = P_{M(e)}(x; t, w)` (p.25). -/
def Desc.prob (G : GlueRoutines) (e : Desc) (x : List Bool) (t : ℕ) (w : List Bool) : ℝ :=
  (e.machine G).outputProb x t w

/-- `P_e(x; T, w) = P_{M(e)}(x; ⌊T⌋, w)` at a real deadline `T ≥ 0` (p.22). -/
def Desc.probR (G : GlueRoutines) (e : Desc) (x : List Bool) (T : ℝ) (w : List Bool) : ℝ :=
  (e.machine G).outputProbR x T w

end QuantumKtSoI


