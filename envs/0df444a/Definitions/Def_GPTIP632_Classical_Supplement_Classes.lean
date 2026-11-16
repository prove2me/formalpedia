-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_Classes
-- name    : GPTIP632_Classical_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:14.13255+00:00
-- url     : https://prove2.me/theorems/a3b751d0-c829-4e3b-a3f6-6b9915f45060
-- title:
--   Message bounds, quantum verifiers, quantum values and theory morphisms
-- statement:
--   A nontrivial message is a nonempty elementary wire list, counted in both directions in every round. GIP with bound $k$ means at most $k$ such messages; GMA allows at most one and requires all questions to be empty. Threshold classes use value at least $c$ on yes-instances and at most $s$ on no-instances. The quantum class QIP is defined independently of the ambient theory on QC with quantum private memories of arbitrary finite dimension and arbitrary quantum channels; its messages consist of qubits, while its internal recorded information may be classical. A containing theory has an elementary qubit with a real Hermitian basis, the ordinary PSD cone on every multiqubit register, all quantum channels and CP instruments, and the specified quantum and classical gates. A quantum verifier in it is the same QC circuit with wires and gates mapped by this embedding. The induced response kernel contracts the actual published prover's memory indices, beginning with its initial state and ending with its unit effect. Complete positivity quantifies over every finite ancilla dimension. A subtheory preserves system coordinates, cones, units, composites, allowed operations and gates; presentation aliases may map to the same physical system. A theory isomorphism has mutually inverse real matrices, preserves cones and units, respects tensor composition, and maps channels and instruments onto each other. It does not require designated gates to match.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.14, 17–19, 22–23, 28, 32–35 (PDF pp.16, 19–21, 24–25, 30, 34–37), Examples B.3, B.5, B.17–B.23, Definitions D.3–D.4, F.1, §G

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Theories
import Definitions.Def_GPTIP632_Classical_Protocol
import Definitions.Def_KTUnitary_Synth_PromisePSPACE

set_option autoImplicit false

/-!
# Message counts, thresholds, quantum verifiers, QIP, quantum combs, subtheories, isomorphisms

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026): Definition A.4 (pp.12–13, PDF pp.14–15),
Definition D.3 and Definition D.4 (pp.22–23, PDF pp.24–25), Definition B.16 and the isomorphism of
theories (pp.17–18, PDF pp.19–20), Definition F.1 (p.28, PDF p.30), Lemma F.9 (p.31, PDF p.33).

All classes are classes of promise problems and reuse the published verifiers, prover strategies
and values (`VData`, `Prover`, `VData.val`) of `GPTIP632.Classical`.
-/

noncomputable section

namespace GPTIP632.Classical.Supplement

open GPTIP632.Classical Matrix KTUnitary.Synth QAlgorithms.Complexity QAdvFew.PoQOracle
open scoped Kronecker ComplexOrder

attribute [local instance] _root_.Classical.propDecidable

/-! ### Message counts and the classes `GIP(G; k)`, `GMA(G)`, `GIP_{c,s}` (Definition D.3) -/

/-- The number of nontrivial messages on input `x`: the messages `Q_i`, `A_i` (`i < r(|x|)`, both
directions) whose register is not the trivial system (a nonempty list of wires). -/
def msgCount {G : Theory} (V : VData G) (x : Str) : ℕ :=
  (((List.range (V.R x)).map fun i => [V.Q x i, V.A x i]).flatten).countP fun l => !l.isEmpty

/-- **`GIP_{c,s}(G; k)`** (Definition D.3, with thresholds `c`, `s`): promise problems with a
verifier for `G` with at most `k` nontrivial messages on every input (`k = ⊤`: no bound), value at
least `c` on `L_yes` and at most `s` on `L_no`. -/
def GIPgen (G : Theory) (c s : ℝ) (k : ℕ∞) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData G, V.IsVerifier ∧ (∀ x, (msgCount V x : ℕ∞) ≤ k) ∧
    (∀ x ∈ L.1, c ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ s)}

/-- **`GIP(G; k)`** (Definition D.3): at most `k` nontrivial messages, thresholds `2/3`, `1/3`. -/
def GIPk (G : Theory) (k : ℕ) : Set KTUnitary.Synth.PromiseProblem := GIPgen G (2 / 3) (1 / 3) k

/-- **`GMA(G)`** (Definition D.3): `GIP(G; 1)` with the single nontrivial message sent by the
prover (every question `Q_i` is trivial). -/
def GMA (G : Theory) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData G, V.IsVerifier ∧ (∀ x i, i < V.R x → V.Q x i = []) ∧ (∀ x, msgCount V x ≤ 1) ∧
    (∀ x ∈ L.1, (2 : ℝ) / 3 ≤ V.val x) ∧ (∀ x ∈ L.2, V.val x ≤ 1 / 3)}

/-! ### QC without adjoined systems, quantum provers, QIP (Definition A.4) -/

/-- `QC` (Example B.18), given its theory axioms. -/
def qc0 (h : (qcPre []).Ok) : Theory := (qcPre []).toTheory h

/-- A QIP verifier: a verifier of QC all of whose messages are qubit registers (Definition A.4). -/
def QubitMsgs {h : (qcPre []).Ok} (V : VData (qc0 h)) : Prop :=
  ∀ x i, i < V.R x → ∀ a ∈ V.Q x i ++ V.A x i, a = QCElem.qubit

/-- **`val_quantum`** (Definition A.4, Theorem F.3): the supremum of the acceptance probability over
quantum provers, i.e., prover strategies of QC whose private systems are quantum systems
(finite-dimensional quantum memory) and whose channels are arbitrary quantum channels. -/
def valQ {h : (qcPre []).Ok} (V : VData (qc0 h)) (x : Str) : ℝ :=
  sSup {t | ∃ P : Prover V x, (∀ i, Tree.IsQuantum (P.P i).1) ∧ V.accProb x P = t}

/-- **`QIP_{c,s}(k)`** (Definition A.4): promise problems with a QIP verifier with at most `k`
nontrivial messages, quantum value at least `c` on `L_yes` and at most `s` on `L_no`. -/
def QIPgen (h : (qcPre []).Ok) (c s : ℝ) (k : ℕ∞) : Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData (qc0 h), V.IsVerifier ∧ QubitMsgs V ∧ (∀ x, (msgCount V x : ℕ∞) ≤ k) ∧
    (∀ x ∈ L.1, c ≤ valQ V x) ∧ (∀ x ∈ L.2, valQ V x ≤ s)}

/-- **QIP(k)**. -/
def QIPk (h : (qcPre []).Ok) (k : ℕ) : Set KTUnitary.Synth.PromiseProblem := QIPgen h (2 / 3) (1 / 3) k

/-- **QIP**. -/
def QIP (h : (qcPre []).Ok) : Set KTUnitary.Synth.PromiseProblem := QIPgen h (2 / 3) (1 / 3) ⊤

/-! ### Theories containing quantum theory (Definition D.4) -/

/-- The `2 × 2` matrix of a wire coordinate, given a qubit element `q` with coordinate basis `B`
and a classical-bit element `b`: `B e` on a qubit coordinate `e`, the diagonal unit `E_ii` on the
bit label `i`, `0` on other wires. -/
def qbWire (C : Core) (q b : C.Elem) (hb : C.elem b = C.cl 1)
    (B : (C.sys (C.elem q)).ι → Matrix (Fin 2) (Fin 2) ℂ) (w : C.Wire) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h : w.1 = q then B (cast (congrArg (fun a => (C.sys (C.elem a)).ι) h) w.2)
  else if h' : w.1 = b then
    (fun i => Matrix.single i i 1)
      (C.clEquiv 1 (cast (congrArg (fun S => (C.sys S).ι) hb)
        (cast (congrArg (fun a => (C.sys (C.elem a)).ι) h') w.2)))
  else 0

/-- Complete positivity of a map between registers, in raw coordinates: for every ancilla
dimension `d`, `Φ ⊗ id_d` maps positive semidefinite operators to positive semidefinite operators
(the operator of a coordinate `j` of the input register being `rawMatOf wm n (regRaw j)`). -/
def IsCPreg {C : Core} (wm : C.Wire → Matrix (Fin 2) (Fin 2) ℂ) (lin lout : List C.Elem)
    (Φ : Matrix (C.sys (C.reg lout)).ι (C.sys (C.reg lin)).ι ℝ) : Prop :=
  ∀ (d : ℕ) (c : (C.sys (C.reg lin)).ι → Matrix (Fin d) (Fin d) ℂ),
    (∑ j, rawMatOf wm lin.length (regRaw C lin j) ⊗ₖ c j).PosSemidef →
    (∑ j, (∑ i, ((Φ i j : ℝ) : ℂ) • rawMatOf wm lout.length (regRaw C lout i)) ⊗ₖ c j).PosSemidef

/-- **Definition D.4 (theory containing quantum theory)**, pp.22–23, with the gates of a quantum
verifier. The data: the qubit `q` (an elementary system) with a real basis `B` of `Herm_2(ℂ)` as its
coordinates; a classical bit `b`.

1. (i) `Q` is the system `(Herm_2(ℂ), Pos_2, Tr)` in the coordinates `B`, and for every `n` the
   composite `Q^{⊗n}` (the register of `n` qubit wires) is `(Herm(C^{2^n}), Pos_{2^n}, Tr)` under
   the identification of (T1): its cone is the set of coordinate vectors whose operator
   `∑_k ξ_k B_{k_1} ⊗ ⋯ ⊗ B_{k_n}` is positive semidefinite.
2. (ii) every CPTP map `Q^{⊗n} → Q^{⊗m}` is an allowed channel, and every family of CP maps with a
   CPTP sum is an allowed instrument.
3. (iii) the gate set contains the quantum gates of Example B.18 (`QGate`, with the qubit discard
   of (T4)) and, on `b`, the classical gates of (T4) (`CGate`): each named gate acts, on the raw
   wire coordinates, as its Kraus operators prescribe. -/
structure QEmb (G : Theory) where
  q : G.C.Elem
  b : G.C.Elem
  hb : G.C.elem b = G.C.cl 1
  B : (G.C.sys (G.C.elem q)).ι → Matrix (Fin 2) (Fin 2) ℂ
  B_herm : ∀ e, (B e).IsHermitian
  B_card : Fintype.card (G.C.sys (G.C.elem q)).ι = 4
  B_indep : LinearIndependent ℝ B
  unit_eq : ∀ e, (G.C.sys (G.C.elem q)).unit e = (B e).trace.re
  cone_reg : ∀ (n : ℕ) (ξ : (G.C.sys (G.C.reg (List.replicate n q))).ι → ℝ),
    ξ ∈ (G.C.sys (G.C.reg (List.replicate n q))).cone ↔
      (∑ k, ((ξ k : ℝ) : ℂ) • rawMatOf (qbWire G.C q b hb B) n
        (regRaw G.C (List.replicate n q) k)).PosSemidef
  chan_cptp : ∀ (n m : ℕ)
    (Φ : Matrix (G.C.sys (G.C.reg (List.replicate m q))).ι (G.C.sys (G.C.reg (List.replicate n q))).ι ℝ),
    IsCPreg (qbWire G.C q b hb B) _ _ Φ →
    (G.C.sys (G.C.reg (List.replicate m q))).unit ᵥ* Φ = (G.C.sys (G.C.reg (List.replicate n q))).unit →
    Φ ∈ G.C.chan _ _
  inst_cp : ∀ (n m k : ℕ) (Φ : Fin k → Matrix (G.C.sys (G.C.reg (List.replicate m q))).ι
      (G.C.sys (G.C.reg (List.replicate n q))).ι ℝ),
    (∀ o, IsCPreg (qbWire G.C q b hb B) _ _ (Φ o)) →
    (G.C.sys (G.C.reg (List.replicate m q))).unit ᵥ* (∑ o, Φ o) =
      (G.C.sys (G.C.reg (List.replicate n q))).unit →
    Φ ∈ G.C.inst _ _ k
  qg : QGate → G.Gate
  qg_ins : ∀ g, G.ins (qg g) = g.ins.map fun a => QB.casesOn a q b
  qg_outs : ∀ g, G.outs (qg g) = g.outs.map fun a => QB.casesOn a q b
  qg_nout : ∀ g, G.nout (qg g) = g.nout
  qg_ker : ∀ (g : QGate) (o : Fin g.nout) (kin : List G.C.Wire), kin ∈ G.C.coords (G.ins (qg g)) →
    ∑ kout ∈ G.C.coords (G.outs (qg g)),
        ((G.gk (qg g) o kout kin : ℝ) : ℂ) • rawMatOf (qbWire G.C q b hb B) g.outs.length kout =
      krausL (g.kraus o) (rawMatOf (qbWire G.C q b hb B) g.ins.length kin)
  cg : CGate → G.Gate
  cg_ins : ∀ g, G.ins (cg g) = g.ins.map fun a => QB.casesOn a q b
  cg_outs : ∀ g, G.outs (cg g) = g.outs.map fun a => QB.casesOn a q b
  cg_nout : ∀ g, G.nout (cg g) = g.nout
  cg_ker : ∀ (g : CGate) (o : Fin g.nout) (kin : List G.C.Wire), kin ∈ G.C.coords (G.ins (cg g)) →
    ∑ kout ∈ G.C.coords (G.outs (cg g)),
        ((G.gk (cg g) o kout kin : ℝ) : ℂ) • rawMatOf (qbWire G.C q b hb B) g.outs.length kout =
      krausL (g.kraus o) (rawMatOf (qbWire G.C q b hb B) g.ins.length kin)

/-- `G` **contains quantum theory** (Definition D.4). -/
def ContainsQuantum (G : Theory) : Prop := Nonempty (QEmb G)

namespace QEmb

variable {G : Theory} (E : QEmb G)

/-- The wire matrices of `G` given by the embedding. -/
def wire : G.C.Wire → Matrix (Fin 2) (Fin 2) ℂ := qbWire G.C E.q E.b E.hb E.B

/-- The elementary systems of QC as elementary systems of `G`. -/
def elemMap : QCElem [] → G.C.Elem
  | .qubit => E.q
  | .bit => E.b
  | .adj i => i.elim0

/-- The gates of QC as gates of `G`. -/
def gateMap : QCGate [] → G.Gate
  | .inl g => E.qg g
  | .inr (.inl g) => E.cg g
  | .inr (.inr (.prep i)) => i.elim0
  | .inr (.inr (.read i)) => i.elim0
  | .inr (.inr (.disc i)) => i.elim0

/-- A verifier of QC read as a verifier of `G` (Definition D.4: "a quantum verifier for `G` …
is exactly a QIP verifier"): the same circuit, with the elementary systems and gates of QC replaced
by those of `G`. -/
def push {h : (qcPre []).Ok} (V : VData (qc0 h)) : VData G where
  r := V.r
  bound := V.bound
  Q := fun x i => (V.Q x i).map E.elemMap
  A := fun x i => (V.A x i).map E.elemMap
  next := fun x i z => match V.next x i z with
    | .halt => .halt
    | .apply g ws => .apply (E.gateMap g) ws

end QEmb

/-- **`GIP_qm,{c,s}(G; k)`** (Definition D.3): promise problems with a quantum verifier for `G`
(Definition D.4: a QIP verifier, read in `G`, that is a verifier for `G`) with at most `k`
nontrivial messages, whose value over all prover strategies of `G` is at least `c` on `L_yes` and at
most `s` on `L_no`. -/
def GIPqmGen (G : Theory) (E : QEmb G) (h : (qcPre []).Ok) (c s : ℝ) (k : ℕ∞) :
    Set KTUnitary.Synth.PromiseProblem :=
  {L | ∃ V : VData (qc0 h), V.IsVerifier ∧ QubitMsgs V ∧ (E.push V).IsVerifier ∧
    (∀ x, (msgCount V x : ℕ∞) ≤ k) ∧
    (∀ x ∈ L.1, c ≤ (E.push V).val x) ∧ (∀ x ∈ L.2, (E.push V).val x ≤ s)}

/-- **`GIP_qm(G; k)`**. -/
def GIPqmk (G : Theory) (E : QEmb G) (h : (qcPre []).Ok) (k : ℕ) : Set KTUnitary.Synth.PromiseProblem :=
  GIPqmGen G E h (2 / 3) (1 / 3) k

/-- **`GIP_qm(G)`**. -/
def GIPqm (G : Theory) (E : QEmb G) (h : (qcPre []).Ok) : Set KTUnitary.Synth.PromiseProblem :=
  GIPqmGen G E h (2 / 3) (1 / 3) ⊤

/-! ### Quantum combs (Definition F.1) -/

/-- The concatenation of the message registers of the first `j` rounds. -/
def catMsgs {α : Type} (M : ℕ → List α) (j : ℕ) : List α := ((List.range j).map M).flatten

/-- The total length of the message registers of the first `j` rounds. -/
def lenMsgs {α : Type} (M : ℕ → List α) (j : ℕ) : ℕ := (catMsgs M j).length

/-- The kernel of the prover's first `j` rounds with its private system `P_j` kept: on raw
coordinates `kA` of `M'_1 ⋯ M'_j` (answers) and `kQ` of `M_1 ⋯ M_j` (questions),
`(Π_j ⊗ id) ∘ ⋯ ∘ (Π_1 ⊗ id) ∘ (τ_0 ⊗ id)` (Definition F.1). -/
def combKer {G : Theory} {V : VData G} {x : Str} (P : Prover V x) :
    (j : ℕ) → List G.C.Wire → List G.C.Wire → (G.C.sys (P.P j)).ι → ℝ
  | 0 => fun kA kQ p => if kA = [] ∧ kQ = [] then P.τ0 p else 0
  | j + 1 => fun kA kQ p' => ∑ p : (G.C.sys (P.P j)).ι,
      VData.chanKer (P.ch j) (kA.drop (lenMsgs (V.A x) j)) p' (kQ.drop (lenMsgs (V.Q x) j)) p *
        combKer P j (kA.take (lenMsgs (V.A x) j)) (kQ.take (lenMsgs (V.Q x) j)) p

/-- **The comb `S^{(j)}` induced by a prover strategy** (Definition F.1): the kernel of
`(id ⊗ u_{P_j}) ∘ (Π_j ⊗ id) ∘ ⋯ ∘ (Π_1 ⊗ id) ∘ (τ_0 ⊗ id)` from the questions of the first `j`
rounds to the answers of the first `j` rounds. `S^{(0)} = 1`; `S = S^{(r)}`. -/
def comb {G : Theory} {V : VData G} {x : Str} (P : Prover V x) (j : ℕ)
    (kA kQ : List G.C.Wire) : ℝ :=
  ∑ p, (G.C.sys (P.P j)).unit p * combKer P j kA kQ p

/-- Complete positivity of a kernel `S` from the register `lin` to the register `lout`, in raw
coordinates (Definition F.1 (i)): for every ancilla dimension `d`, `S ⊗ id_d` maps positive
semidefinite operators on `lin ⊗ ℂ^d` to positive semidefinite operators on `lout ⊗ ℂ^d`. -/
def IsCPker {C : Core} (wm : C.Wire → Matrix (Fin 2) (Fin 2) ℂ) (lin lout : List C.Elem)
    (S : List C.Wire → List C.Wire → ℝ) : Prop :=
  ∀ (d : ℕ) (c : List C.Wire → Matrix (Fin d) (Fin d) ℂ),
    (∑ kq ∈ C.coords lin, rawMatOf wm lin.length kq ⊗ₖ c kq).PosSemidef →
    (∑ kq ∈ C.coords lin,
      (∑ ka ∈ C.coords lout, ((S ka kq : ℝ) : ℂ) • rawMatOf wm lout.length ka) ⊗ₖ c kq).PosSemidef

/-! ### Subtheories and isomorphisms of theories (Definition B.16, p.18) -/

/-- **`G` is a subtheory of `G'` with gate set contained in that of `G'`** (Definition B.16,
Lemma D.5): every system of `G` is a system of `G'` (a map of system presentations, identifying
coordinates, cones, units and composites), every allowed channel and instrument of `G` is one of
`G'`, and every gate of `G` is a gate of `G'` (same wires, same outcome maps). -/
structure Subtheory (G G' : Theory) where
  sys : G.C.Sys → G'.C.Sys
  coord : ∀ A, (G.C.sys A).ι ≃ (G'.C.sys (sys A)).ι
  cone_iff : ∀ A (ξ : (G.C.sys A).ι → ℝ), ξ ∈ (G.C.sys A).cone ↔ ξ ∘ (coord A).symm ∈ (G'.C.sys (sys A)).cone
  unit_eq : ∀ A k, (G'.C.sys (sys A)).unit (coord A k) = (G.C.sys A).unit k
  sys_comp : ∀ A B, sys (G.C.comp A B) = G'.C.comp (sys A) (sys B)
  coord_comp : ∀ A B (k : (G.C.sys (G.C.comp A B)).ι),
    G'.C.compEquiv (sys A) (sys B) (cast (congrArg (fun S => (G'.C.sys S).ι) (sys_comp A B))
      (coord _ k)) = (coord A (G.C.compEquiv A B k).1, coord B (G.C.compEquiv A B k).2)
  chan_sub : ∀ A B, ∀ Φ ∈ G.C.chan A B, Matrix.reindex (coord B) (coord A) Φ ∈ G'.C.chan (sys A) (sys B)
  inst_sub : ∀ A B k, ∀ Φ ∈ G.C.inst A B k,
    (fun o => Matrix.reindex (coord B) (coord A) (Φ o)) ∈ G'.C.inst (sys A) (sys B) k
  el : G.C.Elem → G'.C.Elem
  elem_eq : ∀ a, sys (G.C.elem a) = G'.C.elem (el a)
  gate : G.Gate → G'.Gate
  ins_eq : ∀ g, G'.ins (gate g) = (G.ins g).map el
  outs_eq : ∀ g, G'.outs (gate g) = (G.outs g).map el
  nout_eq : ∀ g, G'.nout (gate g) = G.nout g
  gk_eq : ∀ g o (kout kin : List G.C.Wire),
    G'.gk (gate g) o (kout.map fun w => ⟨el w.1, cast (congrArg (fun S => (G'.C.sys S).ι) (elem_eq w.1))
        (coord _ w.2)⟩)
      (kin.map fun w => ⟨el w.1, cast (congrArg (fun S => (G'.C.sys S).ι) (elem_eq w.1))
        (coord _ w.2)⟩) = G.gk g o kout kin

/-- **An isomorphism of theories** (p.18): a family of linear order isomorphisms
`ι_A : V_A → V_{A'}` (over a bijection of systems) with `u_{A'} ∘ ι_A = u_A`, compatible with
composition (`ι_{AB} = ι_A ⊗ ι_B` under the composite identifications), mapping allowed channels and
instruments onto allowed ones (`Φ ↦ ι_B Φ ι_A^{-1}`). -/
structure TheoryIso (G G' : Theory) where
  sys : G.C.Sys ≃ G'.C.Sys
  map : (A : G.C.Sys) → Matrix (G'.C.sys (sys A)).ι (G.C.sys A).ι ℝ
  inv : (A : G.C.Sys) → Matrix (G.C.sys A).ι (G'.C.sys (sys A)).ι ℝ
  inv_map : ∀ A, inv A * map A = 1
  map_inv : ∀ A, map A * inv A = 1
  cone_iff : ∀ A (ξ : (G.C.sys A).ι → ℝ), ξ ∈ (G.C.sys A).cone ↔ map A *ᵥ ξ ∈ (G'.C.sys (sys A)).cone
  unit_eq : ∀ A, (G'.C.sys (sys A)).unit ᵥ* map A = (G.C.sys A).unit
  sys_comp : ∀ A B, sys (G.C.comp A B) = G'.C.comp (sys A) (sys B)
  map_comp : ∀ A B (k : (G'.C.sys (G'.C.comp (sys A) (sys B))).ι) (l : (G.C.sys (G.C.comp A B)).ι),
    map (G.C.comp A B) (cast (congrArg (fun S => (G'.C.sys S).ι) (sys_comp A B)).symm k) l =
      map A (G'.C.compEquiv _ _ k).1 (G.C.compEquiv A B l).1 *
        map B (G'.C.compEquiv _ _ k).2 (G.C.compEquiv A B l).2
  chan_iff : ∀ A B (Φ : Matrix (G.C.sys B).ι (G.C.sys A).ι ℝ),
    Φ ∈ G.C.chan A B ↔ map B * Φ * inv A ∈ G'.C.chan (sys A) (sys B)
  inst_iff : ∀ A B k (Φ : Fin k → Matrix (G.C.sys B).ι (G.C.sys A).ι ℝ),
    Φ ∈ G.C.inst A B k ↔ (fun o => map B * Φ o * inv A) ∈ G'.C.inst (sys A) (sys B) k

end GPTIP632.Classical.Supplement

end


