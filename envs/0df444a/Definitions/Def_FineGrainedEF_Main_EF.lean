-- Prove2me | Definitions.Def_FineGrainedEF_Main_EF
-- name    : FineGrainedEF_Main_EF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:08:18.094547+00:00
-- url     : https://prove2.me/theorems/db207306-7eca-4c8f-b019-d5fbe98c8176
-- title:
--   Extended Frege in circuit form: contexts, gate definitions, small-step inferences, derivation size and the big-step judgement
-- statement:
--   **Contexts.** Extended Frege (EF) is used in the circuit-centred form of §2. A **context** $\Gamma$ is a list of **wires**, named $0,1,2,\dots$ in order of introduction, each either a declared input wire or a **gate definition** $e := g(u_1,\dots,u_k)$ over earlier wires, together with a list of **asserted wires** (supplied assumptions or derived assertions). The gate basis is pinned to $\{\top,\neg,\to\}$ (arities $0,1,2$). A context is **well formed** when every gate has the arity of its type and reads only earlier wires and every asserted wire exists. $\Gamma'$ **extends** $\Gamma$ ($\Gamma'\supseteq\Gamma$) when $\Gamma$'s wire list is a prefix of $\Gamma'$'s and every assertion of $\Gamma$ is an assertion of $\Gamma'$.
--
--   **Proof steps.** One EF step either defines a new gate over existing wires (extension), or appends one assertion by a small-step inference rule of the pinned rule set: the axiom schemes printed on p. 4,
--   $$P\to(Q\to P),\qquad (P\to(Q\to R))\to((P\to Q)\to(P\to R)),\qquad (\neg Q\to\neg P)\to(P\to Q),$$
--   modus ponens $P,\ P\to Q\vdash Q$, and the axiom $\top$ for a constant-true gate. The letters $P,Q,R$ are substituted by wires, and every connective of an axiom instance must be realised by a gate of the context (Figure 1, p. 6); modus ponens needs $p$ and a gate $p\to q$ both asserted. A derivation of $k$ steps has **size** $k=\#\{\text{new gate definitions}\}+\#\{\text{new small-step inferences}\}$, the cost (2) of p. 7.
--
--   **Circuits and the big-step judgement.** A circuit is a generator that appends gate definitions to a context and returns its output wires. For conclusion circuits $\Phi$, the **expanded context** $\Gamma\cup\Phi$ is $\Gamma$ with the gates of $\Phi$ appended. The judgement
--   $$\Gamma\ \triangleright^{S}_{\mathrm{EF}}\ [\varphi_j]_{j<r}$$
--   holds when some derivation of at most $S$ steps from $\Gamma\cup\Phi$ asserts every output of $\Phi$; the gates of $\Phi$ are not charged. $\Gamma$ **contains** a circuit $\Phi$ with outputs $o$ when a mapping of its generated gate names into existing wires fixes its input wires, preserves every operator and input edge, and maps its outputs to $o$; gates may be interleaved with unrelated circuitry and may be shared; a **designated premise** "$\Gamma : R$" is a check circuit contained in $\Gamma$ whose output is asserted.
--
--   **Abstract circuits.** For the arbitrary circuits $C$, $P$ of Lemmas B.4 and B.8 there is a data type of abstract circuits: $n_{\mathrm{in}}$ abstract inputs, a list of gates over earlier abstract wires, and output wires; $|C|$ is the number of gates, and the copy $C(\mathrm{ins})$ instantiates every gate on the actual input wires.
--
--   **Formalization Note.** `Ctx` (`nodes : Array Node`, `asserted : List ℕ`), `EFStep`, `Derives Γ k Γ'`, `Build := StateM (Array Node)`, `Build.expand`, `Build.gates`, `BigStep Γ Φ S`, `WireOutput`, `Contains`, `Asserts`, `Ctx.Extends`, `Ctx.WF`, `Circuit`, `Circuit.apply`. `evalNodes` (Boolean values of all wires under an input assignment) is used only for testing. The rule set is a reading of the paper's unspecified "sound and implicationally complete finite set of rules": the printed Hilbert system plus $\top$.
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 4-8, §2.1-2.2 (rules p. 4, extension (1) p. 5, Figure 1 p. 6, cost (2) p. 7, conventions p. 8), Γ′ ⊇ Γ p. 11

import Mathlib

namespace FineGrainedEF.Main

/-- The pinned gate basis of the circuit-form Extended Frege system: the constant `⊤`
(arity 0), negation `¬` (arity 1) and implication `→` (arity 2). Every other connective the
paper uses (`∧`, `∨`, `↔`, `⊕`, majority) is a fixed sub-circuit over this basis
(`Def_FineGrainedEF_Main_BoolCircuits`). -/
inductive GateOp where
  | top
  | neg
  | imp
  deriving DecidableEq, Repr, Inhabited

/-- Number of input wires of a gate of the given type. -/
def GateOp.arity : GateOp → ℕ
  | .top => 0
  | .neg => 1
  | .imp => 2

/-- Boolean semantics of a gate type (used only by `evalNodes`). -/
def GateOp.eval : GateOp → List Bool → Bool
  | .top, _ => true
  | .neg, [a] => !a
  | .imp, [a, b] => !a || b
  | _, _ => false

/-- A wire of a context: a declared input wire, or the output of a gate whose input wires are
given by their indices. Wires are named by their position in the context. -/
inductive Node where
  | input
  | gate (op : GateOp) (args : List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- An EF context (§2.2): the wires (declared inputs and gate definitions, in order of
introduction; wire `i` is `nodes[i]`) and the list of asserted wires (supplied assumptions or
derived assertions). -/
structure Ctx where
  nodes : Array Node
  asserted : List ℕ

/-- A well-formed context: every gate has the arity of its type and reads only earlier wires,
and every asserted wire exists. -/
def Ctx.WF (Γ : Ctx) : Prop :=
  (∀ (i : ℕ) (h : i < Γ.nodes.size) (op : GateOp) (args : List ℕ),
      Γ.nodes[i] = Node.gate op args → args.length = op.arity ∧ ∀ a ∈ args, a < i) ∧
    ∀ w ∈ Γ.asserted, w < Γ.nodes.size

/-- All the listed wires exist in `Γ`. -/
def Ctx.HasWires (Γ : Ctx) (ws : List ℕ) : Prop := ∀ w ∈ ws, w < Γ.nodes.size

/-- `Γ'` extends `Γ` (`Γ' ⊇ Γ`, p. 11): it keeps every wire of `Γ` under the same name and
every assertion of `Γ`, possibly with further wires and assertions. -/
def Ctx.Extends (Γ' Γ : Ctx) : Prop :=
  Γ.nodes.toList <+: Γ'.nodes.toList ∧ ∀ w ∈ Γ.asserted, w ∈ Γ'.asserted

/-- Wire `w` is an implication gate `a → b`. -/
def Ctx.IsImp (Γ : Ctx) (w a b : ℕ) : Prop := Γ.nodes[w]? = some (Node.gate .imp [a, b])

/-- Wire `w` is a negation gate `¬a`. -/
def Ctx.IsNeg (Γ : Ctx) (w a : ℕ) : Prop := Γ.nodes[w]? = some (Node.gate .neg [a])

/-- Wire `w` is a constant-true gate. -/
def Ctx.IsTop (Γ : Ctx) (w : ℕ) : Prop := Γ.nodes[w]? = some (Node.gate .top [])

/-- Wire `w` is an instance of AX1, `P → (Q → P)`, with the letters substituted by wires and
both connectives realised by gates of the context (Figure 1). -/
def Ctx.Ax1 (Γ : Ctx) (w : ℕ) : Prop :=
  ∃ P Q a : ℕ, Γ.IsImp w P a ∧ Γ.IsImp a Q P

/-- Wire `w` is an instance of AX2, `(P → (Q → R)) → ((P → Q) → (P → R))`. -/
def Ctx.Ax2 (Γ : Ctx) (w : ℕ) : Prop :=
  ∃ P Q R x y u d e : ℕ, Γ.IsImp w x y ∧ Γ.IsImp x P u ∧ Γ.IsImp u Q R ∧
    Γ.IsImp y d e ∧ Γ.IsImp d P Q ∧ Γ.IsImp e P R

/-- Wire `w` is an instance of AX3, `(¬Q → ¬P) → (P → Q)`. -/
def Ctx.Ax3 (Γ : Ctx) (w : ℕ) : Prop :=
  ∃ P Q x y nq np : ℕ, Γ.IsImp w x y ∧ Γ.IsImp x nq np ∧ Γ.IsNeg nq Q ∧ Γ.IsNeg np P ∧
    Γ.IsImp y P Q

/-- Append an assertion. -/
def Ctx.assert (Γ : Ctx) (w : ℕ) : Ctx := { Γ with asserted := Γ.asserted ++ [w] }

/-- Append a gate definition (a fresh wire, named `Γ.nodes.size`). -/
def Ctx.addGate (Γ : Ctx) (op : GateOp) (args : List ℕ) : Ctx :=
  { Γ with nodes := Γ.nodes.push (Node.gate op args) }

/-- One EF proof step (§2.2, "Overview of the proof growth process"): either define a new gate
over existing wires (extension), or append one assertion by a small-step inference rule of the
pinned rule set: the axiom schemes AX1–AX3 and modus ponens printed on p. 4 (letters substituted by
wires only, footnote 2), plus the axiom `⊤` for a constant-true gate. -/
inductive EFStep : Ctx → Ctx → Prop
  | gate (Γ : Ctx) (op : GateOp) (args : List ℕ) (harity : args.length = op.arity)
      (hargs : ∀ a ∈ args, a < Γ.nodes.size) : EFStep Γ (Γ.addGate op args)
  | ax1 (Γ : Ctx) (w : ℕ) (h : Γ.Ax1 w) : EFStep Γ (Γ.assert w)
  | ax2 (Γ : Ctx) (w : ℕ) (h : Γ.Ax2 w) : EFStep Γ (Γ.assert w)
  | ax3 (Γ : Ctx) (w : ℕ) (h : Γ.Ax3 w) : EFStep Γ (Γ.assert w)
  | top (Γ : Ctx) (w : ℕ) (h : Γ.IsTop w) : EFStep Γ (Γ.assert w)
  | mp (Γ : Ctx) (p pq q : ℕ) (hp : p ∈ Γ.asserted) (hpq : pq ∈ Γ.asserted)
      (h : Γ.IsImp pq p q) : EFStep Γ (Γ.assert q)

/-- `Derives Γ k Γ'`: a sequence of exactly `k` EF steps leads from `Γ` to `Γ'`. The cost (2),
p. 7, `#{new gate definitions} + #{new small-step inferences}`, is `k`. -/
inductive Derives : Ctx → ℕ → Ctx → Prop
  | refl (Γ : Ctx) : Derives Γ 0 Γ
  | step {Γ Γ₁ Γ₂ : Ctx} {k : ℕ} : EFStep Γ Γ₁ → Derives Γ₁ k Γ₂ → Derives Γ (k + 1) Γ₂

/-- A circuit generator: a program that appends gate definitions to the wire list of a context
and returns some of the wires it names. Every circuit of the paper is such a program applied to
the wires of its inputs. -/
abbrev Build := StateM (Array Node)

/-- Append one gate and return its output wire. -/
def Build.gate (op : GateOp) (args : List ℕ) : Build ℕ :=
  modifyGet fun ns => (ns.size, ns.push (Node.gate op args))

/-- Run a generator on top of the wires `ns`. -/
def Build.exec {α : Type} (Φ : Build α) (ns : Array Node) : α × Array Node :=
  Id.run (Φ.run ns)

/-- The expanded context `Γ ∪ Φ` (§2.2): `Γ` with the gates of the conclusion circuits appended,
and the conclusion outputs. -/
def Build.expand {α : Type} (Φ : Build α) (Γ : Ctx) : α × Ctx :=
  let r := Φ.exec Γ.nodes
  (r.1, { Γ with nodes := r.2 })

/-- Number of gates `Φ` appends to `Γ`. -/
def Build.gates {α : Type} (Φ : Build α) (Γ : Ctx) : ℕ :=
  (Φ.exec Γ.nodes).2.size - Γ.nodes.size

/-- The big-step judgement `Γ ▷^S_EF [φ_j]_j` (§2.2, (2)): starting from the expanded context
`Γ ∪ Φ`, at most `S` EF steps (gate definitions plus small-step inferences) produce a context in
which every conclusion output is asserted. The gates of `Φ` itself are not charged. Designated
premises `R` are stated as hypotheses `Asserts Γ _` beside the judgement. -/
def BigStep (Γ : Ctx) (Φ : Build (List ℕ)) (S : ℕ) : Prop :=
  ∃ (k : ℕ) (Γ' : Ctx), k ≤ S ∧ Derives (Φ.expand Γ).2 k Γ' ∧
    ∀ o ∈ (Φ.expand Γ).1, o ∈ Γ'.asserted

/-- Renaming the wire names in a circuit's output interface. Instances cover a wire,
words, arrays, and the pair of bits and carries returned by `carry`. -/
class WireOutput (α : Type) where
  rename : (ℕ → ℕ) → α → α

instance : WireOutput ℕ where
  rename ρ w := ρ w

instance {α : Type} [WireOutput α] : WireOutput (List α) where
  rename ρ xs := xs.map (WireOutput.rename ρ)

instance {α β : Type} [WireOutput α] [WireOutput β] : WireOutput (α × β) where
  rename ρ x := (WireOutput.rename ρ x.1, WireOutput.rename ρ x.2)

/-- `Γ` contains a copy of `Φ` with outputs `out`. Generate fresh template gates above
`Γ.nodes`, then map those gates into `Γ`, preserving each gate operator and every input edge.
Existing input wires are fixed. Gates may be interleaved with unrelated circuitry, and identical
gates may be shared, as in §2.2. This is structural containment, not semantic equivalence. -/
def Contains {α : Type} [WireOutput α] (Γ : Ctx) (Φ : Build α) (out : α) : Prop :=
  let r := Φ.exec Γ.nodes
  ∃ ρ : ℕ → ℕ,
    (∀ i < Γ.nodes.size, ρ i = i) ∧
    (∀ i, Γ.nodes.size ≤ i → i < r.2.size →
      ∃ op args, r.2[i]? = some (Node.gate op args) ∧
        Γ.nodes[ρ i]? = some (Node.gate op (args.map ρ))) ∧
    WireOutput.rename ρ r.1 = out

/-- A designated premise: `Γ` contains the check circuit `P` and asserts its output. -/
def Asserts (Γ : Ctx) (P : Build ℕ) : Prop :=
  ∃ o : ℕ, Contains Γ P o ∧ o ∈ Γ.asserted

/-- An abstract Boolean circuit over the pinned basis, used for the arbitrary circuits `C`, `P`
of Lemmas B.4 and B.8: `nIn` abstract inputs `0, …, nIn - 1`; gate `g` defines abstract wire
`nIn + g` and reads abstract wires; `outs` lists the output wires. -/
structure Circuit where
  nIn : ℕ
  gates : List (GateOp × List ℕ)
  outs : List ℕ

/-- Well-formed abstract circuit: correct arities, every gate reads earlier abstract wires,
outputs exist. -/
def Circuit.WF (C : Circuit) : Prop :=
  (∀ (i : ℕ) (h : i < C.gates.length),
      (C.gates[i]).2.length = (C.gates[i]).1.arity ∧ ∀ a ∈ (C.gates[i]).2, a < C.nIn + i) ∧
    ∀ o ∈ C.outs, o < C.nIn + C.gates.length

/-- `|C|`, the number of gates. -/
def Circuit.size (C : Circuit) : ℕ := C.gates.length

/-- The copy of `C` applied to the actual input wires `ins` (abstract input `i` ↦ `ins[i]`): its
gates are appended in order, and the actual output wires are returned. -/
def Circuit.apply (C : Circuit) (ins : List ℕ) : Build (List ℕ) := do
  let mut env : Array ℕ := ins.toArray
  for g in C.gates do
    let w ← Build.gate g.1 (g.2.map fun a => env.getD a 0)
    env := env.push w
  return C.outs.map fun o => env.getD o 0

/-- Boolean values of all wires under an assignment `inp` to the input wires (input wire `i`
takes `inp i`). Not used by any statement; used to test the circuits. -/
def evalNodes (ns : Array Node) (inp : ℕ → Bool) : Array Bool :=
  ns.foldl (init := #[]) fun vals nd =>
    match nd with
    | .input => vals.push (inp vals.size)
    | .gate op args => vals.push (op.eval (args.map fun a => vals.getD a false))

end FineGrainedEF.Main


