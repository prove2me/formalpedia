-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_GrayExtractor
-- name    : AutobiddingGSP_Approximation_GrayExtractor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:36.902685+00:00
-- url     : https://prove2.me/theorems/01673ea8-194d-4f77-a9fd-9bea0bdaba5a
-- title:
--   Gray decoding, pure completions, Pure-Circuit gadgets and the Gray-code extraction properties
-- statement:
--   $D_b(g)=\sum_{j=1}^b2^{b-j}(g_1\oplus\dots\oplus g_j)$ for a pure Gray word. A pure completion of $x\in\{0,1,\bot\}^b$ replaces each $\bot$ by $0$ or $1$ and keeps the pure entries.
--
--   A gadget has vertices, gates, one external input $r$ (output of no gate) and output vertices; every other vertex is the output of exactly one gate. Acyclic: a ranking increasing from inputs to outputs of every gate. `IsGrayExtractor E b`: well formed with $b$ distinct outputs, acyclic, and in every satisfying assignment the output word $g$ has at most one impure entry, any two pure completions decode to integers at distance $\le1$, and if $x[r]=0$ (resp. $1$) every pure completion decodes to $0$ (resp. $2^b-1$).
--
--   `LinearGadgetConstruction E` means that one finite register program constructs every $E_b$ in at most $c b$ elementary word operations. Instructions assign constants, add, compare/branch, emit one basic gate, emit one output vertex, or halt. All registers remain at most $c(b+1)$, so vertex indices use $O(\log(b+1))$ bits. The emitted gate and output streams determine the gadget; no correctness or runtime is assumed as a field.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §6.2, p. 27 (PDF 27); Lemma 6.1, pp. 27–28

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_AutobiddingGSP_Approximation_PureCircuit

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- The decoded integer of a pure Gray word (§6.2, p. 27):
`D_b(g) = ∑_{j=1}^{b} 2^{b−j} (g_1 ⊕ ⋯ ⊕ g_j)`, for `g = (g_1, …, g_b)`. -/
def grayDecode (g : List Bool) : ℕ :=
  ((List.range g.length).map (fun j =>
    if (g.take (j + 1)).foldl xor false then 2 ^ (g.length - 1 - j) else 0)).sum

/-- `g` is a **pure completion** of `x ∈ {0, 1, ⊥}^b` (§6.2, p. 27): it replaces each `⊥` by `0`
or `1` and keeps every pure entry. -/
def IsPureCompletion (x : List Tri) (g : List Bool) : Prop :=
  g.length = x.length ∧ ∀ j (hj : j < x.length) (hg : j < g.length),
    x[j] ≠ Tri.bot → x[j] = (if g[j] then Tri.one else Tri.zero)

/-- A Pure-Circuit gadget: vertices `0, …, n − 1`, its gates, one external input vertex and a list
of output vertices. -/
structure Gadget where
  nV : ℕ
  gates : List PCGate
  input : ℕ
  outs : List ℕ

/-- A gadget with `b` distinct outputs is well formed: every vertex mentioned exists, the outputs of each
gate are distinct, the external input is the output of no gate, and every other vertex is the
output of exactly one gate. -/
def Gadget.WF (E : Gadget) (b : ℕ) : Prop :=
  E.input < E.nV ∧ E.outs.length = b ∧ E.outs.Nodup ∧ (∀ o ∈ E.outs, o < E.nV) ∧
    (∀ g ∈ E.gates, (∀ u ∈ g.inputs, u < E.nV) ∧ (∀ w ∈ g.outputs, w < E.nV) ∧ g.outputs.Nodup) ∧
    ∀ v, v < E.nV →
      (E.gates.filter (fun g => decide (v ∈ g.outputs))).length = if v = E.input then 0 else 1

/-- The gadget is **acyclic**: some ranking of the vertices increases along every gate, from each
input to each output. -/
def Gadget.Acyclic (E : Gadget) : Prop :=
  ∃ rk : ℕ → ℕ, ∀ g ∈ E.gates, ∀ u ∈ g.inputs, ∀ w ∈ g.outputs, rk u < rk w

/-- **The Gray-code extraction properties** of Lemma 6.1 (pp. 27–28) for a gadget
`E_b(r; g_1, …, g_b)`: it is well formed with `b` outputs and acyclic, and in every satisfying
assignment `x` (all gates of the gadget satisfied; the input `r` is arbitrary), the output word
`g = (x[g_1], …, x[g_b])` satisfies

1. at most one entry of `g` is impure;
2. any two pure completions `ĝ, g̃` of `g` have `|D_b(ĝ) − D_b(g̃)| ≤ 1`;
3. if `x[r] = 0` every pure completion decodes to `0`; if `x[r] = 1` every pure completion decodes
   to `2^b − 1`. -/
def Gadget.IsGrayExtractor (E : Gadget) (b : ℕ) : Prop :=
  E.WF b ∧ E.Acyclic ∧
    ∀ x : ℕ → Tri, (∀ g ∈ E.gates, g.Sat x) →
      ((E.outs.map x).count Tri.bot ≤ 1) ∧
      (∀ g₁ g₂ : List Bool, IsPureCompletion (E.outs.map x) g₁ → IsPureCompletion (E.outs.map x) g₂ →
        Nat.dist (grayDecode g₁) (grayDecode g₂) ≤ 1) ∧
      (x E.input = Tri.zero → ∀ g, IsPureCompletion (E.outs.map x) g → grayDecode g = 0) ∧
      (x E.input = Tri.one → ∀ g, IsPureCompletion (E.outs.map x) g → grayDecode g = 2 ^ b - 1)

/-- Binary code of a gadget. -/
def encGadget (E : Gadget) : List Bool :=
  encBin E.nV ++ encBin E.gates.length ++ E.gates.flatMap encPCGate ++ encBin E.input ++
    encBin E.outs.length ++ E.outs.flatMap encBin

/-- Elementary word operations for the linear-time construction in Lemma 6.1 (pp. 27–28).
Register addresses and jump targets are constants in a finite program. `gate` interprets its
vertex arguments as register addresses and emits one basic gate; `output` emits one designated
output vertex. Each instruction costs one word operation. There is no oracle or whole-gadget
instruction. The time predicate below bounds every register by `c * (b + 1)`, so each word has
`O(log(b + 1))` bits, the usual unit-cost convention for constructing a circuit on `O(b)` vertices. -/
inductive GadgetInstr where
  | set (dst value : ℕ)
  | add (dst left right : ℕ)
  | branchLt (left right yes no : ℕ)
  | gate (g : PCGate)
  | output (src : ℕ)
  | halt

/-- Machine configuration, with append-only output streams stored in reverse order. Register 0
initially holds `b`; at termination registers 1 and 2 hold the vertex count and external input. -/
structure GadgetBuildState where
  pc : ℕ := 0
  reg : ℕ → ℕ
  gatesRev : List PCGate := []
  outsRev : List ℕ := []
  halted : Bool := false

/-- One elementary construction operation. A missing instruction halts; no output is implicit. -/
def gadgetBuildStep (program : List GadgetInstr) (s : GadgetBuildState) : GadgetBuildState :=
  if s.halted then s else
  match program[s.pc]? with
  | none | some GadgetInstr.halt => { s with halted := true }
  | some (GadgetInstr.set dst value) =>
      { s with pc := s.pc + 1, reg := Function.update s.reg dst value }
  | some (GadgetInstr.add dst left right) =>
      { s with pc := s.pc + 1, reg := Function.update s.reg dst (s.reg left + s.reg right) }
  | some (GadgetInstr.branchLt left right yes no) =>
      { s with pc := if s.reg left < s.reg right then yes else no }
  | some (GadgetInstr.gate g) =>
      let emitted := match g with
        | PCGate.not u w => PCGate.not (s.reg u) (s.reg w)
        | PCGate.nor u v w => PCGate.nor (s.reg u) (s.reg v) (s.reg w)
        | PCGate.npurify u v w => PCGate.npurify (s.reg u) (s.reg v) (s.reg w)
      { s with pc := s.pc + 1, gatesRev := emitted :: s.gatesRev }
  | some (GadgetInstr.output src) =>
      { s with pc := s.pc + 1, outsRev := s.reg src :: s.outsRev }

/-- Run a fixed construction program for a specified number of elementary operations. -/
def gadgetBuildRun (program : List GadgetInstr) (b steps : ℕ) : GadgetBuildState :=
  (gadgetBuildStep program)^[steps] { reg := fun j => if j = 0 then b else 0 }

/-- The gadget explicitly written by the construction program. Reversing the two output streams
takes linear time in their lengths and therefore preserves the claimed asymptotic bound. -/
def GadgetBuildState.result (s : GadgetBuildState) : Gadget :=
  ⟨s.reg 1, s.gatesRev.reverse, s.reg 2, s.outsRev.reverse⟩

/-- A uniform `O(b)`-time gadget construction: one finite program and one constant work for all
`b ≥ 1`; the program halts within `c*b` word operations, writes exactly `E b`, and uses only
linearly bounded word values throughout. This is a runtime bound, not merely a size bound. -/
def LinearGadgetConstruction (E : ℕ → Gadget) : Prop :=
  ∃ (program : List GadgetInstr) (c : ℕ), 0 < c ∧ ∀ b, 1 ≤ b →
    ∃ steps, steps ≤ c * b ∧ (gadgetBuildRun program b steps).halted = true ∧
      (gadgetBuildRun program b steps).result = E b ∧
      ∀ t, t ≤ steps → ∀ j, (gadgetBuildRun program b t).reg j ≤ c * (b + 1)

end AutobiddingGSP.Approximation


