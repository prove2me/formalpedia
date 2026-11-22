-- Prove2me | Definitions.Def_DistLTLSynth_Char_SynthesisEngine
-- name    : DistLTLSynth_Char_SynthesisEngine
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T09:09:02.886379+00:00
-- url     : https://prove2.me/theorems/2186ab70-729b-4b3b-92f1-d74dda819e4c
-- title:
--   Finite Automaton and Symbolic Tree Codes for Distributed LTL Synthesis
-- statement:
--   Finite code representations and semantic decoders supporting the decidability and algorithm-synthesis procedure for distributed LTL synthesis under message adversaries with nowhere-dense geometric image ($\pi(A)$ nowhere dense, Theorem 3.4).
--
--   1. **Automaton codes (`GenDPACode`, `NBWCode`, `ListNBWCode`):** Finite tuple encodings of deterministic parity automata (`toGenDPA`) and nondeterministic B\u00fcchi automata (`NBWAccepts`, `ListNBWAccepts`) over finite indexed alphabets $\mathrm{Fin}(\alpha + 1)$, used to compile LTL specifications, adversary complements, and bounded edge-thread monitors.
--   2. **Parity tree specifications (`TreeSpecCode`, `ValidAcceptingTree`):** Finite descriptions of $(b + 1)$-branching labeled tree languages over $\mathrm{Fin}(A + 1)$ equipped with root admissibility `tsRootOk`, parent-direction-child compatibility `tsChildOk`, and a deterministic parity branch monitor `tsDPA` capturing symbolic compressed component trees.
--   3. **Typed instance formula interpretation (`instFormulaOf`):** Maps an arithmetic-indexed LTL formula $\varphi \in \mathrm{Formula}(\mathbb{N},\mathbb{N},\mathbb{N},\mathbb{N})$ onto the finite alphabets $X_1, X_2, Y_1, Y_2$ of an `Instance`, sending out-of-range atomic indices to $\bot$.
--
--   **Formalization Note** All code types are concrete products of natural numbers and lists so that `Primcodable` instances synthesize automatically in Lean 4 without custom Gödel-numbering boilerplate.
-- source:
--   arXiv:2611.04561, Distributed LTL Synthesis under Arbitrary Message Adversaries, Section 3.3 (Lemmas 3.7, 3.12, 3.13, pp. 13-16) and Section 7 (Definition 7.6)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree

set_option autoImplicit false

namespace DistLTLSynth.Char

/-- Finite description of a deterministic parity automaton over `Fin (αSize + 1)`:
`(maxState, trans, prios)` describes the automaton with state space `Fin (d.1 + 1)`,
initial state `0`, transition `step s a = trans[s * (αSize + 1) + a] mod (d.1 + 1)`,
and priority `prio s = prios[s]` (missing entries default to `0`). -/
abbrev GenDPACode : Type := ℕ × List ℕ × List ℕ

/-- Semantic deterministic parity automaton over `Fin (αSize + 1)` decoded from `d`. -/
def toGenDPA (αSize : ℕ) (d : GenDPACode) : DPA (Fin (d.1 + 1)) (Fin (αSize + 1)) where
  init := ⟨0, Nat.succ_pos _⟩
  step s a := ⟨(d.2.1.getD (s.val * (αSize + 1) + a.val) 0) % (d.1 + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩
  prio s := d.2.2.getD s.val 0

/-- Bitmask-based description of a nondeterministic Büchi automaton over `Fin (αSize + 1)`:
`(maxState, initMask, transMasks, accMask)` over state space `Fin (b.1 + 1)`. -/
abbrev NBWCode : Type := ℕ × ℕ × List ℕ × ℕ

/-- Acceptance of an infinite word `w : ℕ → Fin (αSize + 1)` by a bitmask-encoded `NBWCode`. -/
def NBWAccepts (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)) : Prop :=
  ∃ ρ : ℕ → Fin (b.1 + 1),
    Nat.testBit b.2.1 (ρ 0).val = true ∧
    (∀ n, Nat.testBit (b.2.2.1.getD ((ρ n).val * (αSize + 1) + (w n).val) 0)
      (ρ (n + 1)).val = true) ∧
    ∃ᶠ n in Filter.atTop, Nat.testBit b.2.2.2 (ρ n).val = true

/-- List-based description of a nondeterministic Büchi automaton over `Fin (αSize + 1)`:
`(maxState, initList, transRows, accList)` over state space `Fin (B.1 + 1)`. -/
abbrev ListNBWCode : Type := ℕ × List ℕ × List (List ℕ) × List ℕ

/-- Acceptance of an infinite word `w : ℕ → Fin (αSize + 1)` by a `ListNBWCode`. -/
def ListNBWAccepts (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) : Prop :=
  ∃ ρ : ℕ → Fin (B.1 + 1),
    (ρ 0).val ∈ B.2.1 ∧
    (∀ n, (ρ (n + 1)).val ∈ B.2.2.1.getD ((αSize + 1) * (ρ n).val + (w n).val) []) ∧
    ∃ q : Fin (B.1 + 1), q.val ∈ B.2.2.2 ∧ ∃ᶠ n in Filter.atTop, ρ n = q

/-- Finite specification `(b, A, rootOk, childOk, mN, mTrans, mPrios)` of a `(b + 1)`-branching
labeled tree language over alphabet `Fin (A + 1)` with a deterministic parity branch monitor
over state space `Fin (mN + 1)` (§3.3, Lemma 3.13). -/
abbrev TreeSpecCode : Type := ℕ × ℕ × List Bool × List Bool × ℕ × List ℕ × List ℕ

/-- Root admissibility predicate of a `TreeSpecCode`. -/
def tsRootOk (ts : TreeSpecCode) (a : Fin (ts.2.1 + 1)) : Bool :=
  ts.2.2.1.getD a.val false

/-- Local parent-direction-child compatibility predicate of a `TreeSpecCode`. -/
def tsChildOk (ts : TreeSpecCode) (a : Fin (ts.2.1 + 1)) (d : Fin (ts.1 + 1))
    (a' : Fin (ts.2.1 + 1)) : Bool :=
  ts.2.2.2.1.getD ((a.val * (ts.1 + 1) + d.val) * (ts.2.1 + 1) + a'.val) false

/-- Deterministic parity branch monitor decoded from a `TreeSpecCode`. -/
def tsDPA (ts : TreeSpecCode) :
    DPA (Fin (ts.2.2.2.2.1 + 1)) (Fin (ts.2.1 + 1) × Fin (ts.1 + 1)) where
  init := ⟨0, Nat.succ_pos _⟩
  step q ad :=
    ⟨(ts.2.2.2.2.2.1.getD ((q.val * (ts.2.1 + 1) + ad.1.val) * (ts.1 + 1) + ad.2.val) 0) %
        (ts.2.2.2.2.1 + 1),
      Nat.mod_lt _ (Nat.succ_pos _)⟩
  prio q := ts.2.2.2.2.2.2.getD q.val 0

/-- A `(b + 1)`-branching tree `t` satisfies the root, local child, and branch-parity conditions
specified by `ts`. -/
def ValidAcceptingTree (ts : TreeSpecCode)
    (t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1)) : Prop :=
  tsRootOk ts (t []) = true ∧
    (∀ (addr : List (Fin (ts.1 + 1))) (d : Fin (ts.1 + 1)),
      tsChildOk ts (t addr) d (t (addr ++ [d])) = true) ∧
    (∀ branch : ℕ → Fin (ts.1 + 1),
      (tsDPA ts).Accepts
        (fun n => (t (List.ofFn (fun i : Fin n => branch i.val)), branch n)))

/-- Interpretation of an arithmetic-indexed formula `Formula ℕ ℕ ℕ ℕ` over the finite `Fin`
alphabets of an `Instance`, mapping out-of-range atomic indices to `Formula.ff`. -/
def instFormulaOf (I : Instance) : Formula ℕ ℕ ℕ ℕ → Formula I.X1 I.X2 I.Y1 I.Y2
  | .inp1 x => if h : x < I.k1 + 1 then .inp1 ⟨x, h⟩ else .ff
  | .inp2 x => if h : x < I.k2 + 1 then .inp2 ⟨x, h⟩ else .ff
  | .out1 y => if h : y < I.m1 + 1 then .out1 ⟨y, h⟩ else .ff
  | .out2 y => if h : y < I.m2 + 1 then .out2 ⟨y, h⟩ else .ff
  | .graph g => .graph g
  | .next φ => .next (instFormulaOf I φ)
  | .eventually φ => .eventually (instFormulaOf I φ)
  | .always φ => .always (instFormulaOf I φ)
  | .untl φ ψ => .untl (instFormulaOf I φ) (instFormulaOf I ψ)
  | .weakUntil ψ φ => .weakUntil (instFormulaOf I ψ) (instFormulaOf I φ)
  | .neg φ => .neg (instFormulaOf I φ)
  | .or φ ψ => .or (instFormulaOf I φ) (instFormulaOf I ψ)
  | .and φ ψ => .and (instFormulaOf I φ) (instFormulaOf I ψ)
  | .imp φ ψ => .imp (instFormulaOf I φ) (instFormulaOf I ψ)
  | .iff φ ψ => .iff (instFormulaOf I φ) (instFormulaOf I ψ)

end DistLTLSynth.Char


