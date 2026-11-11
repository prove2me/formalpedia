-- Prove2me | Definitions.Def_ReLUSynth_Boolean_Synthesis
-- name    : ReLUSynth_Boolean_Synthesis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:09:41.053394+00:00
-- url     : https://prove2.me/theorems/d3efa51c-4e03-47db-8217-e6e7aacee491
-- title:
--   Exact synthesis for a Boolean target supplied by an AND/OR/NOT circuit: instances, binary codes and the language for each inventory rule
-- statement:
--   A **Boolean circuit** has $d\ge1$ input bits, a list of AND, OR and NOT gates in topological order (gate $k$ reads wires $<d+k$; wires $0,\dots,d-1$ are the inputs), and a designated output wire; it computes $C:\{0,1\}^d\to\{0,1\}$. An **instance** $(C,W,n_{\max})$ consists of a circuit, an inventory $W=(w_1,\dots,w_m)$ listed as rational codes (signed integer numerator, positive denominator; list positions distinguish occurrences) with $m\ge1$, and a cap $n_{\max}\ge1$.
--
--   The instance is a **yes instance** under a rule (at-most-once or exactly-once) when some permitted network with input vertices $1,\dots,d$, the occurrences of $W$ under that rule, at most $n_{\max}$ computational vertices and an affine output satisfies
--   $$N(x)=C(x)\qquad\text{for every }x\in\{0,1\}^d,$$
--   an exact equality of real numbers (no rounding, no output threshold). The **synthesis language** for the rule is the set of binary codes of well-formed yes instances; codes are fixed prefix-free binary codes (natural numbers in self-delimiting binary, integers with a sign bit, lists with their length first). A string that is not the code of a well-formed instance is not in the language.
--
--   The module also defines **coNP** (a language whose complement is in NP, with the published `AvgWorstGap.InNP`), circuits computing a **threshold function with positive rational coefficients** ($C(x)=1\iff\sum_t c_tx_t\ge\theta$, all $c_t>0$), and deterministic polynomial-time many-one reductions (the published `ComputesFn` with $u\in L_1\iff f(u)\in L_2$) **with a condition on every image**.
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 9 (§2 encodings); pp. 12–13 (§3); pp. 15–16 (§4)

import Mathlib
import Definitions.Def_AvgWorstGap_IsSigmaPComplete
import Definitions.Def_ReLUSynth_Boolean_Network

namespace ReLUSynth.Boolean

/-! Myrisiotis, *The Complexity of ReLU Network Synthesis from a Parameter Multiset*,
arXiv:2611.04074v1, §2 (p. 9: encodings), §3 (pp. 12–13: languages, reductions), §4 (pp. 15–16:
exact synthesis for a Boolean target supplied by a circuit).

Languages are sets of binary strings (`Set (List Bool)`), as in the published
`AvgWorstGap.InSigmaP` / `AvgWorstGap.IsSigmaPComplete`. -/

/-- Binary code of a natural number: its binary representation (most significant bit first,
`AvgWorstGap.bin`), made self-delimiting by bit doubling and the delimiter `01`
(`AvgWorstGap.selfDelim`). -/
def encNat (n : ℕ) : List Bool := AvgWorstGap.selfDelim (AvgWorstGap.bin n)

/-- Binary code of an integer: a sign bit (`true` for negative) followed by the binary code of
its absolute value. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- Binary code of a list: its length, then the codes of its entries in order. -/
def encList {β : Type} (e : β → List Bool) (l : List β) : List Bool :=
  encNat l.length ++ l.flatMap e

/-- A rational number as supplied in an input (§2, p. 9): a signed integer numerator and a
denominator, which a well-formed input requires to be positive. -/
abbrev RatCode := ℤ × ℕ

/-- The value `num / den` of a rational code. -/
def RatCode.val (c : RatCode) : ℚ := (c.1 : ℚ) / (c.2 : ℚ)

/-- Binary code of a rational code: numerator, then denominator. -/
def encRat (c : RatCode) : List Bool := encInt c.1 ++ encNat c.2

/-- A gate of a Boolean circuit (§4, p. 15), reading wires by number: wires `0, …, d − 1` are
the inputs, and wire `d + k` is the output of gate `k`. -/
inductive Gate where
  | and (a b : ℕ)
  | or (a b : ℕ)
  | not (a : ℕ)

/-- **A Boolean circuit** with `d` input bits and one output bit, and AND, OR, NOT gates
(§4, p. 15): a list of gates in topological order (gate `k` reads only wires `< d + k`) and a
designated output wire `out`. -/
structure Circuit where
  /-- the number of input bits -/
  d : ℕ
  /-- the gates, in topological order -/
  gates : List Gate
  /-- the output wire -/
  out : ℕ

/-- The wires a gate reads. -/
def Gate.args : Gate → List ℕ
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .not a => [a]

/-- The value of a gate given the values of the wires so far (a missing wire reads `false`; this
never happens in a well-formed circuit). -/
def Gate.apply (wires : List Bool) : Gate → Bool
  | .and a b => wires.getD a false && wires.getD b false
  | .or a b => wires.getD a false || wires.getD b false
  | .not a => !(wires.getD a false)

namespace Circuit

/-- A circuit is well formed: it has `d ≥ 1` inputs (§2, p. 9: "Let `d ≥ 1` be an integer, the
input dimension"), gate `k` reads only wires `< d + k` (acyclic, topological order), and the
output wire exists. -/
def WellFormed (C : Circuit) : Prop :=
  1 ≤ C.d ∧ (∀ k : Fin C.gates.length, ∀ a ∈ (C.gates.get k).args, a < C.d + k.val) ∧
    C.out < C.d + C.gates.length

/-- The values of all wires on the input `x`: the inputs, then each gate in order. -/
def wires (C : Circuit) (x : Fin C.d → Bool) : List Bool :=
  C.gates.foldl (fun ws g => ws ++ [g.apply ws]) (List.ofFn x)

/-- The function `C : {0,1}^d → {0,1}` computed by the circuit: the value of the output wire. -/
def eval (C : Circuit) (x : Fin C.d → Bool) : Bool := (C.wires x).getD C.out false

/-- Binary code of a gate: a two-bit tag, then the wire numbers. -/
def encGate : Gate → List Bool
  | .and a b => [false, false] ++ encNat a ++ encNat b
  | .or a b => [false, true] ++ encNat a ++ encNat b
  | .not a => [true, false] ++ encNat a

/-- Binary code of a circuit: `d`, the list of gates, the output wire. -/
def encode (C : Circuit) : List Bool := encNat C.d ++ encList encGate C.gates ++ encNat C.out

/-- `C` computes a threshold function with positive rational coefficients:
`C(x) = 1 ⟺ ∑_t c_t x_t ≥ θ` for some rationals `c_t > 0` and `θ`. -/
def IsPosThreshold (C : Circuit) : Prop :=
  ∃ (c : Fin C.d → ℚ) (θ : ℚ), (∀ t, 0 < c t) ∧
    ∀ x : Fin C.d → Bool, C.eval x = true ↔ θ ≤ ∑ t, c t * (if x t then 1 else 0)

end Circuit

/-- **An instance `(C, W, n_max)` of exact synthesis for a Boolean target supplied by a circuit**
(§4, p. 15): a circuit `C`, the inventory `W = (w_1, …, w_m)` as an explicit list of rational codes
(list positions distinguish occurrences), and the cap `n_max`. -/
structure SynthInstance where
  /-- the target circuit -/
  C : Circuit
  /-- the inventory, one rational code per occurrence -/
  W : List RatCode
  /-- the cap on computational vertices -/
  nmax : ℕ

namespace SynthInstance

/-- Well-formedness (§2, p. 9): a well-formed circuit, `m ≥ 1` occurrences, positive
denominators, and `n_max ≥ 1`. -/
def WellFormed (I : SynthInstance) : Prop :=
  I.C.WellFormed ∧ I.W ≠ [] ∧ (∀ c ∈ I.W, 0 < c.2) ∧ 1 ≤ I.nmax

/-- The real values of the occurrences `1, …, m` of the inventory. -/
noncomputable def invVal (I : SynthInstance) (o : Fin I.W.length) : ℝ :=
  ((I.W.get o).val : ℝ)

/-- **Yes instance** under the rule `rule`, with an affine output (§4, p. 15): some permitted
network (Definition 2.1) with input vertices `1, …, d` (`d` the circuit's input count), using the
occurrences of `W` under `rule` and at most `n_max` computational vertices, satisfies
`N(x) = C(x)` exactly, as real numbers, for every `x ∈ {0,1}^d`. -/
def Yes (rule : InventoryRule) (I : SynthInstance) : Prop :=
  ∃ N : Net (Fin I.C.d) (Fin I.W.length), N.Permitted rule I.nmax ∧
    ∀ x : Fin I.C.d → Bool, N.eval I.invVal (boolVec x) = bitR (I.C.eval x)

/-- Binary code of an instance: circuit, inventory, cap. -/
def encode (I : SynthInstance) : List Bool :=
  I.C.encode ++ encList encRat I.W ++ encNat I.nmax

end SynthInstance

/-- **The language of exact synthesis for a Boolean target supplied by a circuit** under the rule
`rule`, with an affine output: the codes of the well-formed yes instances. A string that is not
the code of a well-formed instance is not in the language. -/
def SynthLang (rule : InventoryRule) : Set (List Bool) :=
  {s | ∃ I : SynthInstance, I.WellFormed ∧ I.Yes rule ∧ s = I.encode}

/-- **coNP** (§4, p. 16: "A problem belongs to coNP if its complement belongs to NP"), with the
published `AvgWorstGap.InNP`. -/
def InCoNP (L : Set (List Bool)) : Prop := AvgWorstGap.InNP Lᶜ

/-- **A deterministic polynomial-time many-one reduction with restricted images**: the published
`AvgWorstGap.ManyOneReduces L₁ L₂` (a function `f` computed by a deterministic machine within a
polynomial time bound, with `u ∈ L₁ ⟺ f u ∈ L₂`), together with the requirement that every input
`u` and its image `f u` satisfy `Good u (f u)`. -/
def ReducesWithImages (L₁ L₂ : Set (List Bool)) (Good : List Bool → List Bool → Prop) : Prop :=
  ∃ (M : NKtLB.Machine) (p : Polynomial ℕ) (f : List Bool → List Bool),
    AvgWorstGap.ComputesFn M p f ∧ (∀ u : List Bool, u ∈ L₁ ↔ f u ∈ L₂) ∧ ∀ u, Good u (f u)

end ReLUSynth.Boolean


