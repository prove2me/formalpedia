-- Prove2me | Definitions.Def_STCSublinear1377_Main_DataMachine
-- name    : STCSublinear1377_Main_DataMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:33.26206+00:00
-- url     : https://prove2.me/theorems/a13af954-44f3-4b7c-9909-047f13235d4b
-- title:
--   Weighted inputs, self-delimited data and randomized evaluators
-- statement:
--   A data algorithm receives a finite binary description and a polynomial-length fair tape. Integer graphs are described by their active vertices, support and integer edge weights. The unary variant additionally pads by the total edge weight, so a polynomial bound in description length charges the source parameter $n+M$ rather than $n+\log M$.
--
--   $$\Pr(A)=\frac{\#\{s:\operatorname{output}(s)\in A\}}{2^{p(|\operatorname{input}|)}}.$$
--
--   Natural numbers use self-delimited binary frames. A family encoding lists exactly its distinct named regions; order is immaterial and cardinalities and labels are included. These encodings allow a theorem to require a computed family or tree without giving that family or tree to the algorithm as an input certificate.
--
--   **Formalization Note** Integer extraction from real weight fields is used only on inputs separately assumed integral and nonnegative. Each evaluator has the same actual finite-alphabet TM2 requirement as the graph-machine interface.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 1.3, PDF/printed p.3 and Appendix A.2 p.18; Algorithm 1 p.8 and polynomial-time discussion p.15

import Definitions.Def_STCSublinear1377_Main_Machine
import Definitions.Def_STCSublinear1377_Main_Laminar
set_option autoImplicit false

namespace STCSublinear1377.Main

def frame (xs : List Bool) : List Bool := List.replicate xs.length true ++ [false] ++ xs

def natBits (k : ℕ) : List Bool := frame (Computability.encodeNat k)

def setBits {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  (List.finRange n).map (fun v => decide (v ∈ s))

/-- Every ordering is allowed, but the list is duplicate-free and encodes exactly the family. -/
def encodesFamily {n : ℕ} (out : List Bool) (l : NamedFamily n) : Prop :=
  ∃ xs : List (Finset (Fin n) × Fin n), xs.Nodup ∧ xs.toFinset = l ∧
    out = natBits xs.length ++ xs.flatMap (fun r => setBits r.1 ++ natBits r.2.val)

noncomputable def integerGraphBits {n : ℕ} (f : WeightedGraph n) : List Bool :=
  List.replicate n true ++ [false] ++ setBits f.vertices ++ tableBits f.edges ++
    (List.finRange n).flatMap (fun u => (List.finRange n).flatMap (fun v =>
      natBits (Int.toNat ⌊f.weight u v⌋)))

/-- Unary weight padding is used only where the source charges total edge weight. -/
noncomputable def unaryGraphBits {n : ℕ} (f : WeightedGraph n) : List Bool :=
  integerGraphBits f ++ List.replicate (Int.toNat ⌊f.totalWeight⌋) false

structure RandomDataMachine where
  evaluator : BinaryEvaluator
  tapePolynomial : Polynomial ℕ

def RandomDataMachine.tapeLength (a : RandomDataMachine) (input : List Bool) : ℕ :=
  a.tapePolynomial.eval input.length

def RandomDataMachine.output (a : RandomDataMachine) (input : List Bool)
    (tape : Fin (a.tapeLength input) → Bool) : List Bool :=
  a.evaluator.eval (frame input ++ (List.finRange (a.tapeLength input)).map tape)

noncomputable def dataProbability (a : RandomDataMachine) (input : List Bool)
    (event : List Bool → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun tape => event (a.output input tape))).card : ℝ) /
    (2 : ℝ) ^ a.tapeLength input

end STCSublinear1377.Main


