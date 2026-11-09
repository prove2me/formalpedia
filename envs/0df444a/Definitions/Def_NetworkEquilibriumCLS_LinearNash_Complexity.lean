-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
-- name    : NetworkEquilibriumCLS_LinearNash_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:52.759199+00:00
-- url     : https://prove2.me/theorems/989301b5-fd79-4d95-b572-57c94a32b8e6
-- title:
--   The fixed continuous-local-search problem and CLS classification
-- statement:
--   The reference problem is three-dimensional continuous local optimization. Its input gives arithmetic circuits for a potential p:[0,1]^3→[0,1], a move g:[0,1]^3→[0,1]^3, and positive rational ε,L. Gates are explicitly topologically ordered and use rational constants, arithmetic, min, max, and comparison. The number of true multiplications on every ancestor path to an output is at most the binary logarithm of the circuit description size. Outputs are clipped to the cube; adding such clips preserves every canonical instance already having the prescribed range.
--
--   An answer is either a rational cube point satisfying
--
--   $$p(g(x))\ge p(x)-\varepsilon,$$
--
--   or two rational cube points violating the claimed L-Lipschitz bound for p or g, using the maximum norm. Both violation alternatives are present. Gate references and output indices must exist; default values of malformed references are outside the validity predicate.
--
--   TFNP is expressed by totality on valid instances, one uniform polynomial answer bound, and polynomial-time verification of valid instance/answer pairs on Cook's machine. A problem belongs to CLS when it is in TFNP and admits a published polynomial-time search reduction to this fixed canonical problem. Hardness quantifies over every member of that class. No game or quadratic classification is a field or assumption of this definition.
--
--   This is the standard well-behaved circuit formulation, used independently of the target games. Circuit size means encoded bit length. Sharing the four outputs in one DAG and inserting range clips changes no canonical solution or complexity class.
-- source:
--   Daskalakis and Papadimitriou, Continuous Local Search, SODA 2011, §2.1, p.794, https://doi.org/10.1137/1.9781611973082.62; Fearnley, Goldberg, Hollender and Savani, The Complexity of Gradient Descent: CLS = PPAD ∩ PLS, arXiv:2011.01929v4, §3.2, Definition 4, pp.16–17 (PDF 16–17), https://arxiv.org/pdf/2011.01929v4; also the submission §2, p.6 (PDF 7).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Straight-line arithmetic circuit gates of the canonical CLS problem.
References are earlier gate indices. `test` is the comparison gate (1 iff a>b). -/
inductive ArithmeticGate where
  | input : ℕ → ArithmeticGate
  | constant : ℚ → ArithmeticGate
  | add : ℕ → ℕ → ArithmeticGate
  | sub : ℕ → ℕ → ArithmeticGate
  | mul : ℕ → ℕ → ArithmeticGate
  | minimum : ℕ → ℕ → ArithmeticGate
  | maximum : ℕ → ℕ → ArithmeticGate
  | test : ℕ → ℕ → ArithmeticGate
  deriving DecidableEq

def gateCode : ArithmeticGate → List Bool
  | .input i => encNat 0 ++ encNat i
  | .constant r => encNat 1 ++ encRat r
  | .add a b => encNat 2 ++ encNat a ++ encNat b
  | .sub a b => encNat 3 ++ encNat a ++ encNat b
  | .mul a b => encNat 4 ++ encNat a ++ encNat b
  | .minimum a b => encNat 5 ++ encNat a ++ encNat b
  | .maximum a b => encNat 6 ++ encNat a ++ encNat b
  | .test a b => encNat 7 ++ encNat a ++ encNat b

def GateValid (inputs previous : ℕ) : ArithmeticGate → Prop
  | .input i => i < inputs
  | .constant _ => True
  | .add a b | .sub a b | .mul a b | .minimum a b | .maximum a b | .test a b =>
      a < previous ∧ b < previous

def gateEval (x : List ℝ) (prior : List ℝ) : ArithmeticGate → ℝ
  | .input i => x[i]?.getD 0
  | .constant r => r
  | .add a b => prior[a]?.getD 0 + prior[b]?.getD 0
  | .sub a b => prior[a]?.getD 0 - prior[b]?.getD 0
  | .mul a b => prior[a]?.getD 0 * prior[b]?.getD 0
  | .minimum a b => min (prior[a]?.getD 0) (prior[b]?.getD 0)
  | .maximum a b => max (prior[a]?.getD 0) (prior[b]?.getD 0)
  | .test a b => if prior[b]?.getD 0 < prior[a]?.getD 0 then 1 else 0

/-- Flag for a nonliteral gate, and true-multiplication depth on an ancestor path.
Only a rational constant gate is literal: computed constants cannot evade the depth bound. -/
def gateComplexity (prior : List (Bool × ℕ)) : ArithmeticGate → Bool × ℕ
  | .input _ => (true, 0)
  | .constant _ => (false, 0)
  | .add a b | .sub a b | .minimum a b | .maximum a b | .test a b =>
      let u := prior[a]?.getD (false,0)
      let v := prior[b]?.getD (false,0)
      (true, max u.2 v.2)
  | .mul a b =>
      let u := prior[a]?.getD (false,0)
      let v := prior[b]?.getD (false,0)
      (true, max u.2 v.2 + if u.1 && v.1 then 1 else 0)

/-- One shared DAG computes p and the three coordinates of g. Outputs are clipped to [0,1].
This range normal form leaves every in-range canonical instance unchanged. -/
structure CLSInstance where
  gates : List ArithmeticGate
  output : Fin 4 → ℕ
  epsilon : ℚ
  lipschitz : ℚ

def encCLS (C : CLSInstance) : List Bool :=
  encList gateCode C.gates ++ encList encNat (List.ofFn C.output) ++
    encRat C.epsilon ++ encRat C.lipschitz

def CLSInstance.Valid (C : CLSInstance) : Prop :=
  0 < C.epsilon ∧ 0 < C.lipschitz ∧
  (∀ j : Fin C.gates.length, GateValid 3 j.val C.gates[j.val]) ∧
  let complexities := C.gates.foldl (fun prior g => prior ++ [gateComplexity prior g]) []
  ∀ j, C.output j < C.gates.length ∧
    2 ^ (complexities[C.output j]?.getD (false,0)).2 ≤ (encList gateCode C.gates).length

def clip (r : ℝ) : ℝ := max 0 (min 1 r)

def circuitOutputs (C : CLSInstance) (x : Fin 3 → ℝ) (j : Fin 4) : ℝ :=
  let values := C.gates.foldl (fun prior g => prior ++ [gateEval (List.ofFn x) prior g]) []
  clip (values[C.output j]?.getD 0)

def clsPotential (C : CLSInstance) (x : Fin 3 → ℝ) : ℝ := circuitOutputs C x 0

def clsMove (C : CLSInstance) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  circuitOutputs C x ⟨i.val + 1, by omega⟩

def distance3 (x y : Fin 3 → ℝ) : ℝ :=
  max |x 0 - y 0| (max |x 1 - y 1| |x 2 - y 2|)

/-- Canonical 3D-Continuous-Localopt, with both standard Lipschitz-violation witnesses.
Definition 4, FGHS, The Complexity of Gradient Descent, pp.16–17, arXiv:2011.01929. -/
def clsSearch : SearchProblem where
  valid x := ∃ C, C.Valid ∧ encCLS C = x
  answer x y := ∃ C, C.Valid ∧ encCLS C = x ∧
    ((∃ z : Fin 3 → ℚ, y = false :: encVector z ∧ InCube (fun i => (z i : ℝ)) ∧
       clsPotential C (clsMove C (fun i => (z i : ℝ))) ≥
         clsPotential C (fun i => (z i : ℝ)) - C.epsilon) ∨
     (∃ (z w : Fin 3 → ℚ) (which : Bool),
       y = true :: which :: (encVector z ++ encVector w) ∧
       InCube (fun i => (z i : ℝ)) ∧ InCube (fun i => (w i : ℝ)) ∧
       (if which then
         distance3 (clsMove C (fun i => (z i : ℝ))) (clsMove C (fun i => (w i : ℝ)))
       else |clsPotential C (fun i => (z i : ℝ)) - clsPotential C (fun i => (w i : ℝ))|) >
         (C.lipschitz : ℝ) * distance3 (fun i => (z i : ℝ)) (fun i => (w i : ℝ))))

def TotalSearch (S : SearchProblem) : Prop := ∀ x, S.valid x → ∃ y, S.answer x y

/-- The explicit finite-string TFNP conditions, independently of CLS. -/
def InTFNP (S : SearchProblem) : Prop :=
  TotalSearch S ∧
  (∃ k : ℕ, ∀ x y, S.valid x → S.answer x y → y.length ≤ (x.length + 1)^k + k) ∧
  CookPvsNP.checkLang (fun x y => S.valid x ∧ S.answer x y) ∈
    CookPvsNP.P (Option (Bool ⊕ Bool))

/-- The fixed standard class, independent of this paper's games and quadratic objectives. -/
def InCLS (S : SearchProblem) : Prop := InTFNP S ∧ SearchReduces S clsSearch

def CLSHard (S : SearchProblem) : Prop := ∀ R : SearchProblem, InCLS R → SearchReduces R S

def CLSComplete (S : SearchProblem) : Prop := InCLS S ∧ CLSHard S

end NetworkEquilibriumCLS.LinearNash


