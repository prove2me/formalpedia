-- Prove2me | Definitions.Def_ContiguousCake597_Approximate_Search
-- name    : ContiguousCake597_Approximate_Search
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:27.304615+00:00
-- url     : https://prove2.me/theorems/5d35bb54-dc59-4197-b062-21f937b9da65
-- title:
--   Finite-string cake search relations, binary and unary precision
-- statement:
--   Density lists are length-prefixed and contain self-delimiting binary rational codes. An instance records $n$ and all agents' density lists. Approximate inputs additionally contain positive integers $p,q$ with $\varepsilon=p/q$: both integers are binary in binary mode and unary in unary mode. Unary $m$ is encoded as $m$ ones followed by a zero. Exact mode has no precision suffix and uses $p=0,q=1$ internally. No upper bound on positive $\varepsilon$ is imposed.
--
--   An answer records all $n+1$ rational cuts and the image of each agent under the assignment permutation. For mode $m$ and restriction flag $r$, define the finite-string relation
--   $$\mathcal C_{m,r}(s,t)\iff s\text{ encodes a valid normalized input of the indicated class and }t\text{ encodes a complete }\varepsilon\text{-envy-free allocation}.$$
--   The valid-instance predicate is independent of the answer relation. Every rational-cut answer is allowed, including long representations. Polynomial verification and the existence of a polynomial-size answer are separate conclusions of Lemma 3, rather than assumed fields of the input.
--
--   The module reuses the published search-problem, Cook-machine reduction, End-of-Line and PPAD definitions. Their reductions have uniform polynomial running time in encoded string length and must decode every target answer.
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 4 (PDF 5), §2.1 and Lemma 3

import Definitions.Def_ContiguousCake597_Approximate_Model
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_PPADComplete

namespace ContiguousCake597.Approximate
open QAlgorithms.LocalHamiltonian

/-- Each finite list is prefixed by its length. All rational data use reduced
signed binary numerators and positive binary denominators. -/
def encRats (xs : List ℚ) : List Bool :=
  encBin xs.length ++ xs.flatMap encRat

def encDensity (d : StepDensity) : List Bool := encRats d.knots ++ encRats d.levels

def encCake (D : CakeData) : List Bool :=
  encBin D.n ++ (List.finRange D.n).flatMap fun i => encDensity (D.densities i)

def encAllocation {n : ℕ} (T : Allocation ℚ n) : List Bool :=
  CardinalMatching.encRatVec (n+1) T.cuts ++
    (List.finRange n).flatMap fun i => encBin (T.assign i).val

inductive Precision where
  | exact | binary | unary
  deriving DecidableEq

def encUnary (m : ℕ) : List Bool := List.replicate m true ++ [false]

def Precision.admissible (mode : Precision) (p q : ℕ) : Prop :=
  match mode with
  | .exact => p = 0 ∧ q = 1
  | _ => 0 < p ∧ 0 < q

def encInput (mode : Precision) (D : CakeData) (p q : ℕ) : List Bool :=
  encCake D ++ match mode with
    | .exact => []
    | .binary => encBin p ++ encBin q
    | .unary => encUnary p ++ encUnary q

/-- §2.1: the relation contains every rational-cut answer, without a length
restriction. Short-witness existence and verification are conclusions of Lemma 3. -/
def CakeProblem (mode : Precision) (restricted : Bool) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (D : CakeData) (p q : ℕ), D.Valid ∧
    (restricted = true → D.Restricted) ∧ mode.admissible p q ∧ s = encInput mode D p q
  answer s t := ∃ (D : CakeData) (p q : ℕ) (T : Allocation ℚ D.n), D.Valid ∧
    (restricted = true → D.Restricted) ∧ mode.admissible p q ∧
    s = encInput mode D p q ∧ t = encAllocation T ∧ CakeAnswer D ((p : ℚ) / q) T

end ContiguousCake597.Approximate


