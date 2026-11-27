-- Prove2me | Definitions.Def_ParityDegreeDepth_Core_Setting
-- name    : ParityDegreeDepth_Core_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:18:05.264693+00:00
-- url     : https://prove2.me/theorems/2fd30c63-2f14-4528-8f93-991d2d175881
-- title:
--   Phases, spectral norm, ANF degree, parity decision trees and XOR protocols (public setting of Theorem 1.3)
-- statement:
--   The operational setting of Theorem 1.3 of the source, as public definitions (they reproduce verbatim the private context of the mission statement `ParityDegreeDepth.Main.theorem_1_3`). Vectors are $V_n=\mathbb F_2^n$.
--
--   1. The **phase** of $p:V_n\to\mathbb F_2$ is $f(x)=(-1)^{p(x)}$; its **spectral norm** is $\|\widehat f\|_1=\sum_\xi|\widehat f(\xi)|$ and its **sparsity** is $s(f)=|\{\xi:\widehat f(\xi)\neq0\}|$, with $\widehat f(\xi)=2^{-n}\sum_xf(x)(-1)^{\xi\cdot x}$; $\log_2$ is `logTwo`.
--   2. The **ANF coefficient** $c_S$ and the **ANF degree** $\deg p=\max\{|S|:c_S\neq0\}$ (with $\deg 0=-\infty$).
--   3. A **parity decision tree** is either a leaf with a fixed sign output or a query node labelled by a nonzero $a\in V_n$ with two subtrees, the input $x$ going to the first subtree iff $a\cdot x=0$. Its depth is the longest root-to-leaf path, and $D_\oplus(f)$ (`parityDepth`) is the least depth of a tree computing $f$ exactly.
--   4. $D^{\rm cc}(F)$ (`communicationDepth`) is the least depth of a deterministic two-party protocol (Alice holds $x$, Bob holds $y$) whose output sign equals $f(x+y)$.
--
--   These definitions make the statement of Theorem 1.3 importable and provable on the platform: the mission statement embeds them as `private` declarations, and a `private inductive` from another module cannot be matched by any submitted proof.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §1.1-1.3, §2, Definition A.3 (pp. 1-4, 18)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section
namespace ParityDegreeDepth.Core.Setting


abbrev Vec (n : ℕ) (F : Type) := Fin n → F

def phase {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (x : Vec n (ZMod 2)) : ℝ :=
  (-1 : ℝ) ^ (p x).val

def spectralNorm {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℝ :=
  ∑ a, |QAlgorithms.boolFourier f a|

def sparsity {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  (Finset.univ.filter fun a => QAlgorithms.boolFourier f a ≠ 0).card

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

def coefficient {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  if ParityCubes.anfCoeff (fun x => decide (p (fun i => if x i then 1 else 0) ≠ 0)) S
  then 1 else 0

def anfDegree {n : ℕ} (p : Vec n (ZMod 2) → ZMod 2) : WithBot ℕ :=
  Finset.univ.sup fun S : Finset (Fin n) =>
    if coefficient p S = 0 then ⊥ else (S.card : WithBot ℕ)

inductive ParityTree (n : ℕ) where
  | leaf (b : Bool)
  | query (a : Vec n (ZMod 2)) (ha : a ≠ 0) (zero one : ParityTree n)

def treeDepth {n : ℕ} : ParityTree n → ℕ
  | .leaf _ => 0
  | .query _ _ l r => 1 + max (treeDepth l) (treeDepth r)

def treeEval {n : ℕ} : ParityTree n → Vec n (ZMod 2) → ℝ
  | .leaf b, _ => if b then -1 else 1
  | .query a _ l r, x => if ∑ i, a i * x i = 0 then treeEval l x else treeEval r x

def parityDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : ParityTree n, treeDepth t = k ∧ ∀ x, treeEval t x = f x}

def protocolSign {n : ℕ} (t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)))
    (x y : Vec n (ZMod 2)) : ℝ := if t.eval x y then -1 else 1

def communicationDepth {n : ℕ} (f : Vec n (ZMod 2) → ℝ) : ℕ :=
  sInf {k | ∃ t : DetCCHard.Protocol (Vec n (ZMod 2)) (Vec n (ZMod 2)),
    t.depth = k ∧ ∀ x y, protocolSign t x y = f (x + y)}

end ParityDegreeDepth.Core.Setting


