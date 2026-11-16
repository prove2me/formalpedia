-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_PathSuccess
-- name    : InvariantMoneySecurity_Decomposition_Supplement_PathSuccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:31:23.799647+00:00
-- url     : https://prove2.me/theorems/4dc39642-622c-4c3b-a92c-66b9c6219d74
-- title:
--   Success probabilities of a quantum path-finder (Theorem 4.8)
-- statement:
--   A **path-finder** is a uniform quantum polynomial-time algorithm $A$ whose input register holds a pair $(x,y)$ of $n$-bit strings as a computational-basis state and whose output register is measured and decoded as a word (Definition 2.3).
--
--   For a seed $x$ and a target $y$, $\Pr[A(x,y)\text{ outputs a path from }x\text{ to }y]$ is the Born probability, under $A$'s actual output state on input $|x\rangle|y\rangle$, of the set of output strings that decode to a path from $x$ to $y$; it includes $A$'s internal measurements and randomness. Averaging over $y$ uniform on the orbit $C_{k(x)}$ gives
--   $$s_A(x)=\frac{1}{|C_{k(x)}|}\sum_{y\in C_{k(x)}}\Pr[A(x,y)\text{ outputs a path from }x\text{ to }y].$$
--   For a family of seeds $G$, the joint probability with $(p,x)\leftarrow M_n$ (the measured mint output, $x$ uniform on $X_n$) is
--   $$\Pr[x\in G_n\text{ and }A(x,y)\text{ outputs a path from }x\text{ to }y]=\mathbb E_{x\leftarrow X_n}\big[\mathbf 1_{G_n}(x)\,s_A(x)\big].$$
--
--   These are the two success measures in the hypotheses of Theorem 4.8.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 8, Definition 2.2 and Definition 2.3; p. 19, Theorem 4.8

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_Words
import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_OrbitPreparation
import Definitions.Def_InvariantMoneySecurity_Decomposition_MintVerifier
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

attribute [local instance] Classical.propDecidable

/-- A path-finder: a uniform QPT algorithm whose input register holds `(x, y)` as a
computational-basis state on `n + n` qubits and whose `o(n)`-qubit output is measured. -/
abbrev PathFinder (o : ℕ → ℕ) := QPT (fun n => n + n) o

/-- The Born probability, under `A`'s actual output state on input `|x⟩|y⟩`, that measuring the
output register yields a string decoding to a path from `x` to `y`. It includes `A`'s internal
measurements and randomness. -/
def pathProb (D : Scheme) {o : ℕ → ℕ} (A : PathFinder o) (n : ℕ) (x : (D.data n).Object)
    (y : Bits n) : ℝ :=
  born (Matrix.diagonal fun z : Bits (o n) => if OutputsPath D n x y (List.ofFn z) then 1 else 0)
    (A.run n (ketbra (basisVector (appendBits x.val y))))

/-- `Pr_y[A(x, y) outputs a path from x to y]` with `y` uniform on the orbit `C_{k(x)}`. -/
def successProb (D : Scheme) {o : ℕ → ℕ} (A : PathFinder o) (n : ℕ) (x : (D.data n).Object) : ℝ :=
  (((D.data n).orbit x).card : ℝ)⁻¹ * ∑ y ∈ (D.data n).orbit x, pathProb D A n x y

/-- `Pr[x ∈ G_n and A(x, y) outputs a path from x to y]` with `(p, x) ← M_n` (the measured mint
law, `x` uniform on `X_n`) and `y` uniform on `C_{k(x)}`. -/
def seedSuccessProb (D : Scheme) (G : SeedFamily D) {o : ℕ → ℕ} (A : PathFinder o) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun _ x => if x ∈ G n then successProb D A n x else 0

end InvariantMoneySecurity.Decomposition.Supplement


