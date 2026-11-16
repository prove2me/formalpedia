-- Prove2me | Definitions.Def_MetricSelfDualCompletion_Completion_Supplement_Metrics
-- name    : MetricSelfDualCompletion_Completion_Supplement_Metrics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:43.647542+00:00
-- url     : https://prove2.me/theorems/5fd1db99-4bbc-4c20-b9bb-0800e1875c05
-- title:
--   CSS and graph-state metrics; systematic graphs and code types
-- statement:
--   Let $V_n=\mathbb F_2^n$ and let a binary code be an arbitrary linear subspace of $V_n$. The published dual, minimum distance, row-basis convention and matrix encoding are reused. For vectors $x,z\in V_n$ put
--   $$\operatorname{swt}(x,z)=|\operatorname{supp}(x)\cup\operatorname{supp}(z)|.$$
--   For a self-orthogonal check space $B$, the identical-check CSS stabilizer is $B\times B$, its symplectic orthogonal space is $B^\perp\times B^\perp$, and the logical-qubit count is $n-2\dim B$. Its logical distance is the minimum symplectic weight on $(B^\perp\times B^\perp)\setminus(B\times B)$; its nonzero stabilizer distance is the minimum on $(B\times B)\setminus\{(0,0)\}$. Both minima have value $+\infty$ when empty. Logical-distance applications require a positive logical-qubit count.
--
--   For a symmetric zero-diagonal binary adjacency matrix $\Gamma$, define
--   $$d(\Gamma)=\min_{x\ne0}\operatorname{swt}(x,\Gamma x).$$
--   A bipartition is a Boolean labeling whose same-part adjacency entries vanish; balanced means the two parts have equal size. No connectedness, regularity or sparsity is required. The systematic code is the kernel of $[I_a\mid R]$; its graph has adjacency $\left[\begin{smallmatrix}0&R\\R^\top&0\end{smallmatrix}\right]$ in that coordinate order. A coordinate permutation moves coordinate $i$ to coordinate $e(i)$.
--
--   A code is doubly even when all word weights are divisible by four; Type II means self-dual and doubly even, while Type I means self-dual and not doubly even. These definitions separate logical distance from graph-state stabilizer distance and support all nine new results.
--
--   **Formalization Note** Vectors use `Fin n → ZMod 2`. The zero code and full space are retained. Natural subtraction in the logical-qubit count is used only with self-orthogonality, which ensures $2\dim B\le n$. Empty minima use $\mathbb N_\infty$.
-- source:
--   Rafail Ostrovsky, STOC 2027 submission #5 (October 2026), §§2.1–2.3, equations (2)–(5), Lemma 6, printed p. 5–6 (PDF p. 7–8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/5.pdf

import Mathlib
import Definitions.Def_MetricSelfDualCompletion_Completion_Codes
import Definitions.Def_MetricSelfDualCompletion_Completion_Encoding

namespace MetricSelfDualCompletion.Completion.Supplement

open QAlgorithms

/-- Binary vectors and codes use the published submodule representation, with no rank promise. -/
abbrev V (n : ℕ) := Fin n → ZMod 2
abbrev Code (n : ℕ) := Submodule (ZMod 2) (V n)
/-- §2.2, equation (2): union, not sum, of supports. -/
def swt {n : ℕ} (x z : V n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card
/-- §2.2: S=B×B and S^⊥s=B^⊥×B^⊥; infinity if there is no logical label. -/
noncomputable def cssDistance {n : ℕ} (B : Code n) : ℕ∞ :=
  ⨅ (x : V n) (z : V n) (_ : x ∈ codeDual B ∧ z ∈ codeDual B)
    (_ : x ∉ B ∨ z ∉ B), (swt x z : ℕ∞)
noncomputable def stabilizerDistance {n : ℕ} (B : Code n) : ℕ∞ :=
  ⨅ (x : V n) (z : V n) (_ : x ∈ B ∧ z ∈ B) (_ : x ≠ 0 ∨ z ≠ 0),
    (swt x z : ℕ∞)
noncomputable def logicalQubits {n : ℕ} (B : Code n) : ℕ :=
  n - 2 * Module.finrank (ZMod 2) B
/-- A binary symmetric zero-diagonal adjacency is exactly a finite simple unweighted graph. -/
def IsSimple {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  G.IsSymm ∧ ∀ i, G i i = 0
/-- An explicit bipartition; the balance condition is equality of the part sizes. -/
def IsBipartite {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∃ b : Fin n → Bool, ∀ i j, b i = b j → G i j = 0
def IsBalancedBipartite {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∃ b : Fin n → Bool,
    (Finset.univ.filter fun i => b i = true).card =
      (Finset.univ.filter fun i => b i = false).card ∧
    ∀ i j, b i = b j → G i j = 0
/-- §2.3, equation (5), with the empty minimum equal to infinity. -/
noncomputable def graphDistance {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ∞ :=
  ⨅ (x : V n) (_ : x ≠ 0), (swt x (G.mulVec x) : ℕ∞)
/-- Blocks in the systematic parity-check coordinate order. -/
def blockGraph {a b : ℕ} (R : Matrix (Fin a) (Fin b) (ZMod 2)) :
    Matrix (Fin (a+b)) (Fin (a+b)) (ZMod 2) := fun i j =>
  if hi : i.val < a then
    if hj : j.val < a then 0 else R ⟨i.val, hi⟩ ⟨j.val-a, by omega⟩
  else if hj : j.val < a then R ⟨j.val, hj⟩ ⟨i.val-a, by omega⟩ else 0
/-- Kernel of [I_a | R], in exactly the same coordinate order as blockGraph. -/
def systematicCode {a b : ℕ} (R : Matrix (Fin a) (Fin b) (ZMod 2)) : Code (a+b) :=
  LinearMap.ker (Matrix.mulVecLin (fun (i : Fin a) (j : Fin (a+b)) =>
    if hj : j.val < a then (if i.val = j.val then 1 else 0)
    else R i ⟨j.val-a, by omega⟩))
/-- Coordinate permutation sends x_i to coordinate e(i). -/
def permute (n : ℕ) (e : Equiv.Perm (Fin n)) : V n →ₗ[ZMod 2] V n where
  toFun x i := x (e.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- §2.1 / Appendix A: doubly even, Type II, and genuinely Type I. -/
def DoublyEven {n : ℕ} (A : Code n) : Prop := ∀ x ∈ A, 4 ∣ hammingNorm x
def TypeII {n : ℕ} (A : Code n) : Prop := IsSelfDual A ∧ DoublyEven A
def TypeI {n : ℕ} (A : Code n) : Prop := IsSelfDual A ∧ ¬ DoublyEven A

end MetricSelfDualCompletion.Completion.Supplement


