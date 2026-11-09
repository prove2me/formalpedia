-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Model
-- name    : CompressedOracleDuality_LabelSymmetric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:36.42155+00:00
-- url     : https://prove2.me/theorems/17cddefc-8cb8-4337-8af2-e06e3ee85f72
-- title:
--   Query-algorithm label symmetry and average collision success
-- statement:
--   Let $N=2^n$. Inputs are integers $0,\ldots,N-1$, labels are $n$-bit strings, and a memory basis element is $((x,y),w)$ for a workspace basis $W$. An output is either failure or a triple $(x_1,x_2,y)$. It is successful on $H$ precisely when $x_1<x_2$ and $H(x_1)=H(x_2)=y$.
--
--   A unitary query algorithm $A$ is label-symmetric when, for every time $0\le t\le T$, every pair of functions $H_1,H_2$, and every permutation $\sigma$ of all $N$ labels,
--   $$\langle\psi_t^{H_1}|\psi_t^{H_2}\rangle=\langle\psi_t^{\sigma\circ H_1}|\psi_t^{\sigma\circ H_2}\rangle.$$
--   Its collision success is the uniform average over all $N^N$ functions of the final computational-basis measurement probability of a successful reported triple. This definition fixes the actual algorithmic task independently of all compressed-oracle progress bounds.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, pp. 11–12, (14)–(16); p. 20, Definition 4.1 and Theorem 4.2

import Definitions.Def_QAlgorithms_Defs_Query

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

/-- §§2.2 and 4: input basis, label basis, memory basis, and reported collision. -/
abbrev Input (n : ℕ) := Fin (2 ^ n)
abbrev Label (n : ℕ) := Qubits n
abbrev Memory (n : ℕ) (W : Type) := (Input n × Label n) × W
abbrev CollisionOutput (n : ℕ) := Option (Input n × Input n × Label n)

/-- Definition 4.1, (51): invariance of overlaps at every time, including 0 and T. -/
def IsLabelSymmetric {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) : Prop :=
  ∀ (t : Fin (T + 1)) (H₁ H₂ : Input n → Label n) (σ : Equiv.Perm (Label n)),
    inner ℂ (A.stateAt (xorOracle H₁) t) (A.stateAt (xorOracle H₂) t) =
    inner ℂ (A.stateAt (xorOracle (σ ∘ H₁)) t) (A.stateAt (xorOracle (σ ∘ H₂)) t)

/-- Theorem 4.2: an output reports ordered distinct inputs and their common label. -/
def Successful {n : ℕ} (H : Input n → Label n) : CollisionOutput n → Prop
  | none => False
  | some (x₁, x₂, y) => x₁ < x₂ ∧ H x₁ = y ∧ H x₂ = y

/-- Success averaged uniformly over all N^N oracles and the final measurement. -/
def collisionSuccess {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n) : ℝ :=
  open Classical in
  (Fintype.card (Input n → Label n) : ℝ)⁻¹ *
    ∑ H : Input n → Label n,
      probEvent (A.finalState (xorOracle H)) (fun z => Successful H (out z))

end CompressedOracleDuality.LabelSymmetric


