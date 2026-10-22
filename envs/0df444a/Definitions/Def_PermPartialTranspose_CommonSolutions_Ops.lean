-- Prove2me | Definitions.Def_PermPartialTranspose_CommonSolutions_Ops
-- name    : PermPartialTranspose_CommonSolutions_Ops
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:53.246683+00:00
-- url     : https://prove2.me/theorems/6663edf5-522b-4591-b585-38ccd394fa09
-- title:
--   Permutation, partial transpose, and the braid and Yang–Baxter equations
-- statement:
--   Let $V=\mathbb C^d$, with its standard basis indexed by $1,\ldots,d$. On $V\otimes V$, the permutation operator sends $|ij\rangle$ to $|ji\rangle$. Partial transpose $\Theta_2$ transposes matrix indices in the second factor, and $P_*=\Theta_2(P)$. At $d=2$, write $P^*=\mathbf1-P_*$. The family of interest is
--
--   $$\check R(u)=a\mathbf1+uP+bP_*.$$
--
--   On $V^{\otimes3}$, the subscripts $i$ and $i+1$ place an operator on the first two or the last two factors, respectively. The braid relation is $\check R_i\check R_{i+1}\check R_i=\check R_{i+1}\check R_i\check R_{i+1}$. The multiplicative and additive Yang–Baxter equations are (14) and (15), with $u$ or $x$ varying as the coefficient of $P$ while $a,b$ stay fixed.
--
--   These definitions give one shared matrix model for the goal and its milestones.
--
--   **Formalization Note** The basis is indexed by `Fin d`, and operators on two and three factors are matrices over $\mathbb C$. Tensor placement uses explicit entries. The definition $P_*=\Theta_2(P)$ is retained rather than replacing it with a derived entry formula.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, pp. 5, 8–9, 18, 21–22, §2.1, (3), (14), (15), (54), (63), (69)

import Mathlib

namespace PermPartialTranspose.CommonSolutions

/-- Operators on two copies of ℂ^d. -/
abbrev Op2 (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

/-- Operators on three copies of ℂ^d. -/
abbrev Op3 (d : ℕ) := Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ

/-- The permutation operator P = ∑ᵢⱼ |ij⟩⟨ji|. -/
def swapOp (d : ℕ) : Op2 d :=
  fun r c => if r.1 = c.2 ∧ r.2 = c.1 then 1 else 0

/-- Partial transpose in the second tensor factor. -/
def partialTranspose2 {d : ℕ} (M : Op2 d) : Op2 d :=
  fun r c => M (r.1, c.2) (c.1, r.2)

/-- P_* = Θ₂(P), equation (3). -/
def pStar (d : ℕ) : Op2 d := partialTranspose2 (swapOp d)

/-- P^* = 𝟙 − P_*, equation (63), used at d = 2. -/
def pBar (d : ℕ) : Op2 d := 1 - pStar d

/-- The check-R matrix from equation (69). -/
def Rcheck (d : ℕ) (a u b : ℂ) : Op2 d :=
  a • (1 : Op2 d) + u • swapOp d + b • pStar d

/-- M ⊗ Id, on the first two factors. -/
def onFirst {d : ℕ} (M : Op2 d) : Op3 d :=
  fun r c => M (r.1, r.2.1) (c.1, c.2.1) * (if r.2.2 = c.2.2 then 1 else 0)

/-- Id ⊗ M, on the last two factors. -/
def onLast {d : ℕ} (M : Op2 d) : Op3 d :=
  fun r c => (if r.1 = c.1 then 1 else 0) * M r.2 c.2

/-- The adjacent-generator clause of the braid relation (54). -/
def BraidRel {d : ℕ} (M : Op2 d) : Prop :=
  onFirst M * onLast M * onFirst M = onLast M * onFirst M * onLast M

/-- Multiplicative Yang–Baxter equation (14). -/
def MultiplicativeYBE (d : ℕ) (a b : ℂ) : Prop :=
  ∀ x y : ℂ,
    onFirst (Rcheck d a x b) * onLast (Rcheck d a (x * y) b) * onFirst (Rcheck d a y b) =
      onLast (Rcheck d a y b) * onFirst (Rcheck d a (x * y) b) * onLast (Rcheck d a x b)

/-- Additive Yang–Baxter equation (15). -/
def AdditiveYBE (d : ℕ) (a b : ℂ) : Prop :=
  ∀ u v : ℂ,
    onFirst (Rcheck d a u b) * onLast (Rcheck d a (u + v) b) * onFirst (Rcheck d a v b) =
      onLast (Rcheck d a v b) * onFirst (Rcheck d a (u + v) b) * onLast (Rcheck d a u b)

end PermPartialTranspose.CommonSolutions


