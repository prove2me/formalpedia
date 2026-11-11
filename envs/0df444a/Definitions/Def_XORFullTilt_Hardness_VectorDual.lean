-- Prove2me | Definitions.Def_XORFullTilt_Hardness_VectorDual
-- name    : XORFullTilt_Hardness_VectorDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:38.205166+00:00
-- url     : https://prove2.me/theorems/94e0263c-8495-4b05-92bf-7a2010beae0f
-- title:
--   Vector correlations, bias and the XOR dual SDP
-- statement:
--   The game matrix is $H_{x,y}=(-1)^{f(x,y)}\pi(x,y)$. A vector correlation is specified by real unit vectors $u_x,v_y$ in a common finite Euclidean space, with
--   $$\beta(G,C)=\sum_{x,y}H_{x,y}\langle u_x,v_y\rangle.$$
--   The vector optimum is the supremum of this expression over all such representations; the quantum bias is separately defined as $2\omega^*(G)-1$. Their equality is not assumed by definition.
--
--   The dual objective is $\tfrac12\sum_xa_x+\tfrac12\sum_yb_y$, with positive semidefinite slack matrix $\begin{pmatrix}\Delta(a)&-H\\-H^T&\Delta(b)\end{pmatrix}$. This is twice the source's slack and has the same feasibility condition. Uniform optimal bias $\alpha$ means that constant row and column variables equal to $\alpha$ are feasible and minimize that actual objective over every feasible pair. It imposes no desired error estimate.
--
--   These definitions expose the precise optimality hypothesis of Lemma 4.4.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.10–11, Definition 2.5 and Eq.(7)

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

namespace XORFullTilt.Hardness

noncomputable def gameMatrix {X Y : Type} [Fintype X] [Fintype Y]
    (G : XORGame X Y) (x : X) (y : Y) : ℝ :=
  (if G.f x y then -1 else 1) * G.game.μ x y

structure VectorCorrelation (X Y : Type) (n : ℕ) where
  u : X → Fin n → ℝ
  v : Y → Fin n → ℝ
  u_unit : ∀ x, ∑ i, (u x i)^2 = 1
  v_unit : ∀ y, ∑ i, (v y i)^2 = 1

noncomputable def vectorBias {X Y : Type} [Fintype X] [Fintype Y]
    (G : XORGame X Y) {n : ℕ} (C : VectorCorrelation X Y n) : ℝ :=
  ∑ x, ∑ y, gameMatrix G x y * ∑ i, C.u x i * C.v y i

noncomputable def optimalVectorBias {X Y : Type} [Fintype X] [Fintype Y]
    (G : XORGame X Y) : ℝ :=
  sSup {v | ∃ n, ∃ C : VectorCorrelation X Y n, v = vectorBias G C}

noncomputable def quantumBias {X Y : Type} [Fintype X] [Fintype Y]
    (G : XORGame X Y) : ℝ := 2 * quantumValue G.game - 1

/-- Twice the slack matrix in the dual (7); scaling by two preserves PSD. -/
noncomputable def dualSlack {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (G : XORGame X Y) (a : X → ℝ) (b : Y → ℝ) :
    Matrix (X ⊕ Y) (X ⊕ Y) ℝ := fun i j => match i, j with
  | Sum.inl x, Sum.inl z => if x = z then a x else 0
  | Sum.inr y, Sum.inr z => if y = z then b y else 0
  | Sum.inl x, Sum.inr y => -gameMatrix G x y
  | Sum.inr y, Sum.inl x => -gameMatrix G x y

noncomputable def dualObjective {X Y : Type} [Fintype X] [Fintype Y]
    (a : X → ℝ) (b : Y → ℝ) : ℝ := (∑ x, a x)/2 + (∑ y, b y)/2

noncomputable def UniformOptimalBias {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (G : XORGame X Y) (α : ℝ) : Prop :=
  (dualSlack G (fun _ => α) (fun _ => α)).PosSemidef ∧
  ∀ a b, (dualSlack G a b).PosSemidef →
    dualObjective (fun _ : X => α) (fun _ : Y => α) ≤ dualObjective a b

end XORFullTilt.Hardness


