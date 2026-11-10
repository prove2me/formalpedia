-- Prove2me | Definitions.Def_InteractionElim_Main_Instance
-- name    : InteractionElim_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:20:25.888486+00:00
-- url     : https://prove2.me/theorems/83b09abc-250f-4306-b0b7-328b5df2c7e5
-- title:
--   The workflow instance of §2, its stage spaces $W_j$ (2.3), the quantities (2.7) and the regime (2.8)
-- statement:
--   A **workflow instance** consists of $R\ge 16$ coordinates; an ordered partition $(B_1,\dots,B_m)$ of $[R]$ into nonempty blocks (stages), $r_j=|B_j|$, $k=\max_j r_j$; a public binary matrix $A$ with $R$ columns (any number of rows); rational noise parameters $p_i\in[1/8,3/8]$; rational prices $w>0$ (per tool call) and $\gamma>0$ (per paid bit); and a rational risk $\delta\in(0,1)$, with $L=\ln(1/\delta)$.
--
--   With $U_j=\operatorname{row}A\cap\{v: v_{>j}=0\}$ (vectors of the row space vanishing on all later blocks) and $U_{j-1}=\operatorname{row}A\cap\{v:v_{\ge j}=0\}$, the **stage space** (2.3) is
--   $$
--   W_j=\{v_{B_j}: v\in\operatorname{row}A,\ v_{>j}=0\}\le\mathbb F_2^{r_j}.
--   $$
--   The quantities (2.7) are $\Phi=\sum_jF(W_j)$, $P=\sum_j r_j\ln(r_j+1)$, $T_{\ker}=\sum_j\tau(0,W_j^\perp)$, and $\sum_jG(W_j)$. The **regime** (2.8) is
--   $$
--   R\ge16,\quad \tfrac12\le\tfrac{wL}{\gamma}\le2,\quad
--   \Big(L\ge\max\{\ln(R+1),P/(16\Phi)\}\ \text{and}\ \Phi\le L+2T_{\ker}\Big)\ \text{or}\ \Big(k\le4\ \text{and}\ L\ge 8\ln(R+1)\Big),
--   $$
--   and (B.38) is the bounded-block regime $R\ge16$, $k\le4$, $L\ge8\ln(R+1)$, $\tfrac12\le wL/\gamma\le2$.
--
--   The module also records Lemma A.1's objects: a **lift** for stage $j$ is a list of rows $[P_j,Q_j,0_{>j}]$ in $U_j$ that extend a basis of $U_{j-1}$ to one of $U_j$ and whose current-block parts $Q_j$ are independent with row space $W_j$; and a list of vectors supported on $B_j$ whose restrictions form a basis of $W_j^\perp$.
--
--   **Formalization Note** Coordinates are `Fin R` and blocks `Fin m` (0-based, in stage order); the partition is a surjection `block : Fin R → Fin m` (blocks need not be intervals). $\mathbb F_2^{B_j}$ is the function space on the subtype `Blk j`; $\operatorname{proj}_{B_j}$ is restriction. `row A` is the span of the rows; `kerA` is $\{v: Av=0\}$. $\Phi\ge m>0$ by Lemma A.3, so $P/(16\Phi)$ is never a division by zero.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), pp. 4-5, §2 (workflow, Eqs. (2.3), (2.7), (2.8)); p. 17, Lemma A.1 (U_j, lifts); p. 30, (B.38)

import Mathlib
import Definitions.Def_InteractionElim_Main_Certificate

open scoped BigOperators

namespace InteractionElim.Main

/-!
# The workflow instance, its stage spaces `W_j`, the quantities (2.7) and the regime (2.8)

Source: Jin, Zang, Xu, Li, *Eliminating Ongoing Interaction in Long-Running Verification Agents*,
STOC 2027 submission (manuscript sha256 44f6d829…), §2, pp. 4–5, Eqs. (2.3), (2.7), (2.8);
Lemma A.1 (p. 17) for `U_j`; Proposition B.6 (p. 30) for the regime (B.38).

Coordinates `[R]` are `Fin R` (0-based) and the ordered blocks `B_1, …, B_m` are `Fin m`
(0-based, in stage order): coordinate `i` lies in block `block i`. Any surjection
`Fin R → Fin m` is an ordered partition into nonempty blocks (blocks need not be intervals).
-/

/-- A workflow instance of §2: `R ≥ 16` coordinates, an ordered partition into `m` nonempty
blocks, a public binary matrix `A` with `R` columns (any number `nrows` of rows), rational noise
parameters `p_i ∈ [1/8, 3/8]`, rational prices `w, γ > 0` and a rational risk `δ ∈ (0, 1)`. -/
structure Instance where
  /-- Number of coordinates. -/
  R : ℕ
  hR : 16 ≤ R
  /-- Number of blocks (stages). -/
  m : ℕ
  /-- The block (stage) containing each coordinate. -/
  block : Fin R → Fin m
  block_surj : Function.Surjective block
  /-- Number of rows of `A`. -/
  nrows : ℕ
  /-- The public binary matrix; the expert initially knows exactly `A x`. -/
  A : Matrix (Fin nrows) (Fin R) (ZMod 2)
  /-- Noise parameter of the tool on coordinate `i`. -/
  p : Fin R → ℚ
  p_ge : ∀ i, 1 / 8 ≤ p i
  p_le : ∀ i, p i ≤ 3 / 8
  /-- Price of one tool call. -/
  w : ℚ
  w_pos : 0 < w
  /-- Price of one paid bit (either direction). -/
  γ : ℚ
  γ_pos : 0 < γ
  /-- Whole-chain risk. -/
  δ : ℚ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

namespace Instance

variable (I : Instance)

/-- The coordinates of block `j` (the set `B_j`). -/
abbrev Blk (j : Fin I.m) : Type := {i : Fin I.R // I.block i = j}

/-- `r_j = |B_j|`. -/
def r (j : Fin I.m) : ℕ := Fintype.card (I.Blk j)

/-- `k = max_j r_j`. -/
def k : ℕ := Finset.univ.sup I.r

/-- The row space `row A ≤ F_2^R`. -/
def rowSpace : Submodule (ZMod 2) (Fin I.R → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range I.A)

/-- The kernel `ker A = {v : A v = 0}`. -/
def kerA : Submodule (ZMod 2) (Fin I.R → ZMod 2) :=
  LinearMap.ker (Matrix.mulVecLin I.A)

/-- Vectors vanishing on every block after `B_j` (`v_{>j} = 0`). -/
def laterZero (j : Fin I.m) : Submodule (ZMod 2) (Fin I.R → ZMod 2) where
  carrier := {v | ∀ i, j < I.block i → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    simp
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

/-- Vectors vanishing on every block from `B_j` on (`v_{≥j} = 0`). -/
def fromZero (j : Fin I.m) : Submodule (ZMod 2) (Fin I.R → ZMod 2) where
  carrier := {v | ∀ i, j ≤ I.block i → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    simp
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

/-- Vectors vanishing on every block before `B_j` (`v_{<j} = 0`). -/
def earlierZero (j : Fin I.m) : Submodule (ZMod 2) (Fin I.R → ZMod 2) where
  carrier := {v | ∀ i, I.block i < j → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    simp
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

/-- The restriction `proj_{B_j} : F_2^R → F_2^{B_j}`, `v ↦ v_{B_j}`. -/
def restrict (j : Fin I.m) : (Fin I.R → ZMod 2) →ₗ[ZMod 2] (I.Blk j → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) Subtype.val

/-- `U_j = row A ∩ {v : v_{>j} = 0}` (Lemma A.1). -/
def U (j : Fin I.m) : Submodule (ZMod 2) (Fin I.R → ZMod 2) :=
  I.rowSpace ⊓ I.laterZero j

/-- `U_{j−1} = row A ∩ {v : v_{≥j} = 0}` (with `U_0 = 0` for the first block). -/
def Uprev (j : Fin I.m) : Submodule (ZMod 2) (Fin I.R → ZMod 2) :=
  I.rowSpace ⊓ I.fromZero j

/-- The stage space of Eq. (2.3): `W_j = {v_{B_j} : v ∈ row A, v_{>j} = 0} ≤ F_2^{r_j}`. -/
def W (j : Fin I.m) : Submodule (ZMod 2) (I.Blk j → ZMod 2) :=
  (I.U j).map (I.restrict j)

/-- `L = ln(1/δ)`. -/
noncomputable def L : ℝ := Real.log (1 / (I.δ : ℝ))

/-- `Φ = ∑_j F(W_j)` (Eq. (2.7)). -/
noncomputable def Φ : ℝ := ∑ j, F (I.W j)

/-- `∑_j G(W_j)`. -/
noncomputable def sumG : ℝ := ∑ j, G (I.W j)

/-- `P = ∑_j r_j ln(r_j + 1)` (Eq. (2.7)). -/
noncomputable def Pq : ℝ := ∑ j, (I.r j : ℝ) * Real.log (I.r j + 1)

/-- `T_ker = ∑_j τ(0, W_j^⊥)` (Eq. (2.7)). -/
noncomputable def Tker : ℝ := ∑ j, tau 0 (orth (I.W j) : Set (I.Blk j → ZMod 2))

/-- The parameter regime (2.8): `R ≥ 16`, `1/2 ≤ wL/γ ≤ 2`, and either the geometric branch
`L ≥ max{ln(R+1), P/(16Φ)}` with `Φ ≤ L + 2T_ker`, or the bounded-block branch `k ≤ 4` with
`L ≥ 8 ln(R+1)`. -/
def Regime : Prop :=
  16 ≤ I.R ∧ 1 / 2 ≤ (I.w : ℝ) * I.L / I.γ ∧ (I.w : ℝ) * I.L / I.γ ≤ 2 ∧
    ((max (Real.log (I.R + 1)) (I.Pq / (16 * I.Φ)) ≤ I.L ∧ I.Φ ≤ I.L + 2 * I.Tker) ∨
      (I.k ≤ 4 ∧ 8 * Real.log (I.R + 1) ≤ I.L))

/-- The bounded-block regime (B.38) of Proposition B.6: `R ≥ 16`, `k ≤ 4`, `L ≥ 8 ln(R+1)`,
`1/2 ≤ wL/γ ≤ 2`. -/
def RegimeB38 : Prop :=
  16 ≤ I.R ∧ I.k ≤ 4 ∧ 8 * Real.log (I.R + 1) ≤ I.L ∧
    1 / 2 ≤ (I.w : ℝ) * I.L / I.γ ∧ (I.w : ℝ) * I.L / I.γ ≤ 2

/-- Lemma A.1's lift for stage `j`: rows `[P_j, Q_j, 0_{>j}]` (the list `lift`) lying in `U_j`
that extend a basis of `U_{j−1}` to one of `U_j`, whose current-block parts `Q_j` are linearly
independent (full row rank) with row space `W_j`. -/
def IsLift (j : Fin I.m) (lift : List (Fin I.R → ZMod 2)) : Prop :=
  (∀ v ∈ lift, v ∈ I.U j) ∧
    LinearIndependent (ZMod 2) (fun t : Fin lift.length => I.restrict j (lift.get t)) ∧
    Submodule.span (ZMod 2) (Set.range fun t : Fin lift.length => I.restrict j (lift.get t)) =
      I.W j ∧
    I.Uprev j ⊔ Submodule.span (ZMod 2) {v | v ∈ lift} = I.U j

/-- A basis of `W_j^⊥`, written as vectors of `F_2^R` supported on `B_j`. -/
def IsPerpBasis (j : Fin I.m) (b : List (Fin I.R → ZMod 2)) : Prop :=
  (∀ v ∈ b, ∀ i, I.block i ≠ j → v i = 0) ∧
    LinearIndependent (ZMod 2) (fun t : Fin b.length => I.restrict j (b.get t)) ∧
    Submodule.span (ZMod 2) (Set.range fun t : Fin b.length => I.restrict j (b.get t)) =
      orth (I.W j)

end Instance

end InteractionElim.Main


