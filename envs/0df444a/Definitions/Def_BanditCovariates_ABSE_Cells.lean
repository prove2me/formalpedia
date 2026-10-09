-- Prove2me | Definitions.Def_BanditCovariates_ABSE_Cells
-- name    : BanditCovariates_ABSE_Cells
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:07:19.588455+00:00
-- url     : https://prove2.me/theorems/962a05bf-bad9-4a4f-b344-224e8748e872
-- title:
--   §§3.3 and 5 — dyadic cells, k₀ (5.1), ℓ_B (5.2), c₀, c₁, ε_{B,s} and cell means (3.1)
-- statement:
--   A dyadic cell $B$ of depth $k$ is a cube of side $|B|=2^{-k}$ in the regular partition $\mathcal B_{2^k}$ of $\mathcal X=[0,1]^d$ into $2^{kd}$ cubes; it is indexed by its depth and its integer coordinates $(j_1,\dots,j_d)$ with $0\le j_l<2^k$. Its children $\operatorname{burst}(B)$ are the $2^d$ cells of depth $k+1$ that partition it. For arm $i$, the cell mean (3.1) is
--
--   $$\bar f_B^{(i)}=\frac{1}{P_X(B)}\int_B f^{(i)}(x)\,dP_X(x).$$
--
--   With $c_0=2Ld^{\beta/2}$ and $c_1=2^{3+\beta}c_0$, the maximal depth $k_0$ is the smallest integer with $2^{-k_0}\le(K\log K/n)^{1/(d+2\beta)}$ (5.1), and the stopping round $\ell_B\ge1$ of a cell is the smallest integer with
--
--   $$U(\ell_B,n|B|^d)\le 2c_0|B|^\beta \qquad (5.2).$$
--
--   The proof's radius is $\varepsilon_{B,s}=2U(s,n|B|^d)$.
--
--   **Formalization Note** A point is assigned to the cell with coordinates $\min(\lfloor 2^kx_l\rfloor,2^k-1)$, so cells are half-open (closed at the face $x_l=1$) and partition the cube exactly; the paper defines cells only up to Lebesgue-null boundaries. $k_0$ and $\ell_B$ are least elements of sets of natural numbers; both sets are nonempty on the parameter range of the theorems ($K\ge2$, $n\ge K\log K$; $U(\cdot,T)\to0$). $\ell_B$ is searched among $s\ge1$, since Lean's $U(0,T)$ would be $0$ instead of the paper's $+\infty$. The cell mean is a junk value only for a cell of zero mass, which the density lower bound excludes.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, pp. 13–14, 20–21, 23–24, (3.1), (5.1), (5.2), definitions of ε_{B,s} and c₁

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Setting

noncomputable section

namespace BanditCovariates.ABSE

open MeasureTheory

/-- A node of the dyadic tree: depth and integer coordinates. -/
structure Cell (d : ℕ) where
  depth : ℕ
  idx : Fin d → ℕ
  deriving DecidableEq

/-- The root of the tree. -/
def root (d : ℕ) : Cell d := ⟨0, fun _ => 0⟩

def ValidCell {d : ℕ} (B : Cell d) : Prop :=
  ∀ j, B.idx j < 2 ^ B.depth

/-- Boundary points are assigned to the cell on their right, except that 1
belongs to the last cell. This fixes the paper's null-boundary ambiguity. -/
def cellAt (d k : ℕ) (x : Covariate d) : Cell d :=
  ⟨k, fun j => min (Nat.floor (((2 : ℝ) ^ k) * x j)) (2 ^ k - 1)⟩

def cellSet {d : ℕ} (B : Cell d) : Set (Covariate d) :=
  {x | x ∈ cube d ∧ cellAt d B.depth x = B}

def side {d : ℕ} (B : Cell d) : ℝ :=
  1 / (2 : ℝ) ^ B.depth

/-- The children at the next depth, indexed by binary coordinate choices. -/
def burst {d : ℕ} (B : Cell d) : Finset (Cell d) :=
  Finset.univ.image (fun bits : Fin d → Fin 2 =>
    ⟨B.depth + 1, fun j => 2 * B.idx j + (bits j).val⟩)

/-- The least dyadic depth satisfying (5.1). On the theorem's parameter
range this set is nonempty; outside that range `sInf` is a default. -/
def k0 (d K n : ℕ) (β : ℝ) : ℕ :=
  sInf {k : ℕ | (1 / (2 : ℝ) ^ k) ≤
    (((K : ℝ) * Real.log (K : ℝ) / (n : ℝ)) ^
      (1 / ((d : ℝ) + 2 * β)))}

/-- The cells of depth k, i.e. the regular partition into `2^(k d)` cubes of side `2^(-k)`. -/
def cellsAt (d k : ℕ) : Finset (Cell d) :=
  Finset.univ.image (fun j : Fin d → Fin (2 ^ k) => (⟨k, fun l => (j l : ℕ)⟩ : Cell d))

/-- The constant `c₀ = 2 L d^{β/2}` of Policy 3 and (5.2). -/
def c0 (d : ℕ) (β L : ℝ) : ℝ := 2 * L * (d : ℝ) ^ (β / 2)

/-- The constant `c₁ = 2^{3+β} c₀` of the proof of Theorem 5.1 (p. 24). -/
def c1 (d : ℕ) (β L : ℝ) : ℝ := (2 : ℝ) ^ (3 + β) * c0 d β L

/-- The least positive round count satisfying (5.2). -/
def ell (d n : ℕ) (β L : ℝ) (B : Cell d) : ℕ :=
  sInf {s : ℕ | 1 ≤ s ∧ U s ((n : ℝ) * side B ^ d) ≤
    2 * c0 d β L * side B ^ β}

/-- The cell-conditional arm mean (3.1). -/
def fbar {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Machine d K Ω) (B : Cell d) (i : Fin K) : ℝ :=
  (∫ x in cellSet B, M.f i x ∂M.PX) / (M.PX (cellSet B)).toReal

/-- The proof's radius ε_{B,s}=2U(s,n|B|^d). -/
def epsilon (d n : ℕ) (B : Cell d) (s : ℕ) : ℝ :=
  2 * U s ((n : ℝ) * side B ^ d)

end BanditCovariates.ABSE


