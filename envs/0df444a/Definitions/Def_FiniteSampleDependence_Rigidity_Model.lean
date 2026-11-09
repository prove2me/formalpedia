-- Prove2me | Definitions.Def_FiniteSampleDependence_Rigidity_Model
-- name    : FiniteSampleDependence_Rigidity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:45:20.228549+00:00
-- url     : https://prove2.me/theorems/52f65b36-57a8-4253-a986-0f5c3516431d
-- title:
--   Joint-distribution simplex $\Delta_{n,m}$, column-stochastic channels, (LF-DPI), (IZ) and $C^1$-extendability
-- statement:
--   Fix alphabet sizes $n,m$. A joint distribution of a pair $(X,Y)$ with $X\in\{1,\dots,n\}$ and $Y\in\{1,\dots,m\}$ is a real $n\times m$ matrix $U$ in the closed simplex
--   $$\Delta_{n,m}=\Big\{U\in\mathbb R^{n\times m}:\ U_{i\alpha}\ge 0\ \text{for all } i,\alpha,\quad \tau(U)=\sum_{i,\alpha}U_{i\alpha}=1\Big\}.$$
--   Rows index the variable that is processed. The row and column marginals are $r(U)=U\mathbf 1_m$ and $c(U)=U^\top\mathbf 1_n$.
--
--   A matrix $T\in\mathbb R^{n\times n}$ is **column-stochastic** if its entries are nonnegative and each column sums to one; $T_{ij}$ is the probability that state $j$ is sent to state $i$, and $TU$ is the joint law after processing $X$ through the channel $T$. No condition is imposed on row sums.
--
--   For a functional $F$ on $\Delta_{n,m}$ the two conditions of the paper are
--
--   1. **(LF-DPI)**, left-sided fixed-alphabet data processing inequality: $F(TU)\le F(U)$ for every $U\in\Delta_{n,m}$ and every column-stochastic $T\in\mathbb R^{n\times n}$;
--   2. **(IZ)**, independence-zero: $F(U)=0$ for every $U\in\Delta_{n,m}$ of rank one.
--
--   A **$C^1$ extension** of $F$ is a pair $(\Omega,\widetilde F)$ where $\Omega\subseteq\mathbb R^{n\times m}$ is open and contains the closed simplex $\Delta_{n,m}$, $\widetilde F$ is continuously differentiable on $\Omega$, and $\widetilde F=F$ on $\Delta_{n,m}$. $F$ is **$C^1$-extendable** (Definition 2.2) if it has a $C^1$ extension. The partial derivative $\partial_{i\alpha}\widetilde F(U)$ is the derivative in the direction of the matrix unit $E_{i\alpha}$.
--
--   For distinct rows $i\ne j$ the **merging channel** $M_{ij}$ is the column-stochastic matrix that sends state $j$ to state $i$ and fixes every other state: $M_{ij}U$ has row $i$ equal to $U_{i\bullet}+U_{j\bullet}$, row $j$ equal to zero, and all other rows unchanged.
--
--   These objects are the whole hypothesis layer of the paper's structural theorems.
--
--   **Formalization Note** A functional is a function on all of $\mathbb R^{n\times m}$; (LF-DPI), (IZ) and the extension property only read its values on $\Delta_{n,m}$. The ambient space of an extension is `Fin n → Fin m → ℝ` with its standard product topology and normed structure (all norms on it are equivalent, so $C^1$ does not depend on the choice); a matrix $U$ is placed there by `Matrix.of.symm`. Rank is `Matrix.rank` over $\mathbb R$.
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Section 2 (set-up, (LF-DPI), (IZ)), PDF p. 6 (printed p. 5); Definition 2.2, PDF p. 7 (printed p. 6); merging channel M_ij, Section 3, PDF p. 7 (printed p. 6)

import Mathlib

namespace FiniteSampleDependence.Rigidity

open Matrix

/-- The total mass `τ(U) = ∑_{i,α} U_{iα}` of a real `n × m` matrix. -/
def tau {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ α, U i α

/-- The joint-distribution simplex `Δ_{n,m} = {U ∈ ℝ^{n×m} : U ≥ 0 entrywise, τ(U) = 1}`
(closed: zero entries are allowed). Rows index the processed variable. -/
def simplex (n m : ℕ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {U | (∀ i α, 0 ≤ U i α) ∧ tau U = 1}

/-- The row marginal `r(U) = U 1_m`. -/
def rowMarginal {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) : Fin n → ℝ :=
  fun i => ∑ α, U i α

/-- The column marginal `c(U) = Uᵀ 1_n`. -/
def colMarginal {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) : Fin m → ℝ :=
  fun α => ∑ i, U i α

/-- A square matrix `T ∈ ℝ^{n×n}` is column-stochastic: its entries are nonnegative and each
column sums to one (`T_{ij} = Pr(X' = i | X = j)`). No condition is imposed on row sums. -/
def IsColumnStochastic {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧ ∀ j, ∑ i, T i j = 1

/-- (LF-DPI) Left-sided fixed-alphabet data processing inequality for a functional
`F : Δ_{n,m} → ℝ`: `F(TU) ≤ F(U)` for every `U ∈ Δ_{n,m}` and every column-stochastic
`T ∈ ℝ^{n×n}`. The functional is given as a function on all real `n × m` matrices; only its
values on the simplex enter (note `TU ∈ Δ_{n,m}` whenever `U ∈ Δ_{n,m}`). -/
def LFDPI {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) : Prop :=
  ∀ U ∈ simplex n m, ∀ T : Matrix (Fin n) (Fin n) ℝ, IsColumnStochastic T → F (T * U) ≤ F U

/-- (IZ) Independence-zero: `F(U) = 0` whenever `U ∈ Δ_{n,m}` has rank one. -/
def IZ {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) : Prop :=
  ∀ U ∈ simplex n m, U.rank = 1 → F U = 0

/-- The ambient space `ℝ^{n×m}`, as plain functions so that it carries its standard
(finite-dimensional, product) normed-space structure. -/
abbrev Ambient (n m : ℕ) := Fin n → Fin m → ℝ

/-- `G : Ω → ℝ` is a `C¹` extension of `F` (Definition 2.2): `Ω ⊆ ℝ^{n×m}` is open and contains
the closed simplex `Δ_{n,m}`, `G` is continuously differentiable on `Ω`, and `G = F` on `Δ_{n,m}`.
(`G` is a total function; only its values on `Ω` matter.) -/
def IsC1Extension {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (Ω : Set (Ambient n m))
    (G : Ambient n m → ℝ) : Prop :=
  IsOpen Ω ∧ (∀ U ∈ simplex n m, Matrix.of.symm U ∈ Ω) ∧ ContDiffOn ℝ 1 G Ω ∧
    ∀ U ∈ simplex n m, G (Matrix.of.symm U) = F U

/-- Definition 2.2: `F : Δ_{n,m} → ℝ` is `C¹`-extendable if it has a `C¹` extension to an open
neighbourhood of the closed simplex. -/
def IsC1Extendable {n m : ℕ} (F : Matrix (Fin n) (Fin m) ℝ → ℝ) : Prop :=
  ∃ (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ), IsC1Extension F Ω G

/-- The coordinate direction `E_{iα}` of `ℝ^{n×m}` (the matrix unit), so that the partial
derivative `∂_{iα} G(U)` is `fderiv ℝ G U (entryDir i α)`. -/
def entryDir {n m : ℕ} (i : Fin n) (α : Fin m) : Ambient n m :=
  Pi.single i (Pi.single α 1)

/-- The merging channel `M_{ij}` (for distinct rows `i ≠ j`): left multiplication by it replaces
row `i` by `U_{i•} + U_{j•}`, row `j` by zero, and fixes every other row. It is column-stochastic:
state `j` is sent to state `i`, every other state to itself. -/
def mergeMatrix {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k l =>
    if k = i then (if l = i ∨ l = j then 1 else 0)
    else if k = j then 0
    else if l = k then 1 else 0

end FiniteSampleDependence.Rigidity


