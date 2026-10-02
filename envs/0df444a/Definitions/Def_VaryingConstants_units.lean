-- Prove2me | Definitions.Def_VaryingConstants_units
-- name    : VaryingConstants_units
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T01:20:00.653988+00:00
-- url     : https://prove2.me/theorems/f67bd9d9-8553-45b8-bf4d-49ea0e6dcc0b
-- title:
--   Dimensional analysis of physical constants: unit changes, dimensionless monomials, natural units
-- statement:
--   This file fixes the vocabulary of dimensional analysis used throughout the mission.
--
--   We consider $n$ dimensional constants $x_1,\dots,x_n$ measured with respect to $d$ base units $U_1,\dots,U_d$ (for mechanics, $d=3$: length $L$, mass $M$, time $T$). The **dimension matrix** $D\in\mathbb R^{n\times d}$ records that constant $i$ has dimension $\prod_j U_j^{D_{ij}}$. Real exponents are allowed (e.g. Gaussian units give the charge the dimension $M^{1/2}L^{3/2}T^{-1}$).
--
--   1. **Change of units.** For a vector $s\in\mathbb R^d$ (in practice $s_j>0$), the rescaled configuration is
--   $$ (s\cdot x)_i \;=\; x_i\prod_{j=1}^d s_j^{\,D_{ij}} . $$
--   Here $s_j$ is the factor by which numerical values of quantities of dimension $U_j$ change.
--   2. **Positivity.** A vector is positive if all its entries are $>0$.
--   3. **Unit-invariant observable.** $f:\mathbb R^n\to\mathbb R$ is unit invariant if $f(s\cdot x)=f(x)$ for every positive $x$ and every positive $s$.
--   4. **Dimensionless exponents.** The subspace $\mathcal Z_D=\{a\in\mathbb R^n : \sum_i a_i D_{ij}=0 \ \forall j\}$ (the left kernel of $D$).
--   5. **Power monomial.** $\pi_a(x)=\prod_i x_i^{a_i}$.
--   6. **Natural units.** Given $d$ chosen constants $e_1,\dots,e_d$, a positive $s$ is a system of natural units for $x$ if $(s\cdot x)_{e_j}=1$ for all $j$.
--   7. **Planck dimension matrix.** With rows $(c,G,\hbar)$ and columns $(L,M,T)$:
--   $$ D_{\rm P}=\begin{pmatrix}1&0&-1\\ 3&-1&-2\\ 2&1&-1\end{pmatrix}, $$
--   i.e. $[c]=LT^{-1}$, $[G]=L^3M^{-1}T^{-2}$, $[\hbar]=L^2MT^{-1}$.
--
--   These objects make precise the statements of Uzan's §2.1: natural units are defined by setting three independent constants to $1$, and "only the variation of dimensionless constants can be measured".
--
--   **Formalization Note** Real powers are `Real.rpow`; positivity is not built into the vectors but carried as explicit hypotheses. $\mathcal Z_D$ is the kernel of $a\mapsto a^{\mathsf T}D$.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1 ("Natural units", pp. 15–16; "Fundamental parameters", p. 17) and §2.1.2 (p. 14).

import Mathlib

/-!
Dimensional analysis of physical constants (Uzan 2011, Living Rev. Relativity 14:2, §2.1).

`n` dimensional constants are measured with respect to `d` base units (for mechanics
`d = 3`: length, mass, time).  The dimension matrix `D : Matrix (Fin n) (Fin d) ℝ` records
that constant `i` has dimension `∏ⱼ Uⱼ ^ D i j`.  A configuration `x : Fin n → ℝ` lists the
(positive) numerical values of the constants in some system of units.
-/

namespace VaryingConstants

/-- Change of units: if every base unit `j` is rescaled so that numerical values of quantities
of dimension `Uⱼ` are multiplied by `s j > 0`, the numerical value of constant `i` is multiplied
by `∏ⱼ (s j) ^ (D i j)`. -/
noncomputable def unitRescale {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (s : Fin d → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * ∏ j, s j ^ D i j

/-- All entries of a vector are strictly positive. -/
def IsPositive {m : ℕ} (x : Fin m → ℝ) : Prop :=
  ∀ i, 0 < x i

/-- A real-valued function of the numerical values of the constants is *unit invariant*
(the outcome of a measurement): on positive configurations it does not change under any
change of units. -/
def IsUnitInvariant {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, IsPositive x → ∀ s : Fin d → ℝ, IsPositive s → f (unitRescale D s x) = f x

/-- Exponent vectors `a` for which the power product `∏ᵢ xᵢ ^ aᵢ` is dimensionless,
i.e. `∑ᵢ aᵢ D i j = 0` for every base unit `j`. -/
def dimensionlessExponents {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.vecMulLinear D)

/-- The power product `∏ᵢ xᵢ ^ aᵢ` (real exponents). -/
noncomputable def powerMonomial {n : ℕ} (a x : Fin n → ℝ) : ℝ :=
  ∏ i, x i ^ a i

/-- `s` is a system of natural units for the configuration `x` built on the constants
`e 0, …, e (d-1)`: `s` is a positive change of units after which each chosen constant
has numerical value `1`. -/
def IsNaturalUnitsFor {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (e : Fin d → Fin n)
    (x : Fin n → ℝ) (s : Fin d → ℝ) : Prop :=
  IsPositive s ∧ ∀ j, unitRescale D s x (e j) = 1

/-- Dimension matrix of Planck's triple `(c, G, ħ)` in the base units `(L, M, T)`:
`[c] = L T⁻¹`, `[G] = L³ M⁻¹ T⁻²`, `[ħ] = L² M T⁻¹`. -/
def planckDims : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, -1; 3, -1, -2; 2, 1, -1]

end VaryingConstants


