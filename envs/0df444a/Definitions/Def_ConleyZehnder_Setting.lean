-- Prove2me | Definitions.Def_ConleyZehnder_Setting
-- name    : ConleyZehnder_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-09T13:20:01.55639+00:00
-- url     : https://prove2.me/theorems/94760363-aa31-422a-97ac-a46b7fca221d
-- title:
--   Paths of symplectic matrices, $\hat\rho$, and the Conley–Zehnder and Maslov indices
-- statement:
--   Objects for the Conley–Zehnder index of paths of symplectic matrices, following Gutt, §2.
--
--   1. **Symplectic group.** $\mathbb{R}^{2n}$ has coordinates $(q,p)$ and
--   $$J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}.$$
--   $\mathrm{Sp}(2n)$ is the set of real $2n\times2n$ matrices with $AJ_0A^{\mathsf T}=J_0$, and $\mathrm{Sp}^*(2n)=\{A\in\mathrm{Sp}(2n):\det(\mathrm{Id}-A)\neq0\}$.
--   2. **Paths.** $\mathrm{SP}(n)$ is the set of continuous $\psi:[0,1]\to\mathrm{Sp}(2n)$ with $\psi(0)=\mathrm{Id}$ and $\psi(1)\in\mathrm{Sp}^*(2n)$ (Definition 4). A symplectic loop is a continuous $\varphi:[0,1]\to\mathrm{Sp}(2n)$ with $\varphi(0)=\varphi(1)=\mathrm{Id}$.
--   3. **Endpoints.** $W^+=-\mathrm{Id}$ and $W^-=\mathrm{diag}(2,-1,\dots,-1,\tfrac12,-1,\dots,-1)$.
--   4. **Complex determinant.** $C_A=\tfrac12(A-J_0AJ_0)=\begin{pmatrix}X&-Y\\Y&X\end{pmatrix}$, $\det_{\mathbb C}C_A=\det(X+iY)$, and $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ (formula (9)).
--   5. **Degree.** A continuous $\theta:[0,1]\to\mathbb{R}$ is an argument of $f:[0,1]\to\mathbb{C}$ if $f(t)=e^{i\theta(t)}$ for all $t$. An extension of $\psi\in\mathrm{SP}(n)$ is a path $\chi$ in $\mathrm{Sp}^*(2n)$ from $\psi(1)$ to $W^+$ or $W^-$. The integer $k$ is a value of the index of $\psi$ if for some extension $\chi$ and arguments $\theta_1$ of $\hat\rho\circ\psi$ and $\theta_2$ of $\hat\rho\circ\chi$,
--   $$2\big((\theta_1(1)-\theta_1(0))+(\theta_2(1)-\theta_2(0))\big)=2\pi k,$$
--   i.e. $k=\deg(\hat\rho^2\circ\tilde\psi)$ for the concatenation $\tilde\psi$ of $\psi$ and $\chi$.
--   6. **Indices.** $\mu_{CZ}(\psi)$ is such a value $k$ (Definition 7 in the form of Corollary 12), and the Maslov index $\mu(\varphi)$ of a loop is an integer $k$ with $\theta(1)-\theta(0)=2\pi k$ for an argument $\theta$ of $\hat\rho\circ\varphi$.
--   7. **Signature and block sum.** $\mathrm{Sign}(S)$ is the number of positive minus the number of negative eigenvalues of a symmetric $S$. $A'\diamond A''$ is the block embedding $\mathrm{Sp}(2n')\times\mathrm{Sp}(2n'')\to\mathrm{Sp}(2(n'+n''))$, $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$.
--   8. **The three characterizing properties** for a map $\mu$ from paths to $\mathbb{Z}$:
--      - *Homotopy*: $\mu$ is constant on each connected component of $\mathrm{SP}(n)$ (compact-open topology).
--      - *Loop*: $\mu(\varphi\psi)=\mu(\psi)+2\mu(\varphi)$ for every symplectic loop $\varphi$ and every $\psi\in\mathrm{SP}(n)$.
--      - *Signature*: $2\mu(t\mapsto\exp(tJ_0S))=\mathrm{Sign}(S)$ for every symmetric nondegenerate $S$ whose eigenvalues all have absolute value $<2\pi$.
--
--   **Formalization Note** Matrices are indexed by `Fin n ⊕ Fin n`; $J_0$ is `Matrix.J` and $\mathrm{Sp}(2n)$ is `Matrix.symplecticGroup`. Paths are `C(unitInterval, Mat n)`. `czIndex` and `maslovIndex` pick a value by choice and return $0$ if none exists; that the value exists and is unique is a separate theorem. Index maps are functions on all continuous paths, and the properties constrain them only on $\mathrm{SP}(n)$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, pp. 5-9: Definition 4, Definition 7, Propositions 8-9, Corollary 12, formula (9); Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Real.Sign

/-!
# The Conley–Zehnder index of a path of symplectic matrices

Salamon–Zehnder (CPAM 45, 1992), §3; Salamon, *Lectures on Floer homology* (1999), §2.4;
in the form of Gutt, *Generalized Conley–Zehnder index*, Ann. Fac. Sci. Toulouse 23 (2014),
arXiv:1307.7239, §2: Definition 4 (`SP(n)`), Definition 7 with Corollary 12 (the index),
the Maslov index of a loop and the signature used in Proposition 8.

Conventions. `ℝ²ⁿ` is indexed by `Fin n ⊕ Fin n` (first block `q`, second block `p`).
`J₀ = [[0, -Id], [Id, 0]]` is Mathlib's `Matrix.J`. The symplectic group is Mathlib's
`Matrix.symplecticGroup`, `A J₀ Aᵀ = J₀`, which is the group `Sp(ℝ²ⁿ, Ω₀)`,
`Ω₀ = [[0, Id], [-Id, 0]] = -J₀`, of Gutt §2. Paths are continuous maps on `[0, 1]`.

The index is the degree of `ρ̂² ∘ ψ̃` (Gutt, Corollary 12, formula (8)), where `ψ̃` is `ψ`
followed by a path in `Sp*` ending at `W⁺` or `W⁻`, and `ρ̂(A)` is the normalized complex
determinant of the `ℂ`-linear part `½(A - J₀AJ₀)` (formula (9)). Under the identification
`(x, y) ↦ x + i y` of `ℝ²ⁿ` with `ℂⁿ`, `J₀` is multiplication by `i` and a real matrix
`[[X, -Y], [Y, X]]` is the complex matrix `X + i Y`.
-/

namespace ConleyZehnder

noncomputable section

open Matrix Classical

/-- Real `2n × 2n` matrices, indexed by `Fin n ⊕ Fin n`. -/
abbrev Mat (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ

/-- `J₀ = [[0, -Id], [Id, 0]]`. -/
abbrev J₀ (n : ℕ) : Mat n := Matrix.J (Fin n) ℝ

variable {n : ℕ}

/-- `A ∈ Sp(ℝ²ⁿ, Ω₀)`. -/
def IsSymplectic (A : Mat n) : Prop := A ∈ Matrix.symplecticGroup (Fin n) ℝ

/-- `Sp*(ℝ²ⁿ, Ω₀)`: symplectic matrices without eigenvalue `1`. -/
def SpStar (n : ℕ) : Set (Mat n) := {A | IsSymplectic A ∧ (1 - A).det ≠ 0}

/-- Gutt, Definition 4: `SP(n)`, the continuous paths `ψ : [0, 1] → Sp(ℝ²ⁿ, Ω₀)` with
`ψ(0) = Id` such that `1` is not an eigenvalue of `ψ(1)`. -/
def SP (n : ℕ) : Set C(unitInterval, Mat n) :=
  {ψ | (∀ t, IsSymplectic (ψ t)) ∧ ψ 0 = 1 ∧ (1 - ψ 1).det ≠ 0}

/-- A loop `φ : [0, 1] → Sp(ℝ²ⁿ, Ω₀)` with `φ(0) = φ(1) = Id`. -/
def IsSymplecticLoop (φ : C(unitInterval, Mat n)) : Prop :=
  (∀ t, IsSymplectic (φ t)) ∧ φ 0 = 1 ∧ φ 1 = 1

/-- `W⁺ = -Id`. -/
def Wplus (n : ℕ) : Mat n := -1

/-- `W⁻ = diag(2, -1, …, -1, 1/2, -1, …, -1)`. -/
def Wminus (n : ℕ) : Mat n :=
  Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (2 : ℝ) else -1)
    (fun j : Fin n => if j.val = 0 then (1 / 2 : ℝ) else -1))

/-- The `ℂ`-linear part `C_A = ½(A - J₀ A J₀)` of `A`. -/
def complexLinearPart (A : Mat n) : Mat n := (1 / 2 : ℝ) • (A - J₀ n * A * J₀ n)

/-- `det_ℂ C_A`: writing `C_A = [[X, -Y], [Y, X]]`, the determinant of the complex
`n × n` matrix `X + i Y`. -/
def complexLinearDet (A : Mat n) : ℂ :=
  ((complexLinearPart A).toBlocks₁₁.map (fun x : ℝ => (x : ℂ)) +
    Complex.I • (complexLinearPart A).toBlocks₂₁.map (fun x : ℝ => (x : ℂ))).det

/-- Gutt (9): `ρ̂(A) = det_ℂ C_A / |det_ℂ C_A|`. -/
def rhoHat (A : Mat n) : ℂ := complexLinearDet A / (‖complexLinearDet A‖ : ℂ)

/-- `θ` is a continuous argument of `f : [0, 1] → S¹`: `f(t) = e^{i θ(t)}`. -/
def IsArgLift (f : unitInterval → ℂ) (θ : unitInterval → ℝ) : Prop :=
  Continuous θ ∧ ∀ t, f t = Complex.exp ((θ t : ℂ) * Complex.I)

/-- `χ` continues `ψ` as in Gutt §2: it starts at `ψ(1)`, stays in `Sp*`, and ends at
`W⁺` or `W⁻`. (The extension `ψ̃ : [0, 2] → Sp` is `ψ` followed by `χ`.) -/
def IsSpStarExtension (ψ χ : C(unitInterval, Mat n)) : Prop :=
  χ 0 = ψ 1 ∧ (∀ t, χ t ∈ SpStar n) ∧ (χ 1 = Wplus n ∨ χ 1 = Wminus n)

/-- `k = deg(ρ̂² ∘ ψ̃)` for some extension `ψ̃` of `ψ`: the total change of a continuous
argument of `ρ̂² ∘ ψ̃` along `ψ` followed by `χ` is `2π k`. -/
def IsCZValue (ψ : C(unitInterval, Mat n)) (k : ℤ) : Prop :=
  ∃ χ : C(unitInterval, Mat n), IsSpStarExtension ψ χ ∧
    ∃ θ₁ θ₂ : unitInterval → ℝ, IsArgLift (fun t => rhoHat (ψ t)) θ₁ ∧
      IsArgLift (fun t => rhoHat (χ t)) θ₂ ∧
      2 * ((θ₁ 1 - θ₁ 0) + (θ₂ 1 - θ₂ 0)) = 2 * Real.pi * k

/-- Gutt, Definition 7 / Corollary 12: the Conley–Zehnder index `μ_CZ(ψ) = deg(ρ̂² ∘ ψ̃)`. -/
def czIndex (ψ : C(unitInterval, Mat n)) : ℤ :=
  if h : ∃ k, IsCZValue ψ k then h.choose else 0

/-- `k = deg(ρ̂ ∘ φ)` for a loop `φ`. -/
def IsMaslovValue (φ : C(unitInterval, Mat n)) (k : ℤ) : Prop :=
  ∃ θ : unitInterval → ℝ, IsArgLift (fun t => rhoHat (φ t)) θ ∧ θ 1 - θ 0 = 2 * Real.pi * k

/-- The Maslov index `μ(φ) = deg(ρ̂ ∘ φ)` of a loop of symplectic matrices. -/
def maslovIndex (φ : C(unitInterval, Mat n)) : ℤ :=
  if h : ∃ k, IsMaslovValue φ k then h.choose else 0

/-- `Sign(S)`: the number of positive minus the number of negative eigenvalues of a
symmetric matrix, counted with multiplicity. -/
def signature (S : Mat n) (hS : S.IsHermitian) : ℤ :=
  ((Finset.univ.filter fun i => 0 < hS.eigenvalues i).card : ℤ) -
    ((Finset.univ.filter fun i => hS.eigenvalues i < 0).card : ℤ)

/-- The block-diagonal embedding `A' ⋄ A''` of `Sp(ℝ²ⁿ') × Sp(ℝ²ⁿ'')` into
`Sp(ℝ^{2(n'+n'')})`, `(q', p') ⊕ (q'', p'') ↦ (q', q'', p', p'')`. -/
def diamond {n' n'' : ℕ} (A : Mat n') (B : Mat n'') : Mat (n' + n'') :=
  Matrix.reindex
    ((Equiv.sumSumSumComm (Fin n') (Fin n') (Fin n'') (Fin n'')).trans
      (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))
    ((Equiv.sumSumSumComm (Fin n') (Fin n') (Fin n'') (Fin n'')).trans
      (Equiv.sumCongr finSumFinEquiv finSumFinEquiv))
    (Matrix.fromBlocks A 0 0 B)

/-- (Homotopy) `μ` is constant on the connected components of `SP(n)`, a subspace of
`C([0, 1], ℝ^{2n×2n})` with the compact-open topology. -/
def HomotopyAxiom (μ : C(unitInterval, Mat n) → ℤ) : Prop :=
  ∀ ψ ∈ SP n, ∀ ψ' ∈ connectedComponentIn (SP n) ψ, μ ψ' = μ ψ

/-- (Loop) `μ(φψ) = μ(ψ) + 2 μ(φ)` for every loop `φ` at `Id` and every `ψ ∈ SP(n)`. -/
def LoopAxiom (μ : C(unitInterval, Mat n) → ℤ) : Prop :=
  ∀ φ, IsSymplecticLoop φ → ∀ ψ ∈ SP n, μ (φ * ψ) = μ ψ + 2 * maslovIndex φ

/-- (Signature) If `S = Sᵀ` is nondegenerate with all eigenvalues of absolute value
`< 2π` and `ψ(t) = exp(J₀ S t)`, then `μ(ψ) = ½ Sign(S)`. -/
def SignatureAxiom (μ : C(unitInterval, Mat n) → ℤ) : Prop :=
  ∀ (S : Mat n) (hS : S.IsHermitian), S.det ≠ 0 →
    (∀ i, |hS.eigenvalues i| < 2 * Real.pi) →
    ∀ ψ : C(unitInterval, Mat n), (∀ t, ψ t = NormedSpace.exp ((t : ℝ) • (J₀ n * S))) →
      2 * μ ψ = signature S hS

end

end ConleyZehnder


