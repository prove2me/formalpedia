-- Prove2me | Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
-- name    : QuantumWalkSearch_ApproxRAA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:02.41496+00:00
-- url     : https://prove2.me/theorems/f7e2f091-fdf3-4827-b6ca-01c49af52019
-- title:
--   The setting of §3.1 and §4: marked projection Π_M, phase flip ref(M⊥), ref(φ), p_M, βᵢ = 18γ/(4π³i²) and the hypotheses on the circuits R(βᵢ)
-- statement:
--   This module fixes the objects shared by Lemmas 1 and 2 of Magniez, Nayak, Roland and Santha.
--
--   Let $X$ be a finite set and $M\subseteq X$ a set of **marked** elements. The Hilbert space is $\mathcal H=\mathbb C^{X\times X}$ with basis $|x\rangle|y\rangle$. An extra register with orthonormal basis indexed by a finite set $\rho$ is attached by tensoring, so $\mathcal H\otimes\mathbb C^{\rho}$ has basis $|x\rangle|y\rangle|r\rangle$. Operators are matrices in these bases.
--
--   1. The **marked subspace** consists of the states whose first register is marked. Its orthogonal projection $\Pi_M$ keeps the basis states $|x\rangle|y\rangle|r\rangle$ with $x\in M$ and kills the others; $\mathrm{Id}-\Pi_M$ is the projection on the orthogonal complement.
--   2. The **phase flip** $\mathrm{ref}(\mathcal M^\perp)=-\mathrm{ref}(\mathcal M)=\mathrm{Id}-2\Pi_M$ multiplies every basis state with $x\in M$ by $-1$ and fixes the others.
--   3. For a state $|\varphi\rangle$, the **reflection** through it is $\mathrm{ref}(\varphi)=2|\varphi\rangle\langle\varphi|-\mathrm{Id}$.
--   4. For a state $|\pi\rangle\in\mathcal H$, the **marked weight** is $p_M=\|\Pi_M|\pi\rangle\|^2$.
--   5. The **precisions** are $\beta_i=\dfrac{18}{4\pi^3}\,\dfrac{\gamma}{i^2}$ for $i\ge 1$.
--   6. **Approximate reflections.** A family $(R_i)_{i\ge1}$, where $R_i$ acts on $\mathcal H\otimes K_i$ with $K_i=\mathbb C^{\kappa_i}$ and a distinguished all-zeros basis state $|0\rangle$, satisfies the hypotheses of Lemmas 1 and 2 at precision parameter $\gamma$ if, for every $i\ge1$, $R_i$ is unitary and
--   $$
--   R_i|\pi\rangle|0\rangle=|\pi\rangle|0\rangle,\qquad \big\|(R_i+\mathrm{Id})|\psi\rangle|0\rangle\big\|\le\beta_i\,\|\psi\|\quad\text{for every }|\psi\rangle\in\mathcal H\text{ with }\langle\pi|\psi\rangle=0 .
--   $$
--   7. For an angle $\theta$, a non-negative integer $t$ is the **first hit** of $\theta$ if $3^t\theta\in[\pi/4,3\pi/4]$ and $3^s\theta\notin[\pi/4,3\pi/4]$ for every $s<t$.
--
--   These are the inputs of the recursive amplitude amplification with approximate reflections: $R_i$ plays the role of the paper's circuit $R(\beta_i)$, an approximation of $\mathrm{ref}(\pi)$ that needs an ancilla register.
--
--   **Formalization Note** $R_i$ stands for $R(\beta_i)$ and is required only at the precisions $\beta_1,\beta_2,\dots$ that the algorithm uses, not at every $\beta>0$; this is a weaker hypothesis than the paper's, so the theorems are at least as strong. Property 3 is stated in the homogeneous form $\le\beta_i\|\psi\|$, which on unit vectors is the paper's "$\le\beta$ when $|\psi\rangle$ is orthogonal to $|\pi\rangle$". Property 1 (the cost $c_1\log 1/\beta$) and the cost $c_2$ of $-\mathrm{ref}(M)$ are not formalized. The data-structure subscript $d$ of the paper is omitted, as in the paper's own error analysis. The register $K_i$ is any finite-dimensional space with a chosen basis state $|0\rangle$; $s_i$ qubits is the case $\kappa_i=\{0,1\}^{s_i}$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 6 (§2, ref(·)), p. 8 (§3.1, M, p_M), p. 12 (Approximate RAA step 2, βᵢ; Lemma 1 properties 2–3, smallest t), p. 15 (Lemma 2, t_max)

import Mathlib

namespace QuantumWalkSearch.ApproxRAA

open Matrix

/-! # The setting of §3.1 and §4 (Magniez–Nayak–Roland–Santha, *Search via Quantum Walk*)

The Hilbert space is `H = ℂ^{X × X}`, modelled as `EuclideanSpace ℂ (X × X)`. An extra register
with basis indexed by a finite type `ρ` is attached by taking the index type `X × X × ρ`
(= `X × (X × ρ)`), so `H ⊗ ℂ^ρ` is `EuclideanSpace ℂ (X × X × ρ)`. Operators are complex
matrices indexed by the basis; a matrix acts on a vector by the matrix–vector product. -/

/-- The action of the operator (matrix) `A` on the vector `v` of `ℂ^ι`: `A v`. -/
noncomputable def act {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (A *ᵥ v.ofLp)

/-- The projection `Π_M` onto the marked subspace: on `ℂ^{X × ρ}` it keeps the basis states
`|x⟩|r⟩` whose first coordinate `x` lies in the marked set `M` and kills the others
(p. 8: "`M = ℂ^{M×X}` denote the subspace with marked items in the first register"; p. 13: the
marked subspace `M̃ = M ⊗ [⊗_j K_j]`). -/
noncomputable def markedProj {X ρ : Type*} [DecidableEq X] [DecidableEq ρ] (M : Finset X) :
    Matrix (X × ρ) (X × ρ) ℂ :=
  Matrix.diagonal fun p => if p.1 ∈ M then 1 else 0

/-- The projection `Id − Π_M` onto the orthogonal complement of the marked subspace. -/
noncomputable def unmarkedProj {X ρ : Type*} [DecidableEq X] [DecidableEq ρ] (M : Finset X) :
    Matrix (X × ρ) (X × ρ) ℂ :=
  Matrix.diagonal fun p => if p.1 ∈ M then 0 else 1

/-- The phase flip `ref(M̃⊥) = −ref(M̃) = Id − 2 Π_M̃`: it multiplies by `−1` every basis state
whose first coordinate is marked (step 2 of Approximate RAA, p. 12: "flip the phase if
`x ∈ M`"). -/
noncomputable def flipMarked {X ρ : Type*} [DecidableEq X] [DecidableEq ρ] (M : Finset X) :
    Matrix (X × ρ) (X × ρ) ℂ :=
  Matrix.diagonal fun p => if p.1 ∈ M then -1 else 1

/-- The reflection through a state, `ref(φ) = 2|φ⟩⟨φ| − Id` (§2, p. 6). -/
noncomputable def refState {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : EuclideanSpace ℂ ι) :
    Matrix ι ι ℂ :=
  (2 : ℂ) • Matrix.vecMulVec φ.ofLp (star φ.ofLp) - 1

/-- `p_M = ‖Π_M |π⟩‖²`, the weight of the state `|π⟩ ∈ H` on the marked subspace (p. 8). -/
noncomputable def markedWeight {X : Type*} [Fintype X] [DecidableEq X] (M : Finset X)
    (piState : EuclideanSpace ℂ (X × X)) : ℝ :=
  ‖act (markedProj M) piState‖ ^ 2

/-- `|ψ⟩|0⟩`: the vector `ψ ∈ H` tensored with the basis state `z` of an extra register `ℂ^ρ`. -/
noncomputable def tensorZero {X ρ : Type*} [DecidableEq ρ] (z : ρ)
    (ψ : EuclideanSpace ℂ (X × X)) : EuclideanSpace ℂ (X × X × ρ) :=
  WithLp.toLp 2 fun p => if p.2.2 = z then ψ (p.1, p.2.1) else 0

/-- The precision used at step `i` of Approximate RAA: `β_i = (18 / (4π³)) · γ / i²` (p. 12). -/
noncomputable def beta (γ : ℝ) (i : ℕ) : ℝ :=
  18 / (4 * Real.pi ^ 3) * γ / (i : ℝ) ^ 2

/-- The hypotheses of Lemmas 1 and 2 on the approximate reflections, at the precisions actually
used. For every step `i ≥ 1`, `R i` is a unitary on `H ⊗ K_i` (`K_i = ℂ^{κ i}`, all-zeros basis
state `z i`) with
* property 2: `R(β_i)|π⟩|0⟩ = |π⟩|0⟩`;
* property 3: `‖(R(β_i) + Id)|ψ⟩|0⟩‖ ≤ β_i ‖ψ‖` for every `ψ ∈ H` orthogonal to `|π⟩`.
Property 1 (the cost `c₁ log 1/β`) is not formalized. -/
structure ApproxReflections {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (piState : EuclideanSpace ℂ (X × X))
    (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (γ : ℝ) : Prop where
  unitary : ∀ i, 1 ≤ i → R i ∈ Matrix.unitaryGroup (X × X × κ i) ℂ
  fixes : ∀ i, 1 ≤ i → act (R i) (tensorZero (z i) piState) = tensorZero (z i) piState
  approx : ∀ i, 1 ≤ i → ∀ ψ : EuclideanSpace ℂ (X × X), inner ℂ piState ψ = 0 →
    ‖act (R i + 1) (tensorZero (z i) ψ)‖ ≤ beta γ i * ‖ψ‖

/-- `t` is the smallest non-negative integer with `3^t · θ ∈ [π/4, 3π/4]` (Lemma 1 with
`θ = sin⁻¹ √p_M`; Lemma 2 with `θ = sin⁻¹ √ε`). -/
def IsFirstHit (θ : ℝ) (t : ℕ) : Prop :=
  (3 : ℝ) ^ t * θ ∈ Set.Icc (Real.pi / 4) (3 * Real.pi / 4) ∧
    ∀ s : ℕ, s < t → (3 : ℝ) ^ s * θ ∉ Set.Icc (Real.pi / 4) (3 * Real.pi / 4)

end QuantumWalkSearch.ApproxRAA


