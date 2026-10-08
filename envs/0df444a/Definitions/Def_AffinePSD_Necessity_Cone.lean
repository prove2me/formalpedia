-- Prove2me | Definitions.Def_AffinePSD_Necessity_Cone
-- name    : AffinePSD_Necessity_Cone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:45.896977+00:00
-- url     : https://prove2.me/theorems/d5d41c3f-2d28-4b2d-a6ff-7705604ac93c
-- title:
--   The matrix space $M_d$, the trace pairing $\langle x,y\rangle=\mathrm{Tr}(xy)$, its norm, and the cone $S_d^+$ (§1.2)
-- statement:
--   This file fixes the matrix notation of §1.2 of Cuchiero, Filipović, Mayerhofer and Teichmann.
--
--   Let $d \ge 0$ and let $M_d$ be the space of real $d\times d$ matrices, with transpose $x^\top$ and matrix product $xy$. Inside $M_d$:
--
--   1. $S_d$ is the subspace of symmetric matrices, and $\mathrm{sym}(x) = \tfrac12 (x + x^\top)$ is the symmetric part of $x$.
--   2. The scalar product is the trace pairing and its norm is
--   $$\langle x, y\rangle = \mathrm{Tr}(xy) = \sum_{i,j} x_{ij} y_{ji}, \qquad \|x\| = \langle x, x\rangle^{1/2}.$$
--   On $S_d$ this is the Frobenius norm.
--   3. $S_d^+$ is the cone of symmetric positive semidefinite matrices and $S_d^{++}$ the cone of symmetric positive definite matrices, its interior in $S_d$. The boundary is $\partial S_d^+ = S_d^+ \setminus S_d^{++}$. The order is $x \preceq y$ iff $y - x \in S_d^+$.
--   4. The state space of the processes is the cone $S_d^+$ itself, with the topology and Borel $\sigma$-algebra inherited from $M_d$.
--   5. $E^{ij}$ is the matrix with a single entry $1$ in position $(i,j)$, and $\tfrac12(E^{ij} + E^{ji})$ is the symmetric unit direction used for partial derivatives of functions on $S_d$.
--
--   These objects are the common vocabulary of every statement in the mission.
--
--   **Formalization Note.** $M_d$ is the function type `Fin d → Fin d → ℝ`, which carries Mathlib's normed-space and Borel structures; Mathlib's `Matrix.of` is used only to invoke positive (semi)definiteness and the determinant. Over $\mathbb R$, Mathlib's positive semidefiniteness includes symmetry. The cone is the subtype of positive semidefinite matrices.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2, p. 6

import Mathlib

namespace AffinePSD.Necessity

/-- The ambient space `M_d` of real `d × d` matrices (Cuchiero, Filipović, Mayerhofer, Teichmann,
arXiv:0910.0137v3, §1.2, p. 6).

**Formalization Note.** `M_d` is the Pi type `Fin d → Fin d → ℝ`, which carries Mathlib's normed-space,
measurable and Borel instances. `Matrix.of` is used only to invoke `PosSemidef`, `PosDef` and `det`. -/
abbrev Mat (d : ℕ) := Fin d → Fin d → ℝ

/-- The scalar product `⟨x, y⟩ = Tr(xy) = ∑_{i,j} x_{ij} y_{ji}` (§1.2, p. 6). -/
def tr {d : ℕ} (x y : Mat d) : ℝ := ∑ i, ∑ j, x i j * y j i

/-- The norm `‖x‖ = ⟨x, x⟩^{1/2}` of the trace scalar product (§1.2, p. 6). On symmetric matrices this
is the Frobenius norm. -/
noncomputable def fnorm {d : ℕ} (x : Mat d) : ℝ := Real.sqrt (tr x x)

/-- The matrix product `xy`. -/
def mmul {d : ℕ} (x y : Mat d) : Mat d := fun i k => ∑ j, x i j * y j k

/-- The transpose `x^⊤`. -/
def transpose {d : ℕ} (x : Mat d) : Mat d := fun i j => x j i

/-- The symmetric part `(x + x^⊤)/2`. -/
noncomputable def sym {d : ℕ} (x : Mat d) : Mat d := (1 / 2 : ℝ) • (x + transpose x)

/-- `x ∈ S_d`: `x` is symmetric. -/
def IsSym {d : ℕ} (x : Mat d) : Prop := ∀ i j, x i j = x j i

/-- `x ∈ S_d^+`: `x` is symmetric positive semidefinite (over `ℝ`, `PosSemidef` includes symmetry). -/
def PSD {d : ℕ} (x : Mat d) : Prop := (Matrix.of x).PosSemidef

/-- `x ∈ S_d^{++}`: `x` is symmetric positive definite. -/
def PD {d : ℕ} (x : Mat d) : Prop := (Matrix.of x).PosDef

/-- The state space `S_d^+` as a subtype of `M_d`, with the subtype topology and Borel σ-algebra. -/
abbrev Cone (d : ℕ) := {x : Mat d // PSD x}

/-- The unit matrix `E^{ij}` with a single `1` in position `(i, j)`. -/
def E {d : ℕ} (i j : Fin d) : Mat d := fun a b => if a = i ∧ b = j then 1 else 0

/-- The symmetric unit direction `(E^{ij} + E^{ji})/2`. -/
noncomputable def symE {d : ℕ} (i j : Fin d) : Mat d := (1 / 2 : ℝ) • (E i j + E j i)

end AffinePSD.Necessity


