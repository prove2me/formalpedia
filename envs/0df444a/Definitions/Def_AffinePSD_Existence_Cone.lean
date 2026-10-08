-- Prove2me | Definitions.Def_AffinePSD_Existence_Cone
-- name    : AffinePSD_Existence_Cone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:48:44.868972+00:00
-- url     : https://prove2.me/theorems/4d9e1635-7a16-4fb2-8ee7-f1429ba132e7
-- title:
--   The spaces M_d and S_d, the trace pairing ⟨x,y⟩ = Tr(xy) and its norm, the cones S_d^+ and S_d^{++} (§1.2)
-- statement:
--   Let $M_d$ be the space of real $d\times d$ matrices and $S_d\subset M_d$ the subspace of symmetric matrices. Both carry the **trace pairing**
--   $$\langle x,y\rangle=\operatorname{Tr}(xy)=\sum_{i,j}x_{ij}\,y_{ji},$$
--   whose norm $\|x\|=\sqrt{\langle x,x\rangle}$ is, on $S_d$, the Frobenius norm. We write $S_d^+$ for the cone of symmetric positive semidefinite matrices and $S_d^{++}$ for its interior in $S_d$, the symmetric positive definite matrices; $x\preceq y$ means $y-x\in S_d^+$ and $x\prec y$ means $y-x\in S_d^{++}$. The boundary is $\partial S_d^+=S_d^+\setminus S_d^{++}$.
--
--   The state space of every process in this mission is $S_d^+$, viewed as a subspace of $M_d$ with the subspace topology and the induced Borel $\sigma$-algebra. The file also fixes the unit matrices $E^{ij}$, the symmetrized directions $\tfrac12(E^{ij}+E^{ji})$ along which the paper differentiates functions on $S_d$, and the symmetric part $\operatorname{sym}(y)=\tfrac12(y+y^\top)$.
--
--   **Formalization Note** $M_d$ is the function type `Fin d → Fin d → ℝ`, so it carries Mathlib's normed-space and Borel structures; positive (semi)definiteness is Mathlib's `Matrix.PosSemidef` / `Matrix.PosDef`, which over $\mathbb R$ include symmetry. Analyticity on the open subset $S_d^{++}$ of $S_d$ is later expressed through $\operatorname{sym}$, as analyticity on the open set $\{y\in M_d:\operatorname{sym}(y)\succ0\}$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2, p. 6

import Mathlib

namespace AffinePSD.Existence

/-- The ambient space `M_d` of real `d × d` matrices, as the Pi type `Fin d → Fin d → ℝ`
(Cuchiero–Filipović–Mayerhofer–Teichmann, arXiv:0910.0137v3, §1.2, p. 6).
Formalization Note: a Pi type, so it carries Mathlib's normed-space, measurable and Borel
instances; `Matrix.of` is used only to invoke `PosSemidef`, `PosDef`. -/
abbrev Mat (d : ℕ) := Fin d → Fin d → ℝ

/-- The trace pairing `⟨x, y⟩ = Tr(xy)` (arXiv:0910.0137v3, §1.2, p. 6). -/
def tr {d : ℕ} (x y : Mat d) : ℝ := ∑ i, ∑ j, x i j * y j i

/-- The norm `‖x‖ = √⟨x, x⟩` of the trace pairing (arXiv:0910.0137v3, §1.2, p. 6); on `S_d` it is
the Frobenius norm. Formalization Note: the paper's only scalar product is `Tr(xy)`, and this is
its norm; the Pi sup norm is never used in a formula of the paper. -/
noncomputable def fnorm {d : ℕ} (x : Mat d) : ℝ := Real.sqrt (tr x x)

/-- Matrix product `(xy)_{ik} = ∑_j x_{ij} y_{jk}`. -/
def mmul {d : ℕ} (x y : Mat d) : Mat d := fun i k => ∑ j, x i j * y j k

/-- Matrix transpose. -/
def transpose {d : ℕ} (x : Mat d) : Mat d := fun i j => x j i

/-- `x ∈ S_d`: `x` is symmetric (arXiv:0910.0137v3, §1.2, p. 6). -/
def IsSym {d : ℕ} (x : Mat d) : Prop := ∀ i j, x i j = x j i

/-- `x ∈ S_d^+`: symmetric positive semidefinite (over `ℝ`, `PosSemidef` includes symmetry).
The order `x ⪯ y` is `PSD (y - x)` (arXiv:0910.0137v3, §1.2, p. 6). -/
def PSD {d : ℕ} (x : Mat d) : Prop := (Matrix.of x).PosSemidef

/-- `x ∈ S_d^{++}`: symmetric positive definite; `x ≺ y` is `PD (y - x)`
(arXiv:0910.0137v3, §1.2, p. 6). -/
def PD {d : ℕ} (x : Mat d) : Prop := (Matrix.of x).PosDef

/-- The state space `S_d^+` as a subtype of `M_d`, with the subtype topology and the subtype
(Borel) σ-algebra (arXiv:0910.0137v3, §1.2, p. 6, and §2, p. 7). -/
abbrev Cone (d : ℕ) := {x : Mat d // PSD x}

/-- The unit matrix `E^{ij}` with a single `1` in position `(i, j)`. -/
def E {d : ℕ} (i j : Fin d) : Mat d := fun a b => if a = i ∧ b = j then 1 else 0

/-- The symmetrized unit direction `(E^{ij} + E^{ji}) / 2`, used for the paper's partial
derivatives `∂/∂x_{ij}` of functions read as `x ↦ f((x + x^⊤)/2)` (arXiv:0910.0137v3, p. 6). -/
noncomputable def symE {d : ℕ} (i j : Fin d) : Mat d := (1 / 2 : ℝ) • (E i j + E j i)

/-- The symmetric part `sym y = (y + y^⊤)/2`, used to encode analyticity on the open subset
`S_d^{++}` of `S_d` as analyticity of `y ↦ G (sym y)` on the open set `{y ∈ M_d | sym y ≻ 0}`. -/
noncomputable def sym {d : ℕ} (y : Mat d) : Mat d := (1 / 2 : ℝ) • (y + transpose y)

end AffinePSD.Existence


