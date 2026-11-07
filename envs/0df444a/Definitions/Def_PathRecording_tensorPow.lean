-- Prove2me | Definitions.Def_PathRecording_tensorPow
-- name    : PathRecording_tensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:54.066601+00:00
-- url     : https://prove2.me/theorems/9bf74a9f-63c9-4676-8e17-0167636bb055
-- title:
--   Tensor power $\rho^{\otimes t}$ and the commutant algebra $\mathcal A_t$
-- statement:
--   Let $\rho:G\to U(N)$ be a unitary representation and $t\ge 0$. The **tensor power** $\rho^{\otimes t}(g)=\rho(g)^{\otimes t}$ acts on $(\mathbb C^N)^{\otimes t}$, whose product basis is $|\vec x\rangle=|x_1,\dots,x_t\rangle$; its matrix entries are
--   $$\langle \vec y|\rho^{\otimes t}(g)|\vec x\rangle=\prod_{i=1}^t\langle y_i|\rho(g)|x_i\rangle .$$
--   The **commutant algebra** of $\rho^{\otimes t}$ is
--   $$\mathcal A_t=\{X\in\mathbb C^{N^t\times N^t}: X\rho^{\otimes t}(g)=\rho^{\otimes t}(g)X\ \text{for all } g\in G\}.$$
--
--   Schur–Weyl duality describes $V^{\otimes t}$ jointly as a representation of $G$ and of $\mathcal A_t$; the path-recording oracle's projector $\Omega_{\mathcal A_t}$ is built from this structure.
--
--   **Formalization Note** Product basis vectors are indexed by functions `Fin t → Fin N`; the matrix $\rho(g)^{\otimes t}$ is the published tensor power of a matrix (`WildeQIT.Schumacher.tensorPow`) applied to $\rho(g)$. The case $t=0$ is allowed: then $\rho^{\otimes 0}(g)=(1)$ and $\mathcal A_0$ is all $1\times1$ matrices (Definition 3.10 is printed for $t\ge1$).
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §3.4, p.33 (ρ^{⊗t}) and Definition 3.10, p.34

import Mathlib
import Definitions.Def_PathRecording_UnitaryRep
import Definitions.Def_WildeQIT_Schumacher_tensorPow

set_option autoImplicit false

namespace PathRecording

/-!
# Tensor powers `ρ^{⊗t}` and the commutant algebra `𝒜_t`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, §3.4, p.33 ("ρ^{⊗t}(g) = ρ(g)^{⊗t}") and Definition 3.10, p.34: "The commutant
algebra 𝒜_t of ρ^{⊗t} is the set of all Nᵗ × Nᵗ matrices that commute with every ρ^{⊗t}(g):
𝒜_t = End_G((ℂᴺ)^{⊗t}) = { X ∈ ℂ^{Nᵗ×Nᵗ} : Xρ^{⊗t}(g) = ρ^{⊗t}(g)X for all g ∈ G }."

**Formalization Note.**
* `(ℂᴺ)^{⊗t}` has the product basis `|x⃗⟩ = |x₁, …, x_t⟩`, indexed by `x⃗ : Fin t → Fin N`; the
  matrix entry is `⟨y⃗|ρ^{⊗t}(g)|x⃗⟩ = ∏ᵢ ⟨yᵢ|ρ(g)|xᵢ⟩`.
* The matrix tensor power is the published `WildeQIT.Schumacher.tensorPow` (entries
  `∏ᵢ M (xᵢ) (yᵢ)` on `Fin t → a`), applied to `M = ρ(g)`.
* `t = 0` is allowed: `Fin 0 → Fin N` has one element and `ρ^{⊗0}(g) = (1)`. Definition 3.10 is
  printed for `t ≥ 1`; at `t = 0` the commutant is all `1 × 1` matrices.
-/

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}

/-- The tensor power `ρ^{⊗t}(g)` as an `Nᵗ × Nᵗ` matrix on the product basis:
`⟨y⃗|ρ^{⊗t}(g)|x⃗⟩ = ∏ᵢ ⟨yᵢ|ρ(g)|xᵢ⟩` (arXiv:2606.30281v2, p.33, p.59). -/
def tensorPow (ρ : UnitaryRep G N) (t : ℕ) (g : G) :
    Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ :=
  WildeQIT.Schumacher.tensorPow t (ρ.mat g)

/-- The commutant algebra `𝒜_t = {X : X ρ^{⊗t}(g) = ρ^{⊗t}(g) X ∀ g}`
(arXiv:2606.30281v2, Definition 3.10, p.34). -/
def commutant (ρ : UnitaryRep G N) (t : ℕ) : Set (Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ) :=
  {X | ∀ g, X * tensorPow ρ t g = tensorPow ρ t g * X}

end PathRecording


