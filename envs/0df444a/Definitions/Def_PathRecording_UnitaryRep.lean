-- Prove2me | Definitions.Def_PathRecording_UnitaryRep
-- name    : PathRecording_UnitaryRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:16.070097+00:00
-- url     : https://prove2.me/theorems/fed039b0-b523-4b5c-8c1d-82054625f26c
-- title:
--   Continuous unitary representation $\rho:G\to U(N)$
-- statement:
--   Let $G$ be a topological group. A **continuous unitary representation** of $G$ of dimension $N$ is a group homomorphism
--   $$\rho:G\to U(N),\qquad g\mapsto\rho(g),$$
--   into the group of $N\times N$ unitary complex matrices that is continuous. The space $V=\mathbb C^N$ carries its standard orthonormal basis $B(V)=\{|x\rangle: x\in\{1,\dots,N\}\}$, and $\langle y|\rho(g)|x\rangle$ denotes the $(y,x)$ matrix entry of $\rho(g)$. Every matrix entry $g\mapsto\langle y|\rho(g)|x\rangle$ is continuous.
--
--   This is the representation $\rho$ of a compact group whose Haar-random element is queried in the path-recording mission; the irreducible representations $\rho_\lambda$ of Schur–Weyl duality are of the same kind.
--
--   **Formalization Note** The homomorphism goes into `Matrix.unitaryGroup (Fin N) ℂ`; basis indices are `Fin N`.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, §3, pp.30–31 and p.60 (fixed orthonormal basis B(V))

import Mathlib

set_option autoImplicit false

namespace PathRecording

/-!
# Continuous finite-dimensional unitary representations

B. Foxman, A. Lombardi, F. Ma, B. Nehoran, J. Wright, *Quantum Lazy Sampling and Path Recording
for Any Group*, arXiv:2606.30281v2, §3, pp.30–31: "Let G be a compact Lie group. … We will consider
a finite-dimensional representation ρ : G ↦ U(N) of the group G."

**Formalization Note.**
* A representation is a group homomorphism `G →* Matrix.unitaryGroup (Fin N) ℂ` together with its
  continuity (representations of a Lie group are continuous). The space `V = ℂᴺ` carries the
  standard basis `B(V) = {|x⟩ : x ∈ Fin N}` (the fixed orthonormal basis of p.60).
* `ρ.mat g` is the `N × N` unitary matrix `ρ(g)`, with entries `⟨y|ρ(g)|x⟩ = ρ.mat g y x`.
-/

/-- A continuous unitary representation `ρ : G → U(N)` of a topological group `G`
(arXiv:2606.30281v2, §3, p.31). -/
structure UnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (N : ℕ) where
  /-- The homomorphism `g ↦ ρ(g)` into the `N × N` unitary matrices. -/
  toHom : G →* Matrix.unitaryGroup (Fin N) ℂ
  /-- `ρ` is continuous. -/
  continuous_toHom : Continuous toHom

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ}

/-- The unitary matrix `ρ(g)`; its `(y, x)` entry is `⟨y|ρ(g)|x⟩`. -/
def mat (ρ : UnitaryRep G N) (g : G) : Matrix (Fin N) (Fin N) ℂ :=
  (ρ.toHom g : Matrix (Fin N) (Fin N) ℂ)

/-- Every matrix entry `g ↦ ⟨y|ρ(g)|x⟩` is continuous. -/
theorem continuous_mat_apply (ρ : UnitaryRep G N) (y x : Fin N) :
    Continuous fun g => ρ.mat g y x :=
  ((continuous_subtype_val.comp ρ.continuous_toHom).matrix_elem y x)

end UnitaryRep

end PathRecording


