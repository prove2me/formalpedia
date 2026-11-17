-- Prove2me | Definitions.Def_IntADSat_Supplement_UnitFrameConditions
-- name    : IntADSat_Supplement_UnitFrameConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:48:13.685219+00:00
-- url     : https://prove2.me/theorems/17db370b-3dee-4563-b055-4fe140ca6a0c
-- title:
--   Conditions (1)–(3) of Definition S5.3
-- statement:
--   For a lattice $L\subseteq V=\mathbb Q^{V(G)}$ and $\omega=e$, the unit-vector conditions of Definition S5.3 are:
--
--   1. the unit vectors of $L$ (those with $\langle v,v\rangle=1$) span $V$;
--   2. every unit vector $v\in L$ satisfies $|\langle\omega,v\rangle|=1$;
--   3. on the seed-oriented unit frame $V_\omega(L)=\{v\in L:\langle v,v\rangle=1,\ \langle\omega,v\rangle=1\}$, every vector is an eigenvector of $D=D_G$, and
--   $$\langle v,Av\rangle=0,\qquad\langle u,Av\rangle\in\{0,1\}\quad(u\neq v)$$
--   for $u,v\in V_\omega(L)$, where $A=A_G$.
--
--   A subgroup $S$ of the discriminant group is graph-admissible when its preimage lattice satisfies these conditions.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Definition S5.3, p.41 (PDF 42)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- Conditions (1)–(3) of **Definition S5.3** (graph-admissibility) for a lattice `L ⊆ V = ℚⁿ`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.41 (PDF 42)), with `ω = e`:
1. the unit vectors of `L` (`⟨v, v⟩ = 1`) span `V`;
2. every unit vector `v ∈ L` has `|⟨ω, v⟩| = 1`;
3. on the seed-oriented unit frame `V_ω(L) = {v ∈ L : ⟨v, v⟩ = 1, ⟨ω, v⟩ = 1}` every vector is an
   eigenvector of `D`, `⟨v, Av⟩ = 0`, and `⟨u, Av⟩ ∈ {0, 1}` for `u ≠ v` in `V_ω(L)`.

**Formalization Note** Unit vectors are nonzero, so "eigenvector" is `Dv = cv` for some `c ∈ ℚ`.
`A = A_G`, `D = D_G` are cast to `ℚ`. -/
def UnitFrameConditions {n : ℕ} (G : SimpleGraph (Fin n)) (L : Submodule ℤ (Fin n → ℚ)) : Prop :=
  Submodule.span ℚ {v : Fin n → ℚ | v ∈ L ∧ v ⬝ᵥ v = 1} = ⊤ ∧
    (∀ v ∈ L, v ⬝ᵥ v = 1 → |(fun _ => (1 : ℚ)) ⬝ᵥ v| = 1) ∧
    (∀ v ∈ L, v ⬝ᵥ v = 1 → (fun _ => (1 : ℚ)) ⬝ᵥ v = 1 →
      (∃ c : ℚ, ((degreeMatrix G).map (Int.cast : ℤ → ℚ)).mulVec v = c • v) ∧
      v ⬝ᵥ ((adjacency G).map (Int.cast : ℤ → ℚ)).mulVec v = 0 ∧
      ∀ u ∈ L, u ⬝ᵥ u = 1 → (fun _ => (1 : ℚ)) ⬝ᵥ u = 1 → u ≠ v →
        (u ⬝ᵥ ((adjacency G).map (Int.cast : ℤ → ℚ)).mulVec v = 0 ∨
          u ⬝ᵥ ((adjacency G).map (Int.cast : ℤ → ℚ)).mulVec v = 1))

end IntADSat.Supplement


