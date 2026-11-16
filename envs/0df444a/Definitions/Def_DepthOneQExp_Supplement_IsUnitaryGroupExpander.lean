-- Prove2me | Definitions.Def_DepthOneQExp_Supplement_IsUnitaryGroupExpander
-- name    : DepthOneQExp_Supplement_IsUnitaryGroupExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:35:13.75116+00:00
-- url     : https://prove2.me/theorems/486d9dc6-85a9-4a7c-a139-31ddc4ca45a9
-- title:
--   Expander on $\mathrm{SU}(d)$ with spectral gap $\Delta$ (Definition 1.3)
-- statement:
--   Let $V_1,\dots,V_m\in\mathrm{SU}(d)$. For a finite-dimensional unitary representation $\rho$ of $\mathrm{SU}(d)$ on $\mathbb C^{D}$, set
--   $$
--   \Phi_\rho = \frac1m\sum_{i=1}^m \rho(V_i).
--   $$
--   The family is an **expander on $\mathrm{SU}(d)$ with spectral gap $\Delta>0$** if
--   $$
--   \|\Phi_\rho|X\rangle\| \le (1-\Delta)\,\||X\rangle\|
--   $$
--   for every finite-dimensional unitary representation $\rho$ and every $|X\rangle$ orthogonal to the invariant subspace $\{|w\rangle : \rho(g)|w\rangle = |w\rangle \text{ for all } g\}$ of $\rho$. The number $m$ is the degree. An expander family is a sequence of such expanders in growing dimensions with the same degree and the same $\Delta$.
--
--   Unlike a quantum expander (Definition 1.1/2.1, which controls only the representation $U\otimes\bar U$), this asks for the gap in every representation at once.
--
--   **Formalization Note** $\mathrm{SU}(d)$ is `Matrix.specialUnitaryGroup ι ℂ` for a finite index type of size $d$, with the subspace topology. Representations are the published `ConstGapCircuits.UnitaryRep`, i.e. continuous homomorphisms into $\mathrm U(D)$. Every finite-dimensional unitary representation of the compact semisimple Lie group $\mathrm{SU}(d)$ is automatically continuous (van der Waerden), so no representation is lost. The family is indexed by $\mathrm{Fin}\ m$, so repetitions count in the average.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Definition 1.3, Eq. (1.2), p.2

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap

namespace DepthOneQExp.Supplement

open scoped InnerProductSpace

/-- **Expander on the unitary group with spectral gap `Δ`** (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Definition 1.3, p.2): for a
representation `ρ` of `SU(d)` let `Φ_ρ = (1/m) Σ_{i=1}^m ρ(V_i)`; the family `V_1, …, V_m ∈ SU(d)`
is an expander on `SU(d)` with spectral gap `Δ > 0` if `‖Φ_ρ |X⟩‖ ≤ (1 − Δ) ‖|X⟩‖` for all `|X⟩`
orthogonal to the invariant subspace of `ρ` and all finite-dimensional unitary representations `ρ`.

**Formalization Note** `SU(d)` is `Matrix.specialUnitaryGroup ι ℂ` for a finite index type `ι` of
size `d`, with the subspace topology of the matrix space. Representations are
`ConstGapCircuits.UnitaryRep`: homomorphisms `SU(d) → U(dim)` that are continuous (every
finite-dimensional unitary representation of the compact semisimple Lie group `SU(d)` is
automatically continuous, so nothing is lost). The vector `|X⟩` lies in `ℂ^{dim}`; "orthogonal to
the invariant subspace" is `⟨w, X⟩ = 0` for every `w` fixed by all `ρ(g)`. The family is indexed by
`Fin m` (repetitions count in the average), and `0 < Δ` is part of the definition, as in the
paper. -/
def IsUnitaryGroupExpander {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (V : Fin m → Matrix.specialUnitaryGroup ι ℂ) (Δ : ℝ) : Prop :=
  0 < Δ ∧
    ∀ ρ : ConstGapCircuits.UnitaryRep (Matrix.specialUnitaryGroup ι ℂ),
      ∀ x : EuclideanSpace ℂ (Fin ρ.dim),
        (∀ w : EuclideanSpace ℂ (Fin ρ.dim),
            (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ)
                (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) w = w) → ⟪w, x⟫_ℂ = 0) →
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
              ((1 / (m : ℂ)) • ∑ i, (ρ.hom (V i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) x‖ ≤
            (1 - Δ) * ‖x‖

end DepthOneQExp.Supplement


