-- Prove2me | Definitions.Def_WildeQIT_Schumacher_IsSpectralDecomposition
-- name    : WildeQIT_Schumacher_IsSpectralDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:54.570989+00:00
-- url     : https://prove2.me/theorems/90835b8e-b379-439a-93e0-3c20a58c158e
-- title:
--   Spectral decomposition $\rho = \sum_x p_X(x)|x\rangle\langle x|$ of a density operator
-- statement:
--   Let $\rho$ be an operator on $\mathcal H_A = \mathbb C^a$, $U$ a matrix on the same space and $p_X$ a probability distribution on the finite set $a$. The triple is a spectral decomposition of $\rho$ when $U$ is unitary and
--
--   $$
--   \rho = \sum_{x} p_X(x)\,|x\rangle\langle x|, \qquad |x\rangle = U e_x ,
--   $$
--
--   i.e. $\rho = U\,\mathrm{diag}(p_X)\,U^\dagger$: the columns $\{|x\rangle\}$ of $U$ form an orthonormal eigenbasis of $\mathcal H_A$ and the eigenvalues $p_X(x)$ are non-negative and sum to one.
--
--   This is the decomposition (15.2) with respect to which the typical subspace and typical projector of $\rho$ are defined.
--
--   **Formalization Note** The eigenbasis is indexed by the same set $a$ as the standard basis, so it is a complete orthonormal basis, as in (15.2). The decomposition is not unique when $\rho$ has repeated eigenvalues; theorems quantify over every spectral decomposition.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (15.2), pp. 462–463

import Definitions.Def_WildeQIT_FinDist
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §15.1, eq. (15.2),
pp. 462–463: a spectral decomposition `ρ_A = ∑_{x ∈ 𝒳} p_X(x) |x⟩⟨x|_A` of a density operator,
where the eigenvectors `{|x⟩_A}` form an orthonormal basis of `ℋ_A` and the eigenvalues `p_X(x)`
are non-negative and sum to one.
-/

open Matrix

namespace WildeQIT.Schumacher

/-- **Spectral decomposition of a density operator** (Wilde, arXiv:1106.1445v8, eq. (15.2),
pp. 462–463). `IsSpectralDecomposition ρ U p` says that `ρ = ∑ₓ p_X(x) |x⟩⟨x|`, where the
orthonormal eigenbasis `{|x⟩}` consists of the columns of the unitary matrix `U` (`|x⟩` has
coordinates `U_{y,x}`) and `p_X = p` is a probability distribution on the index set `𝒳 = a`;
equivalently `ρ = U diag(p) U†`.

**Formalization Note.** The eigenbasis is indexed by the same finite type `a` as the standard
basis of `ℋ_A`, so `|𝒳| = dim ℋ_A`, as in (15.2) (a complete orthonormal eigenbasis). The
decomposition is not unique when `ρ` has repeated eigenvalues; statements quantify over every
spectral decomposition. -/
def IsSpectralDecomposition {a : Type} [Fintype a] [DecidableEq a]
    (ρ U : Matrix a a ℂ) (p : FinDist a) : Prop :=
  U ∈ Matrix.unitaryGroup a ℂ ∧
    ρ = U * Matrix.diagonal (fun x => (p.prob x : ℂ)) * Uᴴ

end WildeQIT.Schumacher


