-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_werner
-- name    : ArgmaxDeFinetti_Supplement_werner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:42:21.428197+00:00
-- url     : https://prove2.me/theorems/a62a50d7-cc8d-44a4-92d2-0695bffbe70d
-- title:
--   The rectangular Werner state $\omega_{ar,(a^r)}$ and its canonical symmetric purification $\psi_{a,r}$
-- statement:
--   Fix $a,r\ge1$ and $N=ar$, and let $(a^r)$ be the rectangular partition with $r$ rows of length $a$. Since $S_{(a^r)}(\mathbb C^r)=\det^a$ is one-dimensional, the $(a^r)$ Schur–Weyl block of $(\mathbb C^r)^{\otimes N}$ is
--
--   $$
--   W=\{v\in(\mathbb C^r)^{\otimes N}:\ U^{\otimes N}v=\det(U)^a\,v\ \text{ for every unitary } U\}.
--   $$
--
--   The **rectangular Werner state** is the normalized projector $\omega_{ar,(a^r)}=P_W/\dim W$. Its **canonical purification** is
--
--   $$
--   \psi_{a,r}=(I\otimes\sqrt{\omega})\,|\Omega\rangle,\qquad |\Omega\rangle=\sum_x|x\rangle|x\rangle ,
--   $$
--
--   regrouped into $N$ composite sites $\mathbb C^r\otimes\mathbb C^r$ (site $i$ carries the purifying factor $E_i$ and the original factor $A_i$); its coefficient on $|e\rangle_E|x\rangle_A$ is $\sqrt\omega(x,e)$.
--
--   These are the rectangular examples of Christandl, König, Mitchison and Renner, whose $t$-site marginals give the lower bounds of Appendix B.
--
--   **Formalization Note** The block is defined through its $U(r)$-action (by Schur–Weyl duality this is exactly the $(a^r)$-isotypic component), with the orthogonal projector of the standard inner product. Since $P_W$ is a projector, $\sqrt\omega=P_W/\sqrt{\dim W}$, which is the formula used. That $\psi_{a,r}$ lies in $\mathrm{Sym}^{ar}(\mathbb C^r\otimes\mathbb C^r)$ is a fact, not part of the definition.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), App. B.1, p.61

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_Supplement_sepT

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- The subspace `W_{a,r,N} = {v ∈ (ℂ^r)^{⊗N} : U^{⊗N} v = det(U)^a v for every unitary U}` of `(ℂ^r)^{⊗N}`. For
`N = ar` it is the `(a^r)` Schur–Weyl block of `(ℂ^r)^{⊗ar}` (the rectangle with `r` rows of length `a`), since
`S_{(a^r)}(ℂ^r) = det^a` is one-dimensional, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), App. B.1, p.61.

**Formalization Note** The block is defined by its `U(r)`-action: by Schur–Weyl duality the `(a^r)`-isotypic
component of `(ℂ^r)^{⊗ar}` is `S_{(a^r)}(ℂ^r) ⊗ V_{(a^r)}`, on which `U^{⊗ar}` acts as `det(U)^a`, and every vector on
which `U^{⊗ar}` acts as `det(U)^a` lies in it. The subspace lives in `EuclideanSpace ℂ (Fin N → Fin r)` (the
standard inner product) so that its orthogonal projector is available. -/
noncomputable def wernerSpace (a r N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin N → Fin r)) :=
  ⨅ U : Matrix.unitaryGroup (Fin r) ℂ,
    LinearMap.ker (Matrix.toEuclideanLin (kronPow (U : Matrix (Fin r) (Fin r) ℂ) N -
      ((U : Matrix (Fin r) (Fin r) ℂ).det ^ a) • (1 : Matrix (Fin N → Fin r) (Fin N → Fin r) ℂ)))

/-- The orthogonal projector `P_W` onto `wernerSpace a r N`, as a matrix on `(ℂ^r)^{⊗N}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), App. B.1, p.61. -/
noncomputable def wernerProj (a r N : ℕ) : Matrix (Fin N → Fin r) (Fin N → Fin r) ℂ :=
  Matrix.toEuclideanLin.symm ((wernerSpace a r N).starProjection : EuclideanSpace ℂ (Fin N → Fin r) →ₗ[ℂ]
    EuclideanSpace ℂ (Fin N → Fin r))

/-- The rectangular Werner state `ω_{ar,(a^r)} = P_W / dim W`, the normalized projector onto the `(a^r)` Schur–Weyl
block of `(ℂ^r)^{⊗ar}`, used with `N = ar`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), App. B.1, p.61 ("Let ω_{ar,(a^r)} be the rectangular Werner
state: the normalized projector onto the (a^r) Schur–Weyl block of (ℂ^r)^{⊗ar}"). -/
noncomputable def wernerState (a r N : ℕ) : Matrix (Fin N → Fin r) (Fin N → Fin r) ℂ :=
  ((Module.finrank ℂ (wernerSpace a r N) : ℂ))⁻¹ • wernerProj a r N

/-- The canonical symmetric purification `ψ_{a,r} = (I ⊗ √ω)|Ω⟩` of the rectangular Werner state, `|Ω⟩ = Σ_x |x⟩|x⟩`
over `(ℂ^r)^{⊗N}`, regrouped into `N` composite sites `ℂ^r ⊗ ℂ^r` (site `i` = `(E_i, A_i)`, purifying factor first),
used with `N = ar`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), App. B.1, p.61 ("Let ψ_{a,r} be its canonical symmetric purification in
Sym^{ar}(ℂ^r ⊗ ℂ^r)").

**Formalization Note** The coefficient of `|e⟩_E |x⟩_A` in `(I ⊗ √ω)|Ω⟩` is `√ω(x, e)`. Since `ω = P_W / k` with
`k = dim W` and `P_W` a projector, `√ω = P_W / √k`, which is what is written. The composite index
`z : Fin N → Fin r × Fin r` has `(z i).1 = E_i`, `(z i).2 = A_i`. That this vector lies in `Sym^{ar}(ℂ^r ⊗ ℂ^r)` and
spans the Cauchy summand `S_{(a^r)}(ℂ^r) ⊗ S_{(a^r)}(ℂ^r)` is a fact the paper records, not part of the definition. -/
noncomputable def wernerPurif (a r N : ℕ) : (Fin N → Fin r × Fin r) → ℂ :=
  fun z => ((Real.sqrt (Module.finrank ℂ (wernerSpace a r N)) : ℂ))⁻¹ *
    wernerProj a r N (fun i => (z i).2) (fun i => (z i).1)

end Supplement

end ArgmaxDeFinetti


