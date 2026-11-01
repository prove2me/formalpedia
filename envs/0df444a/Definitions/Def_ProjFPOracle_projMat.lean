-- Prove2me | Definitions.Def_ProjFPOracle_projMat
-- name    : ProjFPOracle_projMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:28.757648+00:00
-- url     : https://prove2.me/theorems/75c1e94e-7242-4bd0-be01-776d7cf25885
-- title:
--   The projected operator $M=\Phi_d L\Phi_d^*$
-- statement:
--   For a bounded linear operator $L$ on $\mathbb X$ and the orthonormal basis $\varphi_1,\dots,\varphi_d$ of $\mathbb S$, the **projected operator** is the $d\times d$ matrix
--   $$
--   M:=\Phi_d L\Phi_d^*,\qquad M_{jk}=\langle\varphi_j,L\varphi_k\rangle .
--   $$
--   It represents the compression $\Pi_{\mathbb S}L$ of $L$ to $\mathbb S$ in the coordinates of the basis. All the instance-dependent quantities of the mission ($\kappa(M)$, the approximation factor $\alpha(M,s)$, the statistical term $\mathcal E_n$) are functions of $M$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §2.1, p.7, Eq. (8)

import Mathlib

namespace ProjFPOracle

/-- **The projected operator `M := Φ_d L Φ_d^*`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (8), p.7), the
`d × d` matrix with entries `M_{jk} = ⟨φ_j, L φ_k⟩`.

**Formalization Note** `L : 𝕏 →L[ℝ] 𝕏` is a bounded linear operator and `φ` an orthonormal basis
of the subspace `𝕊`; the entry formula is `Φ_d L Φ_d^*` applied to the standard basis vector `e_k`. -/
noncomputable def projMat {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (L : X →L[ℝ] X) (φ : OrthonormalBasis (Fin d) ℝ S) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => inner ℝ ((φ j : S) : X) (L ((φ k : S) : X))

end ProjFPOracle


