-- Prove2me | Definitions.Def_ProjFPOracle_LSperp
-- name    : ProjFPOracle_LSperp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:37.952227+00:00
-- url     : https://prove2.me/theorems/08e60a4c-cbff-4ea7-8d11-eb34d5cef7f1
-- title:
--   $\Pi_{\mathbb S}$, $L_{\mathbb S,\mathbb S}=\Pi_{\mathbb S}L\Pi_{\mathbb S}$ and $L_{\mathbb S,\perp}=\Pi_{\mathbb S}L\Pi_{\mathbb S^\perp}$
-- statement:
--   Let $\Pi_{\mathbb S}$ be the orthogonal projection of $\mathbb X$ onto the finite-dimensional subspace $\mathbb S$ and $\Pi_{\mathbb S^\perp}=I-\Pi_{\mathbb S}$ the projection onto its orthogonal complement. For a bounded operator $L$ on $\mathbb X$ define the bounded operators
--   $$
--   L_{\mathbb S,\mathbb S}=\Pi_{\mathbb S}L\Pi_{\mathbb S},\qquad L_{\mathbb S,\perp}=\Pi_{\mathbb S}L\Pi_{\mathbb S^\perp}.
--   $$
--   They are two of the four blocks of $L$ in the decomposition $\mathbb X=\mathbb S\oplus\mathbb S^\perp$, and they appear in the approximation-error lemmas (Lemmas 3 and 4).
--
--   **Formalization Note** $\Pi_{\mathbb S}$ is Mathlib's `Submodule.starProjection`; $\mathbb S$ is finite-dimensional because it carries the orthonormal basis $\varphi$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §5.1.1, pp.27–28

import Mathlib

namespace ProjFPOracle

/-- **The orthogonal projection `Π_𝕊` onto `𝕊`**, as a bounded operator on `𝕏` (Mou, Pananjady &
Wainwright, *Optimal Oracle Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1,
§2.1, p.7, and §5.1.1, pp.27–28: `Π_𝕊 + Π_{𝕊^⊥} = I`).

**Formalization Note** Mathlib's `Submodule.starProjection`; `𝕊` is finite-dimensional because it
has the orthonormal basis `φ`, which supplies the instance. -/
noncomputable def projS {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) : X →L[ℝ] X :=
  haveI : FiniteDimensional ℝ S := φ.toBasis.finiteDimensional_of_finite
  S.starProjection

/-- **`L_{𝕊,𝕊} = Π_𝕊 L Π_𝕊`** (arXiv:2012.05299v1, §5.1.1, p.28). -/
noncomputable def LSS {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) : X →L[ℝ] X :=
  projS φ * L * projS φ

/-- **`L_{𝕊,⊥} = Π_𝕊 L Π_{𝕊^⊥}`** (arXiv:2012.05299v1, §5.1.1, p.28), with `Π_{𝕊^⊥} = I − Π_𝕊`. -/
noncomputable def LSperp {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) : X →L[ℝ] X :=
  projS φ * L * (1 - projS φ)

end ProjFPOracle


