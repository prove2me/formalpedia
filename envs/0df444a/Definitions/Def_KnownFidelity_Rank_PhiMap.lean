-- Prove2me | Definitions.Def_KnownFidelity_Rank_PhiMap
-- name    : KnownFidelity_Rank_PhiMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:57.456551+00:00
-- url     : https://prove2.me/theorems/7c053889-8640-4969-b876-a86907cb9155
-- title:
--   The embedding channel $\Phi(X)=LXL^*+\mathrm{tr}((I_J-L^*L)X)\,|f\rangle\langle f|$ of §4.1
-- statement:
--   With $\sigma=U\,\mathrm{diag}(\lambda)\,U^*$, the eigenvectors in $J$ form the isometry $V=(Ue_{J(i)})_i:\mathbb C^j\to\mathbb C^d$, and $|f\rangle=Ue_f$ is an eigenvector orthogonal to $J$. The map
--
--   $$\Phi(X)=V\,(LXL^*)\,V^*+\mathrm{tr}\big((I_J-L^*L)X\big)\,|f\rangle\langle f|$$
--
--   sends operators on $\mathbb C^j$ to operators on $\mathbb C^d$; it is completely positive and trace preserving because $L^*L\preceq I_J$. It embeds the hard instances for the maximally mixed reference into a spectral subspace of $\sigma$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §4.1 (unnumbered display), p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_Lmat

open scoped Matrix

namespace KnownFidelity.Rank

/-- **The embedding channel `Φ` of §4.1.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §4.1 (unnumbered display), printed p. 8 (PDF p. 10): "Since L*L ⪯ I_J, the map
Φ(X) = LXL* + tr((I_J − L*L)X)|f⟩⟨f| is completely positive and trace preserving."

With `σ = U diag(λ) U*`, the eigenvectors in `J` are the columns `V = (U e_{J i})_i` and the
eigenvector `f` is `|f⟩ = U e_f`; on `X ∈ ℂ^{j×j}`,
`PhiMap U lam J f ℓ X = V (L X L*) V* + tr((I − L* L) X) |f⟩⟨f|`, an operator on `ℂ^d`.

**Formalization Note.** "Identify C^j with J" is the isometry `V : ℂ^j → ℂ^d` given by the
columns of `U` indexed by `J`; `L` is `Lmat lam J ℓ`. -/
noncomputable def PhiMap {d j : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (J : Fin j ↪ Fin d) (f : Fin d) (ℓ : ℝ) (X : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let V : Matrix (Fin d) (Fin j) ℂ := Matrix.of fun a i => U a (J i)
  let fv : Fin d → ℂ := fun a => U a f
  let L := Lmat lam J ℓ
  V * (L * X * Lᴴ) * Vᴴ + ((1 - Lᴴ * L) * X).trace • Matrix.vecMulVec fv (star fv)

end KnownFidelity.Rank


