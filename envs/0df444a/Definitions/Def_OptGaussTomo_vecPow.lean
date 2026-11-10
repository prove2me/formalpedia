-- Prove2me | Definitions.Def_OptGaussTomo_vecPow
-- name    : OptGaussTomo_vecPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:34.469259+00:00
-- url     : https://prove2.me/theorems/62dbffa4-60db-4f81-a805-3d84ad005265
-- title:
--   $n$-fold tensor power $\psi^{\otimes n}$ of a vector
-- statement:
--   Let $\mathcal H=\ell^2(I)$ have the orthonormal basis indexed by $I$. The $n$-fold tensor power $\mathcal H^{\otimes n}$ has the basis indexed by $x:\{1,\dots,n\}\to I$ (copy $t$ carries the label $x_t$), and a vector $v$ has the tensor power
--
--   $$
--   (v^{\otimes n})_x=\prod_{t=1}^n v_{x_t}.
--   $$
--
--   These are the $n$-copy pure states $|\psi\rangle^{\otimes n}$ spanning the spaces $\mathcal V^\pm_{n,m}$ of Lemma C.4.
--
--   **Formalization Note** It matches the published operator tensor power `WildeQIT.Schumacher.tensorPow` (same basis of $\mathcal H^{\otimes n}$). For $n=0$ it is the constant $1$ on the one-point basis. The published `ArgmaxDeFinetti.tensorPow` is the same construction for the index type `Fin d` only, which does not cover the qubit labels used here.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.3 p.37 (pdf p.37), definition of V±_{n,m}; n-copy states throughout App. C–D

import Mathlib

namespace OptGaussTomo

/-!
# n-fold tensor powers of vectors, `ψ^{⊗n}`

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.3, p.37 ("let
`V^±_{n,m}` denote the span of `|ψ⟩^{⊗n}` for `|ψ⟩ ∈ G^±_m`") and the `n`-copy pure states used in
§§C.3–C.5 and D.7.

**Formalization Note.** For a vector `v` on the basis `I`, `v^{⊗n}` has coefficients
`∏ₜ v (x t)` on the basis `Fin n → I` of the `n`-fold tensor power (copy `t` carries the label
`x t`), matching the operator tensor power `WildeQIT.Schumacher.tensorPow`. For `n = 0` it is the
constant `1` on the one-point index set. The published `ArgmaxDeFinetti.tensorPow` is the same
construction for the index type `Fin d` only, so it does not apply to `Qubits m`.
-/

/-- The coefficients of the vector `v^{⊗n}` on the basis `Fin n → I`. -/
def vecPow {I : Type} (n : ℕ) (v : I → ℂ) : (Fin n → I) → ℂ :=
  fun x => ∏ t, v (x t)

end OptGaussTomo


