-- Prove2me | Definitions.Def_ConstDepthUnitary_QHat
-- name    : ConstDepthUnitary_QHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:09.980573+00:00
-- url     : https://prove2.me/theorems/dacec44b-60bc-4b31-a520-8e131d030c5b
-- title:
--   The quadratic-phase oracle $\hat Q_S$
-- statement:
--   For a real matrix $S$, the diagonal unitary on $[K]^N$
--   $$\hat Q_S:\ |v\rangle\mapsto e^{\frac12 i\,\alpha(v)^{\mathsf T}S\,\alpha(v)}|v\rangle.$$
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.3, Eq. (51), p.24

import Mathlib
import Definitions.Def_ConstDepthUnitary_alpha

namespace ConstDepthUnitary

/-- The real number `α(v)ᵀ S α(v)`. -/
noncomputable def quadForm {N : ℕ} (K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → Fin K) : ℝ :=
  alphaVec K v ⬝ᵥ S.mulVec (alphaVec K v)

/-- The diagonal quadratic-phase oracle `Q̂_S : |v⟩ ↦ e^{½ i α(v)ᵀ S α(v)} |v⟩`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Eq. (51), p.24. -/
noncomputable def QHat {N : ℕ} (K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N → Fin K) (Fin N → Fin K) ℂ :=
  Matrix.diagonal fun v => Complex.exp ((1 / 2 : ℂ) * Complex.I * (quadForm K S v : ℂ))

end ConstDepthUnitary


