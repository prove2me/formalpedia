-- Prove2me | Definitions.Def_PRUPermLayer_noPlusSub
-- name    : PRUPermLayer_noPlusSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:03.314077+00:00
-- url     : https://prove2.me/theorems/19990220-d6f9-469a-b81f-df8817374202
-- title:
--   Non-plussed subspace $\mathrm{NoPlus}_{N,t}$
-- statement:
--   The **non-plussed subspace** $\mathrm{NoPlus}_{N,t} \subseteq (\mathbb C^N)^{\otimes t}$ is the range of $(I - |+_N\rangle\langle +_N|)^{\otimes t}$: the states orthogonal to $|+_N\rangle$ in every register.
--
--   **Formalization Note** The tensor power is the published one, indexed by $t$-tuples of labels.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PRUPermLayer_plusProj

namespace PRUPermLayer

/-- The non-plussed subspace `NoPlus_{N,t}`, the range of `(I − |+_N⟩⟨+_N|)^{⊗t}`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)).

**Formalization Note** The tensor power is the published
`ShadowTomography.UpperBound.tensorPow`, indexed by `Fin t → Fin N`. -/
noncomputable def noPlusSub (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin t → Fin N)) :=
  LinearMap.range
    (Matrix.toEuclideanLin (ShadowTomography.UpperBound.tensorPow (1 - plusProj N) t))

end PRUPermLayer


