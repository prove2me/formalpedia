-- Prove2me | Definitions.Def_HardCoreBochner_gen
-- name    : HardCoreBochner_gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:19.336687+00:00
-- url     : https://prove2.me/theorems/99878ac1-1ed7-46ad-9c75-f2275e968faa
-- title:
--   Generator $L$ of continuous-time Glauber dynamics
-- statement:
--   For a distribution $\mu$ with jump rates $r_v$, the **continuous-time Glauber dynamics** has generator
--   $$(Lf)(\sigma)=\sum_{v\in V}\big(r_v(\sigma)\,(D^+_v f)(\sigma)+(D^-_v f)(\sigma)\big).$$
--   In words: at a configuration $\sigma\in X$ each occupied $v\in\sigma$ is removed at rate $1$, and each unoccupied $v\notin\sigma$ is added at rate $r_v(\sigma)$. The dynamics is reversible for $\mu$.
--
--   **Formalization Note** $Lf$ is defined at every configuration; only its values on the support of $\mu$ enter the inner products.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.3 (PDF p.3)

import Definitions.Def_HardCoreBochner_rate
import Definitions.Def_HardCoreBochner_Dplus

namespace HardCoreBochner

open scoped BigOperators

/-- The **generator of continuous-time Glauber dynamics**. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3:
`(Lf)(σ) = Σ_{v∈V} ( r_v(σ)(D⁺_v f)(σ) + (D⁻_v f)(σ) )`.

Each occupied `v ∈ σ` dies at rate `1` and each unoccupied `v ∉ σ` is born at rate `r_v(σ)`.

**Formalization Note** Defined for every `σ : V → Bool`; only its values on the support of `µ`
enter the inner products. -/
noncomputable def gen {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (f : (V → Bool) → ℝ) (σ : V → Bool) : ℝ :=
  ∑ v, (rate μ v σ * Dplus v f σ + Dminus v f σ)

end HardCoreBochner


