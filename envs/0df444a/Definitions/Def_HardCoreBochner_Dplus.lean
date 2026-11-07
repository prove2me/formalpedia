-- Prove2me | Definitions.Def_HardCoreBochner_Dplus
-- name    : HardCoreBochner_Dplus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:10.621207+00:00
-- url     : https://prove2.me/theorems/58eff1c6-77e9-4954-a921-3a99c5db4fe4
-- title:
--   Discrete derivatives $D^+_v$ and $D^-_v$
-- statement:
--   For $v\in V$, a configuration $\sigma\in\{0,1\}^V$ and $f:\{0,1\}^V\to\mathbb R$,
--   $$(D^-_v f)(\sigma)=f(\sigma\setminus\{v\})-f(\sigma),\qquad (D^+_v f)(\sigma)=f(\sigma\cup\{v\})-f(\sigma).$$
--   They measure the change of $f$ when $v$ is removed from, or added to, the configuration, and are the building blocks of the generator $L$.
--
--   **Formalization Note** $\sigma\cup\{v\}$ and $\sigma\setminus\{v\}$ are `Function.update σ v true` and `Function.update σ v false`; both operators are defined at every configuration.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §1, p.3 (PDF p.3)

import Mathlib

namespace HardCoreBochner

/-- The discrete derivative `(D⁺_v f)(σ) = f(σ ∪ {v}) − f(σ)`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3.

**Formalization Note** `σ ∪ {v}` is `Function.update σ v true`. Defined for every `σ : V → Bool`. -/
def Dplus {V : Type*} [DecidableEq V] (v : V) (f : (V → Bool) → ℝ) (σ : V → Bool) : ℝ :=
  f (Function.update σ v true) - f σ

/-- The discrete derivative `(D⁻_v f)(σ) = f(σ \ {v}) − f(σ)`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §1, p.3.

**Formalization Note** `σ \ {v}` is `Function.update σ v false`. -/
def Dminus {V : Type*} [DecidableEq V] (v : V) (f : (V → Bool) → ℝ) (σ : V → Bool) : ℝ :=
  f (Function.update σ v false) - f σ

end HardCoreBochner


