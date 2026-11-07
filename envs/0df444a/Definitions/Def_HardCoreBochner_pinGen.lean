-- Prove2me | Definitions.Def_HardCoreBochner_pinGen
-- name    : HardCoreBochner_pinGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:31:15.332238+00:00
-- url     : https://prove2.me/theorems/601a5638-5f1a-4ada-8aa9-cef4d6dfca06
-- title:
--   Generator $L^{(v)}$ of the pinned family
-- statement:
--   Fix $v\in V$. The pinned family is $X^{(v)}=\{\sigma\subseteq V\setminus\{v\}:\sigma\cup\{v\}\in X\}$. Its Glauber generator acts on $h:\{0,1\}^V\to\mathbb R$ by
--   $$(L^{(v)}h)(\sigma)=\sum_{u\in V\setminus\{v\}}\big(r_u(\sigma\cup\{v\})\,D^+_u h(\sigma)+D^-_u h(\sigma)\big),$$
--   with the rates $r_u$ of the original distribution $\mu$ evaluated at $\sigma\cup\{v\}$. It is the generator of continuous-time Glauber dynamics for the conditioned measure $\mu^{(v)}(\sigma)\propto\mu(\sigma\cup\{v\})$ on $X^{(v)}$, and it appears in the commutator identity (Lemma 2.2).
--
--   **Formalization Note** Defined by the printed formula at every configuration.
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), §2, p.7 (PDF p.7)

import Definitions.Def_HardCoreBochner_rate
import Definitions.Def_HardCoreBochner_Dplus

namespace HardCoreBochner

open scoped BigOperators

/-- The **Glauber generator of the pinned family** `L^(v)`. Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), §2, p.7:
`(L(v)h)(σ) := Σ_{u∈V\{v}} ( r_u(σ ∪ {v}) D⁺_u h(σ) + D⁻_u h(σ) )`.

**Formalization Note** Stated by the printed formula, with the rates `r_u` of the original `µ`
evaluated at `σ ∪ {v}` (= `Function.update σ v true`); `V \ {v}` is `Finset.univ.erase v`. -/
noncomputable def pinGen {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (v : V)
    (h : (V → Bool) → ℝ) (σ : V → Bool) : ℝ :=
  ∑ u ∈ Finset.univ.erase v,
    (rate μ u (Function.update σ v true) * Dplus u h σ + Dminus u h σ)

end HardCoreBochner


