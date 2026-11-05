-- Prove2me | Definitions.Def_MosonyiPetz_gammaH
-- name    : MosonyiPetz_gammaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:36.285491+00:00
-- url     : https://prove2.me/theorems/53715e34-8363-41a3-bbf3-d9687de086a4
-- title:
--   The unital map $\gamma_{\mathcal H}=T^*\circ\alpha$
-- statement:
--   For $T$ and $D_1$ as above, $\gamma_{\mathcal H}:\mathcal B(\mathcal H)\to\mathcal B(\mathcal H)$ is the composition
--
--   $$\gamma_{\mathcal H}(A)=T^*\big(\alpha(A)\big),$$
--
--   with $\alpha$ the map (5) and $T^*$ the Hilbert–Schmidt adjoint. It is $(T^\#T)^*$ (p.5); its fixed points form the algebra $\mathcal D_{\mathcal H}$.
--
--   **Formalization Note** $T^*$ is `channelAdjoint`.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, p.5 and §4, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_alpha

open scoped Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **The unital map γ_H := T* ∘ α : B(H) → B(H).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8: "Let the fixed point algebra of γH := T∗◦α be DH" (also p.5 for γ_H).

`gammaH T D₁ A = channelAdjoint T (alpha T D₁ A)`, with `T*` the Hilbert–Schmidt adjoint `channelAdjoint T` and `α` the
map (5) built from `D₁`.

**Formalization Note.** `T*` is the published `channelAdjoint` (Hilbert–Schmidt adjoint). -/
noncomputable def gammaH {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ) (A : Matrix H H ℂ) : Matrix H H ℂ :=
  channelAdjoint T (alpha T D₁ A)

end MosonyiPetz


