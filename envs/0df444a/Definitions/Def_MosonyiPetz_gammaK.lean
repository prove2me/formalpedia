-- Prove2me | Definitions.Def_MosonyiPetz_gammaK
-- name    : MosonyiPetz_gammaK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:35.946006+00:00
-- url     : https://prove2.me/theorems/abb3d172-f522-4556-9698-3cdd09a5e185
-- title:
--   The unital map $\gamma_{\mathcal K}=\alpha\circ T^*$
-- statement:
--   For $T$ and $D_1$ as above, $\gamma_{\mathcal K}:\mathcal B(\mathcal K)\to\mathcal B(\mathcal K)$ is the composition
--
--   $$\gamma_{\mathcal K}(X)=\alpha\big(T^*(X)\big),$$
--
--   with $\alpha$ the map (5) and $T^*$ the Hilbert–Schmidt adjoint. Its fixed points form the algebra $\mathcal D_{\mathcal K}$, the algebra on which Theorem 1 is built.
--
--   **Formalization Note** $T^*$ is `channelAdjoint`.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_alpha

open scoped Matrix
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **The unital map γ_K := α ∘ T* : B(K) → B(K).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8: "that of γK := α◦T∗ be DK" (also p.5 for γ_H).

`gammaK T D₁ A = alpha T D₁ (channelAdjoint T A)`, with `T*` the Hilbert–Schmidt adjoint `channelAdjoint T` and `α` the
map (5) built from `D₁`.

**Formalization Note.** `T*` is the published `channelAdjoint` (Hilbert–Schmidt adjoint). -/
noncomputable def gammaK {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ) (A : Matrix K K ℂ) : Matrix K K ℂ :=
  alpha T D₁ (channelAdjoint T A)

end MosonyiPetz


