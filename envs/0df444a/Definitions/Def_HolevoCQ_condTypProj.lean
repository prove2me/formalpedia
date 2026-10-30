-- Prove2me | Definitions.Def_HolevoCQ_condTypProj
-- name    : HolevoCQ_condTypProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:18.02113+00:00
-- url     : https://prove2.me/theorems/ec4f5983-6b9e-4cd0-ab75-ef403292153d
-- title:
--   Typical projector $P_u$ of $S_u$ (eq. 8)
-- statement:
--   Let $\lambda^u_J$ be the eigenvalues of the word state $S_u$ with eigenvectors $e^u_J$, and let $\bar H(S_{(\cdot)})=\sum_i\pi_iH(S_i)$. For $\delta>0$ the projector onto the typical subspace of $S_u$ is
--
--   $$
--   P_u=\sum_{J\in B_u}|e^u_J\rangle\langle e^u_J|,\qquad B_u=\{J:\ 2^{-n[\bar H(S_{(\cdot)})+\delta]}<\lambda^u_J<2^{-n[\bar H(S_{(\cdot)})-\delta]}\}.
--   $$
--
--   The window is centred on the mean entropy $\sum_i\pi_iH(S_i)$, not on $H(S_u)/n$.
--
--   **Formalization Note** `windowProj` of $S_u$ with the open window; $H$ is the binary von Neumann entropy.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (8), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_windowProj

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (8), p.4: the spectral projector onto the typical subspace of
`S_u`, `P_u = Σ_{J ∈ B_u} |e^u_J⟩⟨e^u_J|` with
`B_u = {J : 2^{−n[H̄(S(·))+δ]} < λ^u_J < 2^{−n[H̄(S(·))−δ]}}`, where
`H̄(S(·)) = Σ_i π_i H(S_i)` and `λ^u_J` are the eigenvalues of `S_u`.

**Formalization Note.** `windowProj` of `wordState S n u` with the open window centred on the
mean entropy `Σ_i π_i H(S_i)` (not on `H(S_u)/n`); `H` is the binary `vnEntropy`, `2^x` is
`Real.rpow`. -/
noncomputable def condTypProj {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (π : A → ℝ) (n : ℕ) (δ : ℝ) (u : Fin n → A) :
    Matrix (Fin n → D) (Fin n → D) ℂ :=
  windowProj (wordState S n u)
    ((2 : ℝ) ^ (-((n : ℝ) * (∑ i, π i * vnEntropy (S i) + δ))))
    ((2 : ℝ) ^ (-((n : ℝ) * (∑ i, π i * vnEntropy (S i) - δ))))

end HolevoCQ


