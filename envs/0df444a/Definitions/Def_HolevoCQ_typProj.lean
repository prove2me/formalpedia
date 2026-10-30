-- Prove2me | Definitions.Def_HolevoCQ_typProj
-- name    : HolevoCQ_typProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:38.984652+00:00
-- url     : https://prove2.me/theorems/efafd374-20b0-4153-b6dc-e106bd171cea
-- title:
--   Typical projector $P$ of $\bar S^{\otimes n}$ (eq. 6)
-- statement:
--   Let $\bar S=\sum_i\pi_iS_i$ and let $\lambda_J$, $J\in D^n$, be the eigenvalues of $\bar S^{\otimes n}$ with eigenvectors $e_J$. For $\delta>0$ the projector onto the typical subspace of $\bar S^{\otimes n}$ is
--
--   $$
--   P=\sum_{J\in B}|e_J\rangle\langle e_J|,\qquad B=\{J:\ 2^{-n[H(\bar S)+\delta]}<\lambda_J<2^{-n[H(\bar S)-\delta]}\}.
--   $$
--
--   **Formalization Note** `windowProj` of $\bar S^{\otimes n}$ with the open window; $H$ is the binary von Neumann entropy, $2^x$ is the real power.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (6), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_HolevoCQ_avgState
import Definitions.Def_HolevoCQ_windowProj

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (6), p.3: the spectral projector onto the typical subspace of
`S̄^{⊗n}`, `P = Σ_{J ∈ B} |e_J⟩⟨e_J|` with
`B = {J : 2^{−n[H(S̄)+δ]} < λ_J < 2^{−n[H(S̄)−δ]}}`, where `S̄ = Σ_i π_i S_i` and `λ_J` are the
eigenvalues of `S̄^{⊗n}`.

**Formalization Note.** `windowProj` of `S̄^{⊗n}` with the open window; `H` is the binary
`vnEntropy` and `2^x` is `Real.rpow`. -/
noncomputable def typProj {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (π : A → ℝ) (n : ℕ) (δ : ℝ) : Matrix (Fin n → D) (Fin n → D) ℂ :=
  windowProj (tensorPowMat (avgState S π) n)
    ((2 : ℝ) ^ (-((n : ℝ) * (vnEntropy (avgState S π) + δ))))
    ((2 : ℝ) ^ (-((n : ℝ) * (vnEntropy (avgState S π) - δ))))

end HolevoCQ


