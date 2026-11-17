-- Prove2me | Definitions.Def_BSCvsBEC_Supplement_pErr
-- name    : BSCvsBEC_Supplement_pErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:09.255661+00:00
-- url     : https://prove2.me/theorems/1775b04e-0aa6-4b48-938a-3d5248c43add
-- title:
--   Optimal guessing probability $P_{\mathrm{guess}}$, decoding error $P_e$, and $\mathrm{BEC}_\lambda$ as a cq channel
-- statement:
--   A **POVM** with outcomes in a finite set $L$ on $\mathbb C^\kappa$ is a family $(M_x)_{x\in L}$ of positive semidefinite matrices with $\sum_xM_x=I$.
--
--   Let $X$ be a random variable on $L$ with pmf $P$, sent through a (possibly classical–quantum) channel that outputs the state $\sigma_x$ on input $x$. The **optimal guessing probability** and the **error probability of optimal decoding** are
--   $$P_{\mathrm{guess}}(W,P)=\max_{\text{POVM }(M_x)_x}\sum_xP(x)\,\mathrm{Tr}(M_x\sigma_x),\qquad P_e(W,P)=1-P_{\mathrm{guess}}(W,P).$$
--
--   The binary erasure channel $\mathrm{BEC}_\lambda$ on $\mathbb F_2^n$ is treated as the cq channel with diagonal output states $\sigma_x=\mathrm{diag}\big(\prod_iW(y_i\mid x_i)\big)_{y\in(\mathbb F_2\cup\{?\})^n}$, with $W(x\mid x)=1-\lambda$ and $W(?\mid x)=\lambda$; for these states $P_{\mathrm{guess}}$ is the success probability of MAP decoding.
--
--   These quantities are compared between $\mathrm{PSC}_\theta$ and $\mathrm{BEC}_\lambda$ in §3.
--
--   **Formalization Note** $P_{\mathrm{guess}}$ is the published `DIObliviousTransfer.pGuess` (the supremum over every POVM with outcomes in $L$) applied to the cq blocks $P(x)\sigma_x$. For a pmf and density matrices the set of values is nonempty and bounded by $1$, so the supremum is the true one (and it is attained). $\mathrm{Tr}(M_x\sigma_x)$ is real for positive semidefinite matrices; its real part is taken. The erasure symbol $?$ is `none`.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, eqs. (16)–(17), p.6 (P_guess, P_e); §2.1, p.5 (BEC_λ)

import Mathlib
import Definitions.Def_DIObliviousTransfer_pGuess
import Definitions.Def_BSCvsBEC_condEntBEC

namespace BSCvsBEC.Supplement

/-- The optimal guessing probability `P_guess(W, P_X) = max_{POVM (M_x)} ∑ₓ P_X(x) Tr(M_x σ_x)` of an
input `X` with pmf `P`, sent through a (possibly classical–quantum) channel with output states `σ_x`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), eqs. (16)–(17), p.6.

**Formalization Note.** This is the published `DIObliviousTransfer.pGuess` (the supremum over every
POVM with outcomes in the input alphabet of `Re ∑ₓ Tr(M_x ρ_x)`) applied to the cq blocks
`ρ_x = P(x) σ_x`, so `Tr(M_x ρ_x) = P(x) Tr(M_x σ_x)`. For a pmf `P` and density matrices `σ_x` the set
of values is nonempty (`M_{x₀} = I`, the other `M_x = 0`) and bounded above by `1`, so the supremum is
the true one (attained by compactness). A classical channel `W` is the cq channel with diagonal
states `σ_x = diag(W(· | x))`, for which this is MAP decoding. -/
noncomputable def pGuess {L κ : Type} [Fintype L] [Fintype κ] [DecidableEq κ]
    (P : L → ℝ) (σ : L → Matrix κ κ ℂ) : ℝ :=
  DIObliviousTransfer.pGuess (fun x => ((P x : ℝ) : ℂ) • σ x)

/-- The error probability of optimal decoding, `P_e(W, P_X) = 1 − P_guess(W, P_X)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), p.6 ("We define the error
probability of optimal decoding (MAP decoding, in the classical case) to be
`P_e(W, P_X) = 1 − P_guess(W, P_X)`"). -/
noncomputable def pErr {L κ : Type} [Fintype L] [Fintype κ] [DecidableEq κ]
    (P : L → ℝ) (σ : L → Matrix κ κ ℂ) : ℝ :=
  1 - pGuess P σ

/-- The `n`-fold binary erasure channel `BEC_λ` as a classical–quantum channel: the input
`x ∈ F₂ⁿ` goes to the diagonal state `diag(∏ᵢ W(yᵢ | xᵢ))` over outputs `y ∈ (F₂ ∪ {?})ⁿ`, with the
published one-symbol kernel `BSCvsBEC.becKernel` (`W(x|x) = 1 − λ`, `W(?|x) = λ`).
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5 (`BEC_λ`) and p.6
("the (possibly classical) joint state … `σ_x`").

**Formalization Note.** `F₂ = Fin 2`, the erasure symbol `?` is `none : Option (Fin 2)`. With these
diagonal states, `pGuess` is the success probability of MAP decoding. -/
noncomputable def becState (lam : ℝ) {n : ℕ} (x : Fin n → Fin 2) :
    Matrix (Fin n → Option (Fin 2)) (Fin n → Option (Fin 2)) ℂ :=
  Matrix.diagonal (fun y => ((∏ i, BSCvsBEC.becKernel lam (x i) (y i) : ℝ) : ℂ))

end BSCvsBEC.Supplement


