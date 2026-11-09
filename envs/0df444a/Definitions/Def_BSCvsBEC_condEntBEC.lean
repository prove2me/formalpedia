-- Prove2me | Definitions.Def_BSCvsBEC_condEntBEC
-- name    : BSCvsBEC_condEntBEC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:33:24.788071+00:00
-- url     : https://prove2.me/theorems/0474554d-c364-4b9e-ab12-4e82f31d849a
-- title:
--   Binary erasure channel $\mathrm{BEC}_\lambda$ and $H(X\mid \mathrm{BEC}_\lambda(X))$
-- statement:
--   The **binary erasure channel** $\mathrm{BEC}_\lambda$ with erasure probability $\lambda$ has input alphabet $\mathbb F_2$ and output alphabet $\mathbb F_2\cup\{?\}$, with transition probabilities $W(x\mid x)=1-\lambda$ and $W(?\mid x)=\lambda$. On a word $x=(x_1,\dots,x_n)\in\mathbb F_2^n$ it acts on each coordinate independently.
--
--   For a random $X\in\mathbb F_2^n$ with pmf $P$ and $Y=\mathrm{BEC}_\lambda(X)$, the joint pmf is
--   $$P_{XY}(x,y)=P(x)\prod_{i=1}^n W(y_i\mid x_i),$$
--   $P_Y$ is its marginal on the output, and the **conditional entropy** is
--   $$H(X\mid \mathrm{BEC}_\lambda(X)) := H(XY)-H(Y)$$
--   in bits.
--
--   This is the classical side of the paper's channel comparison (Theorem 1.3).
--
--   **Formalization Note** The erasure symbol $?$ is `none : Option (Fin 2)`. The conditional entropy is defined from the joint distribution, not from the formula $H(X)-\mathbb E_{R\sim 1-\lambda}H(X_R)$; that identity is a separate milestone.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, p.5 (erasure channel, coordinatewise action); p.6 (H(X|Y) := H(XY) − H(Y))

import Mathlib
import Definitions.Def_BSCvsBEC_shannon

namespace BSCvsBEC

/-- The binary erasure channel `BEC_λ` on one symbol: `W(x|x) = 1 − λ`, `W(?|x) = λ`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5.

**Formalization Note.** `F₂ = Fin 2`; the output alphabet `F₂ ∪ {?}` is `Option (Fin 2)`, with the
erasure symbol `?` as `none`. -/
noncomputable def becKernel (lam : ℝ) (x : Fin 2) : Option (Fin 2) → ℝ
  | none => lam
  | some y => if y = x then 1 - lam else 0

/-- The joint pmf of `(X, BEC_λ(X))` for a random `X ∈ F₂ⁿ` with pmf `P`, the channel applied to each
coordinate independently: `P(x) ∏ᵢ W(yᵢ | xᵢ)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5: "When sending
`x = (x₁, …, xₙ) ∈ Ωⁿ`, a given channel is applied to each coordinate independently." -/
noncomputable def becJoint (lam : ℝ) {n : ℕ} (P : (Fin n → Fin 2) → ℝ) :
    (Fin n → Fin 2) × (Fin n → Option (Fin 2)) → ℝ :=
  fun xy => P xy.1 * ∏ i, becKernel lam (xy.1 i) (xy.2 i)

/-- The output pmf of `BEC_λ(X)`: the marginal of `becJoint` on the output. -/
noncomputable def becOut (lam : ℝ) {n : ℕ} (P : (Fin n → Fin 2) → ℝ) :
    (Fin n → Option (Fin 2)) → ℝ :=
  fun y => ∑ x, becJoint lam P (x, y)

/-- The conditional entropy `H(X | BEC_λ(X)) := H(X, Y) − H(Y)` (bits), `Y = BEC_λ(X)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.6: "the standard
conditional Shannon/von Neumann entropy, `H(X|Y) := H(XY) − H(Y)` defined for a joint distribution
`P_XY`".

**Formalization Note.** Defined from the joint pmf on `F₂ⁿ × (F₂ ∪ {?})ⁿ`, not from the formula
`H(X) − E_{R∼1−λ} H(X_R)` (that identity is a milestone). -/
noncomputable def condEntBEC (lam : ℝ) {n : ℕ} (P : (Fin n → Fin 2) → ℝ) : ℝ :=
  shannon (becJoint lam P) - shannon (becOut lam P)

end BSCvsBEC


