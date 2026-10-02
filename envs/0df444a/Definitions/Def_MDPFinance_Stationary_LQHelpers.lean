-- Prove2me | Definitions.Def_MDPFinance_Stationary_LQHelpers
-- name    : MDPFinance_Stationary_LQHelpers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:25.343901+00:00
-- url     : https://prove2.me/theorems/0b254028-f959-4bcc-b330-3dde74c7845f
-- title:
--   Quadratic forms and matrix-valued expectations for the LQ example
-- statement:
--   For a symmetric matrix $Q$ and vector $x$, $x^\top Q x$ is `xQx Q x`. For a jointly
--   distributed random pair $(A,B) \sim \nu$ and a matrix-valued function $F$, `jointMatMean ν F`
--   is $\mathbb{E}[F(A,B)]$, computed entrywise.
--
--   **Formalization Note.** Mathlib has no `MeasurableSpace` instance for `Matrix m n α`
--   (`Matrix` is a non-reducible `def` for `m → n → α`); `instMeasurableSpaceMatrix` transports
--   the product `MeasurableSpace` structure across this definitional equality so that a *law* of
--   a random matrix is an ordinary `Measure`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 51-52, PDF 66-67, §2.6.3 (notation used without a separate numbered definition)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_NSValueFunction

open MeasureTheory

namespace MDPFinance.Stationary

/-- Mathlib has no `MeasurableSpace (Matrix m n α)` instance (`Matrix` is a plain, non-reducible
`def` for `m → n → α`); this transports the product `MeasurableSpace` structure across that
definitional equality, needed so a *law* of a random matrix (Bäuerle–Rieder's random transition
coefficients `A_{n+1}, B_{n+1}`, §2.6.3) is a `Measure` on a genuine measurable space. -/
instance instMeasurableSpaceMatrix {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))

/-- The quadratic form `x^⊤ Q x` for a square matrix `Q` and a vector `x` (Bäuerle–Rieder use
`x^⊤ Q x` throughout §2.6.3 without a separate numbered definition). -/
def xQx {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  dotProduct x (Q.mulVec x)

/-- The matrix-valued expectation `𝔼[F(A,B)]`, computed entrywise, of a matrix-valued function
of a jointly-distributed random pair `(A,B) ∼ ν` (Bäuerle–Rieder write `𝔼[A_{n+1}^⊤ Q A_{n+1}]`
etc. throughout §2.6.3 without a separate numbered notation for this expectation operator). -/
noncomputable def jointMatMean {m d : Type*} [Fintype m] [Fintype d] {κ₁ κ₂ : Type*}
    [Fintype κ₁] [Fintype κ₂]
    (ν : Measure (Matrix m m ℝ × Matrix m d ℝ))
    (F : Matrix m m ℝ → Matrix m d ℝ → Matrix κ₁ κ₂ ℝ) : Matrix κ₁ κ₂ ℝ :=
  fun i j => ∫ p, F p.1 p.2 i j ∂ν

end MDPFinance.Stationary


