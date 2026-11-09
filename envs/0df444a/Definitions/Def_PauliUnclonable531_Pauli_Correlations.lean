-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Correlations
-- name    : PauliUnclonable531_Pauli_Correlations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:30.908063+00:00
-- url     : https://prove2.me/theorems/e22a44fc-2b08-40c3-8d78-b0ec88c5c741
-- title:
--   Decoder observables and averaged security operators
-- statement:
--   Decoder families Bₖ and Cₖ are arbitrary Hermitian contractions on finite registers B and C: −I≼Bₖ,Cₖ≼I. They need not be reflections. Let d=2ⁿ, K=4ⁿ−1, and Θₖ=Pₖᵀ with ordinary transpose. On A⊗(B⊗C), define
--
--   $$E_B=K^{-1}\sum_k\Theta_k\otimes B_k\otimes I,\quad E_C=K^{-1}\sum_k\Theta_k\otimes I\otimes C_k,\quad E_{BC}=K^{-1}\sum_k I\otimes B_k\otimes C_k,$$
--   $$D=I-E_{BC},\qquad G=\tfrac12(E_B+E_C-D),\qquad F(t)=2t(2tI+D)^{-1}.$$
--
--   The filter is used only for real t>0. Its positive-definiteness and cancellation laws are separate theorem obligations; D itself may have a kernel. No commutativity between E_B and E_C, no norm estimate, and no security conclusion occurs among the decoder assumptions. All tensor factors have a fixed right-associated A,B,C ordering.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Definitions 4.2–4.3, p.19, Eqs. (23)–(29); Definition 4.7, p.23, Eq. (33)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Game
import Definitions.Def_PauliUnclonable531_Pauli_Choi

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Arbitrary Hermitian contraction families of Definition 4.2. In particular, these
are not required to be reflections, and no spectral estimate is a field. -/
structure Decoders (n : ℕ) (B C : Type) [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] where
  bob : Key n → Op B
  charlie : Key n → Op C
  bob_hermitian : ∀ k, (bob k).IsHermitian
  charlie_hermitian : ∀ k, (charlie k).IsHermitian
  bob_lower : ∀ k, Below (-1) (bob k)
  bob_upper : ∀ k, Below (bob k) 1
  charlie_lower : ∀ k, Below (-1) (charlie k)
  charlie_upper : ∀ k, Below (charlie k) 1

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

noncomputable def EB (a : Decoders n B C) : Op (Bits n × (B × C)) :=
  (Fintype.card (Key n) : ℂ)⁻¹ • ∑ k : Key n,
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (a.bob k) (1 : Op C))

noncomputable def EC (a : Decoders n B C) : Op (Bits n × (B × C)) :=
  (Fintype.card (Key n) : ℂ)⁻¹ • ∑ k : Key n,
    Matrix.kronecker (pauli k.val).transpose (Matrix.kronecker (1 : Op B) (a.charlie k))

noncomputable def EBC (a : Decoders n B C) : Op (Bits n × (B × C)) :=
  (Fintype.card (Key n) : ℂ)⁻¹ • ∑ k : Key n,
    Matrix.kronecker (1 : Op (Bits n)) (Matrix.kronecker (a.bob k) (a.charlie k))

noncomputable def disagreement (a : Decoders n B C) := 1 - EBC a
noncomputable def gameOperator (a : Decoders n B C) :=
  (1/2 : ℂ) • (EB a + EC a - disagreement a)

/-- Total inverse; all uses in theorems have t>0, and invertibility is a proved obligation. -/
noncomputable def filterOperator (a : Decoders n B C) (t : ℝ) :=
  (2 * (t : ℂ)) • ((2 * (t : ℂ)) • (1 : Op (Bits n × (B × C))) + disagreement a)⁻¹

end PauliUnclonable531.Pauli


