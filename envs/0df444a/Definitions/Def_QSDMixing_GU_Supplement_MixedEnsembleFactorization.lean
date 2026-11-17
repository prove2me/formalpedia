-- Prove2me | Definitions.Def_QSDMixing_GU_Supplement_MixedEnsembleFactorization
-- name    : QSDMixing_GU_Supplement_MixedEnsembleFactorization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:40:31.92196+00:00
-- url     : https://prove2.me/theorems/f3307fbe-5209-4632-84ed-e6757ade3919
-- title:
--   Block Gram matrices, quantum weak mixing, and stabilized contraction
-- statement:
--   A finite-dimensional uniform mixed-state ensemble is presented by density operators $\rho_i=S_iS_i^\dagger$. Its $t$-copy **block Gram matrix** is
--
--   $$
--   X_t=\bigl[(S_i^\dagger S_j)^{\otimes t}\bigr]_{i,j},
--   $$
--
--   and block pinching $\Delta_t$ retains exactly the diagonal blocks. The quantum weak mixing time is the least $t\ge1$ for which $\|X_t-\Delta_t(X_t)\|_1/|I|$ is at most the requested tolerance.
--
--   The file also defines the inhomogeneous channel $\Phi_t=\mathcal N_t\circ\cdots\circ\mathcal N_1$ directly on matrices, its stabilization by every finite ancillary system, the trace-norm contraction $\eta(\Phi_t)$ on Hermitian inputs with zero diagonal blocks, and
--
--   $$
--   \widetilde\kappa_{\mathrm{gen}}=1-\sup_{s\ge1}\frac{1-\eta(\Phi_s)}s.
--   $$
--
--   These are the objects used in Theorems 7 and 8; this mixing time is distinct from the GU-only mixing time in the base mission.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §5, pp.30–33, eqs. (159)–(165), (181)–(184)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QSDMixing_GU_MixedState

set_option autoImplicit false
open Matrix
open scoped MatrixOrder

namespace QSDMixing.GU.Supplement

noncomputable local instance mixedWeakMixingDecidableEq {α : Type} : DecidableEq α :=
  Classical.decEq α

/-- The density matrix presented by the base mission's countable-mixture representation. -/
noncomputable def mixedStateMatrix {d : ℕ} (ρ : QSDMixing.GU.MixedState (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∑' a, (ρ.w a : ℂ) * ρ.v a i * starRingEnd ℂ (ρ.v a j)

/-- A finite-dimensional uniform mixed-state ensemble together with square factors
`ρᵢ=SᵢSᵢ†`. Square roots show that this loses no finite-dimensional state. -/
structure MixedEnsembleFactorization (I : Type) [Fintype I] (d : ℕ) where
  state : I → QSDMixing.GU.MixedState (Fin d)
  factor : I → Matrix (Fin d) (Fin d) ℂ
  factorizes : ∀ i, mixedStateMatrix (state i) = factor i * (factor i)ᴴ

/-- The ordinary matrix tensor power, indexed by `Fin t → Fin d`. -/
noncomputable def matrixTensorPower {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (t : ℕ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  fun x y => ∏ k, A (x k) (y k)

/-- The block Gram matrix `X_t=[(Sᵢ†Sⱼ)^{⊗t}]_{i,j}` from (159). -/
noncomputable def blockGram {I : Type} [Fintype I] {d : ℕ}
    (E : MixedEnsembleFactorization I d) (t : ℕ) :
    Matrix (I × (Fin t → Fin d)) (I × (Fin t → Fin d)) ℂ :=
  fun x y => matrixTensorPower ((E.factor x.1)ᴴ * E.factor y.1) t x.2 y.2

/-- Block pinching: retain exactly the diagonal `i=j` blocks. -/
noncomputable def blockPinch {I J : Type} [DecidableEq I] (X : Matrix (I × J) (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun x y => if x.1 = y.1 then X x y else 0

/-- The quantum weak mixing time (160), distinct from the base mission's GU `tMin`. -/
noncomputable def mixedWeakMixingTime {I : Type} [Fintype I] [Nonempty I] {d : ℕ}
    (E : MixedEnsembleFactorization I d) (ε : ℝ) : ℕ∞ :=
  sInf {T : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ T = t ∧
    WildeQIT.traceNorm (blockGram E t - blockPinch (blockGram E t)) /
      (Fintype.card I : ℝ) ≤ ε}

/-- The stabilized channel `Φ_t ⊗ id_R`, written directly from the factors. The source channel
`Φ_t=N_t∘⋯∘N_1` has exactly this matrix action. -/
noncomputable def amplifiedPhi {I : Type} [Fintype I] {d : ℕ}
    (E : MixedEnsembleFactorization I d) (t r : ℕ)
    (X : Matrix (I × Fin r) (I × Fin r) ℂ) :
    Matrix ((I × (Fin t → Fin d)) × Fin r) ((I × (Fin t → Fin d)) × Fin r) ℂ :=
  fun a b => X (a.1.1, a.2) (b.1.1, b.2) *
    matrixTensorPower ((E.factor a.1.1)ᴴ * E.factor b.1.1) t a.1.2 b.1.2

/-- Hermitian matrices in the stabilized input space. -/
def IsHermitianBlock {I : Type} [Fintype I] (r : ℕ)
    (X : Matrix (I × Fin r) (I × Fin r) ℂ) : Prop :=
  Xᴴ = X

/-- The condition `(Δ⊗id_R)(X)=0`. -/
def HasZeroDiagonalBlocks {I : Type} [Fintype I] (r : ℕ)
    (X : Matrix (I × Fin r) (I × Fin r) ℂ) : Prop :=
  ∀ i a b, X (i, a) (i, b) = 0

/-- The stabilized Dobrushin coefficient `η(Φ_t)=sup_R κ̃(Φ_t⊗id_R)` from (181)--(183). -/
noncomputable def stabilizedDobrushin {I : Type} [Fintype I] {d : ℕ}
    (E : MixedEnsembleFactorization I d) (t : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ (r : ℕ) (X : Matrix (I × Fin r) (I × Fin r) ℂ),
    0 < r ∧ IsHermitianBlock r X ∧ HasZeroDiagonalBlocks r X ∧ X ≠ 0 ∧
      v = WildeQIT.traceNorm (amplifiedPhi E t r X) / WildeQIT.traceNorm X}

/-- The generalized stabilized coefficient
`κ̃_gen=1-sup_{s≥1}(1-η(Φ_s))/s` from (182). -/
noncomputable def stabilizedDobrushinGen {I : Type} [Fintype I] {d : ℕ}
    (E : MixedEnsembleFactorization I d) : ℝ :=
  1 - sSup {v : ℝ | ∃ s : ℕ, 1 ≤ s ∧
    v = (1 - stabilizedDobrushin E s) / (s : ℝ)}

end QSDMixing.GU.Supplement


