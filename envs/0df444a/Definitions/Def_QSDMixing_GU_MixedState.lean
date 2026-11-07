-- Prove2me | Definitions.Def_QSDMixing_GU_MixedState
-- name    : QSDMixing_GU_MixedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:22.401807+00:00
-- url     : https://prove2.me/theorems/24dffcf4-0e92-464b-b05e-463f2c75c7f7
-- title:
--   A density operator on $\ell^2(\iota)$ as a countable mixture
-- statement:
--   A density operator on $\ell^2(\iota)$ presented as a countable mixture
--
--   $$
--   \rho=\sum_{a\in\mathbb N}w_a\,|v_a\rangle\langle v_a|,
--   $$
--
--   with weights $w_a\ge0$ summing to $1$ and unit vectors $v_a$. The file also defines the pure state $|\psi\rangle\langle\psi|$ as the mixture with weight $1$ at index $0$.
--
--   The spectral theorem gives every density operator this form, so no instance is lost.
--
--   **Formalization Note** Presenting states as mixtures avoids a trace-class layer. Several mixtures present one operator, and the quantities built on them depend only on the operator.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §1.1, p.3; §2.1, p.12

import Mathlib
import Definitions.Def_GaussTesting_Ell2

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- A density operator on `ℓ²(ι)`, presented as a countable mixture `ρ = Σ_a w_a |v_a⟩⟨v_a|` of unit
vectors with probability weights.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §1.1, p.3, and §2.1, p.12: the states `ρ_i` of an ensemble.

**Formalization Note.** The spectral theorem gives every density operator on a Hilbert space this form,
so no instance is lost, and the trace-class layer is avoided. Several mixtures present the same operator;
all quantities below depend only on the operator. -/
structure MixedState (ι : Type) where
  /-- The probability weights. -/
  w : ℕ → ℝ
  /-- The unit vectors. -/
  v : ℕ → Ell2 ι
  w_nonneg : ∀ a, 0 ≤ w a
  hasSum_w : HasSum w 1
  norm_v : ∀ a, ‖v a‖ = 1

/-- The pure state `|ψ⟩⟨ψ|` as a `MixedState`: weight `1` at index `0`, the vector `ψ` at every index. -/
noncomputable def MixedState.pure {ι : Type} (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) : MixedState ι where
  w := fun a => if a = 0 then 1 else 0
  v := fun _ => ψ
  w_nonneg := fun a => by split_ifs <;> norm_num
  hasSum_w := hasSum_ite_eq 0 1
  norm_v := fun _ => hψ

end QSDMixing.GU


