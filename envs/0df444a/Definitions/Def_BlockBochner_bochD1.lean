-- Prove2me | Definitions.Def_BlockBochner_bochD1
-- name    : BlockBochner_bochD1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:35.256109+00:00
-- url     : https://prove2.me/theorems/4a46cfe7-441f-4701-82b4-6d718090e06b
-- title:
--   The map $d_1:\bigoplus_iW_i\to\bigoplus_{i<j}W_{ij}$
-- statement:
--   With $W_{ij}=W_i\cap W_j$, $P_{ij}$ its orthogonal projection, and $H_2=\bigoplus_{i<j}W_{ij}$ (the $\ell^2$ sum),
--   $$d_1\bigl((f_i)_i\bigr)_{ij}=P_{ij}(f_i-f_j)\qquad(i<j).$$
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.22

import Mathlib
import Definitions.Def_BlockBochner_bochD0

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The map `d₁ : ⊕_i W_i → ⊕_{i<j} W_{ij}`, `d₁((f_i)_i)_{ij} = P_{ij}(f_i − f_j)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228,
Sec. 3.3, p.22: `H₂ = ⊕_{i<j} W_{ij}`, `W_{ij} = W_i ∩ W_j`, with the `ℓ²` inner product.

**Formalization Note** The pairs `i < j` are the subtype `{p : Fin n × Fin n // p.1 < p.2}`; `P_{ij}` is
the orthogonal projection onto the closed subspace `W_i ⊓ W_j`. -/
noncomputable def bochD1 {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) :
    PiLp 2 (fun i => (W i : Submodule ℝ H)) →L[ℝ]
      PiLp 2 (fun p : {p : Fin n × Fin n // p.1 < p.2} =>
        ((W p.1.1 ⊓ W p.1.2 : ClosedSubmodule ℝ H) : Submodule ℝ H)) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun p =>
      ((W p.1.1 ⊓ W p.1.2 : ClosedSubmodule ℝ H) : Submodule ℝ H).orthogonalProjectionOnto ∘L
        ((W p.1.1 : Submodule ℝ H).subtypeL ∘L PiLp.proj 2 _ p.1.1 -
          (W p.1.2 : Submodule ℝ H).subtypeL ∘L PiLp.proj 2 _ p.1.2))

end BlockBochner


