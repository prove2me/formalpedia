-- Prove2me | Definitions.Def_QSDMixing_GU_schurChannel
-- name    : QSDMixing_GU_schurChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:25.614748+00:00
-- url     : https://prove2.me/theorems/91331b26-ff69-43c8-a19b-cb1e575f3be2
-- title:
--   The Hadamard channel $\Phi_X(Y)=X\circ Y$
-- statement:
--   The Hadamard channel of a matrix $X$ is the linear map
--
--   $$
--   \Phi_X(Y)=X\circ Y,
--   $$
--
--   with $\circ$ the entrywise (Schur) product. It is a quantum channel when $X$ is positive semidefinite with unit diagonal. Each additional copy of an ensemble with Gram matrix $X$ applies $\Phi_X$ once.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib

set_option autoImplicit false

namespace QSDMixing.GU

/-- The Hadamard channel `Φ_X(Y) = X ∘ Y` of a matrix `X`, with `∘` the Schur product.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17. -/
def schurChannel {n : Type} (X : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun Y := Matrix.hadamard X Y
  map_add' := fun Y Z => Matrix.hadamard_add X Y Z
  map_smul' := fun c Y => Matrix.hadamard_smul X Y c

end QSDMixing.GU


