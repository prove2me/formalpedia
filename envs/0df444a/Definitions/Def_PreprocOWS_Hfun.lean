-- Prove2me | Definitions.Def_PreprocOWS_Hfun
-- name    : PreprocOWS_Hfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:29:54.46841+00:00
-- url     : https://prove2.me/theorems/96d00a56-ba80-4b06-955a-b632faac5375
-- title:
--   The term $H_t$ ("large $S_k$")
-- statement:
--   For $\ell\in\mathbb N$, a start state $\psi$ and $t\ge0$,
--   $$
--   H_t:=\frac1{KN}\sum_{\substack{k,S\\|S_k|>\sqrt\ell+t}}\Big\|\sum_x|v_{t,S\oplus(k,x),x}\rangle\Big\|^2 .
--   $$
--
--   It bounds the part of the winning probability where the final database row of the challenge key is large (display (9)).
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_feynV
open Matrix

namespace PreprocOWS

/-- The "large `S_k`" part **`H_t`**, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02,
sha256 7a0bd8da…), §5.3, p.21 (PDF p.24):
`H_t := (1/(KN)) ∑_{k,S : |S_k| > √ℓ + t} ‖∑_x |v_{t, S ⊕ (k,x), x}⟩‖²`. -/
noncomputable def Hfun {S T K N w : ℕ} (A : Alg S T K N w) (ℓ : ℕ)
    (ψ : Fin (2 ^ S) × DB K N → ℂ) (t : ℕ) : ℝ :=
  ((K : ℝ) * N)⁻¹ * ∑ k, ∑ D ∈ Finset.univ.filter (fun D : DB K N => Real.sqrt ℓ + t < rowCard D k),
    vnormSq (∑ x, feynV A ψ t (symmDiff D {(k, x)}) x)

end PreprocOWS


