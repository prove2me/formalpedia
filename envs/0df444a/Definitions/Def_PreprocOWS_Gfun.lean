-- Prove2me | Definitions.Def_PreprocOWS_Gfun
-- name    : PreprocOWS_Gfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:29:55.320407+00:00
-- url     : https://prove2.me/theorems/547af773-8080-4808-bc1b-bd1c50881f46
-- title:
--   The terms $G_t$, $B_t$, $C_t$ ("final database without $x$")
-- statement:
--   For a start state $\psi$,
--   $$
--   G_t:=\frac1{KN}\sum_{k,S}\Big\|\sum_{x\notin S_k}|v_{t,S\oplus(k,x),x}\rangle\Big\|^2 ,
--   $$
--   and for a step $1\le t\le T$,
--   $$
--   B_t=\frac1{KN}\sum_{k,S}\Big\|\sum_{x\notin S_k}Q_{k,x}U_t|v_{t-1,S,x}\rangle\Big\|^2,\qquad
--   C_t=\frac1{KN}\sum_{k,S'}\Big\|\sum_{x\notin S'_k}Q_{k,x}U_t|v_{t-1,S'\oplus(k,x),x}\rangle\Big\|^2 .
--   $$
--
--   The induction $\sqrt{G_t}\le\sqrt{G_{t-1}}+\sqrt{2/K}$ of display (11) runs through $B_t$ and $C_t$.
--
--   **Formalization Note** The step $t$ is indexed as $t=i+1$ with $i\in\{0,\dots,T-1\}$, so `Bfun A ψ i` is $B_{i+1}$ and uses $U_{i+1}$.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.3, pp.22–23 (PDF pp.25–26)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_feynV
open Matrix

namespace PreprocOWS

/-- The "final database without `x`" part **`G_t`**, Dong–Lombardi, arXiv:2610.02101 (version of
2026-11-02, sha256 7a0bd8da…), §5.3, p.22 (PDF p.25):
`G_t := (1/(KN)) ∑_{k,S} ‖∑_{x ∉ S_k} |v_{t, S ⊕ (k,x), x}⟩‖²`. -/
noncomputable def Gfun {S T K N w : ℕ} (A : Alg S T K N w) (ψ : Fin (2 ^ S) × DB K N → ℂ)
    (t : ℕ) : ℝ :=
  ((K : ℝ) * N)⁻¹ * ∑ k, ∑ D : DB K N,
    vnormSq (∑ x ∈ Finset.univ.filter (fun x => (k, x) ∉ D), feynV A ψ t (symmDiff D {(k, x)}) x)

/-- The term **`B_t`** of arXiv:2610.02101, §5.3, p.22 (PDF p.25), for the step `t = i + 1`:
`B_t = (1/(KN)) ∑_{k,S} ‖∑_{x ∉ S_k} Q_{k,x} U_t |v_{t−1,S,x}⟩‖²`. -/
noncomputable def Bfun {S T K N w : ℕ} (A : Alg S T K N w) (ψ : Fin (2 ^ S) × DB K N → ℂ)
    (i : Fin T) : ℝ :=
  ((K : ℝ) * N)⁻¹ * ∑ k, ∑ D : DB K N,
    vnormSq (∑ x ∈ Finset.univ.filter (fun x => (k, x) ∉ D),
      (Qproj A (some (k, x)) * (A.U i : Matrix (Ω S N w) (Ω S N w) ℂ)) *ᵥ feynV A ψ i D x)

/-- The term **`C_t`** of arXiv:2610.02101, §5.3, p.22 (PDF p.25), for the step `t = i + 1`:
`C_t = (1/(KN)) ∑_{k,S'} ‖∑_{x ∉ S'_k} Q_{k,x} U_t |v_{t−1, S' ⊕ (k,x), x}⟩‖²`. -/
noncomputable def Cfun {S T K N w : ℕ} (A : Alg S T K N w) (ψ : Fin (2 ^ S) × DB K N → ℂ)
    (i : Fin T) : ℝ :=
  ((K : ℝ) * N)⁻¹ * ∑ k, ∑ D : DB K N,
    vnormSq (∑ x ∈ Finset.univ.filter (fun x => (k, x) ∉ D),
      (Qproj A (some (k, x)) * (A.U i : Matrix (Ω S N w) (Ω S N w) ℂ)) *ᵥ
        feynV A ψ i (symmDiff D {(k, x)}) x)

end PreprocOWS


