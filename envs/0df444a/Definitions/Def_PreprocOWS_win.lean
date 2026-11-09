-- Prove2me | Definitions.Def_PreprocOWS_win
-- name    : PreprocOWS_win
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:26:44.601121+00:00
-- url     : https://prove2.me/theorems/d7cf681f-6803-48a1-9694-2db89fbcfb70
-- title:
--   Winning probability of the 1OWS game with advice $|\varphi\rangle$
-- statement:
--   For an algorithm $A$, an oracle $R$ and advice $|\varphi\rangle$, the **winning probability** is the probability that the measurement $\{\Pi_k\}$ returns the key $k$, for $k$ uniform in $[K]$:
--   $$
--   \mathrm{win}_A(R,\varphi)=\frac1K\sum_{k\in[K]}\big\|\Pi_k\,(O_RU)^T\,\big(|\varphi\rangle|\psi_{R,k}\rangle|0^w\rangle\big)\big\|^2 .
--   $$
--   For a projective measurement this equals $\mathbb E_k\langle\varphi|\langle\psi_{R,k}|\langle0^w|(U^\dagger O_R^\dagger)^T\Pi_k(O_RU)^T|\psi_{R,k}\rangle|\varphi\rangle|0^w\rangle$, the quantity inside the §5.1 display.
--
--   The non-uniform security of 1OWS is the average of this quantity over $R$, maximized over advice chosen as a function of $R$.
--
--   **Formalization Note** The advice is any vector on $[2^S]$; statements require it to be a unit vector.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 (PDF p.19); §5.1 display, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_run
import Definitions.Def_PreprocOWS_chal
open Matrix

namespace PreprocOWS

/-- The **winning probability** of the 1OWS game for oracle `R` and advice `|φ⟩`, Dong–Lombardi,
arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 and the §5.1
display, p.17 (PDF p.20):
`E_k ⟨φ|⟨ψ_{R,k}|⟨0^w| (U†O_R†)^T Π_k (O_R U)^T |ψ_{R,k}⟩|φ⟩|0^w⟩ = (1/K) ∑_k ‖Π_k (O_R U)^T (φ ⊗ ψ_{R,k} ⊗ 0^w)‖²`,
the probability that the measurement `{Π_k}` returns the key `k`, for `k` uniform in `[K]`.

**Formalization Note.** For a projective measurement the squared norm equals the quadratic form of the
page. The advice `φ` is a vector on `[2^S]` (a unit vector in every statement); the challenge is one
copy of `|ψ_{R,k}⟩`; the workspace starts at `|0^w⟩`. -/
noncomputable def win {S T K N w : ℕ} (A : Alg S T K N w) (R : Oracle K N) (φ : Fin (2 ^ S) → ℂ) :
    ℝ :=
  (K : ℝ)⁻¹ * ∑ k, vnormSq (A.proj k *ᵥ (run A R *ᵥ (embed w R k *ᵥ φ)))

end PreprocOWS


