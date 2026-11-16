-- Prove2me | Definitions.Def_PreprocOWS_Supplement_prsAdv
-- name    : PreprocOWS_Supplement_prsAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:11:42.114214+00:00
-- url     : https://prove2.me/theorems/ea5e500e-7162-4212-b0bb-be413476b164
-- title:
--   Distinguishing advantage of a zero-query 1PRS adversary with advice $\rho_R$
-- statement:
--   Let $A$ be the $S$-qubit advice register and $X=\mathbb C^N$ the challenge register. For an acceptance operator $0\preceq\Pi\preceq I$ on $A\otimes X$, an advice density matrix $\rho$ and an oracle $R:[K]\times[N]\to\{\pm1\}$, the distinguishing advantage of the zero-query **1PRS** adversary is
--   $$
--   \Delta_{\mathcal A}(R)=\Big|\,\mathbb E_k\operatorname{Tr}\big(\Pi(\rho\otimes|\psi_{R,k}\rangle\langle\psi_{R,k}|)\big)-\mathbb E_{\psi\sim\mathrm{Haar}}\operatorname{Tr}\big(\Pi(\rho\otimes|\psi\rangle\langle\psi|)\big)\Big| ,
--   $$
--   with $k$ uniform on $[K]$.
--
--   **Formalization Note** The Haar average of $|\psi\rangle\langle\psi|$ on $\mathbb C^N$ is $I/N$, so the second term is written $\operatorname{Tr}(\Pi(\rho\otimes I/N))$, the page's $(1/N)\sum_x\Pi_{x,x}$ in (41). Traces are taken as real parts.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 11.1, p.52 (PDF p.55); §11.1, display (41), p.53 (PDF p.56)

import Mathlib
import Definitions.Def_PreprocOWS_chal
open Matrix
open scoped Kronecker

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The **distinguishing advantage of a zero-query 1PRS adversary** with advice `ρ` for the oracle
`R`, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 11.1,
p.52 (PDF p.55) and §11.1, display (41), p.53 (PDF p.56):
`Δ_𝒜(R) = | E_k Tr(Π (ρ ⊗ |ψ_{R,k}⟩⟨ψ_{R,k}|)) − E_{ψ Haar} Tr(Π (ρ ⊗ |ψ⟩⟨ψ|)) |`,
with `Π` the acceptance operator on `A ⊗ X` (advice register `[2^S]`, challenge register `[N]`).

**Formalization Note.** The Haar average of `|ψ⟩⟨ψ|` on `ℂ^N` is `I/N`, so the Haar term is written
as `Tr(Π (ρ ⊗ I/N))` (the page's `(1/N) ∑_x Π_{x,x}` in (41)); this is an exact identity. Traces are
taken as real parts (they are real for positive semidefinite `Π`, `ρ`). `k` is uniform on `[K]`. -/
noncomputable def prsAdv {S K N : ℕ} (P : Matrix (Fin (2 ^ S) × Fin N) (Fin (2 ^ S) × Fin N) ℂ)
    (ρ : Matrix (Fin (2 ^ S)) (Fin (2 ^ S)) ℂ) (R : Oracle K N) : ℝ :=
  |avg (fun k : Fin K => (P * (ρ ⊗ₖ Matrix.vecMulVec (chal R k) (star (chal R k)))).trace.re) -
    (P * (ρ ⊗ₖ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)))).trace.re|

end PreprocOWS.Supplement


