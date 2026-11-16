-- Prove2me | Definitions.Def_PreprocOWS_Supplement_distAdv
-- name    : PreprocOWS_Supplement_distAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:08:12.200368+00:00
-- url     : https://prove2.me/theorems/810e5399-4995-4304-bb8c-c02cae516936
-- title:
--   Oracle state distinguishing game: the advantage for a fixed phase function
-- statement:
--   For a sign vector $h:[N]\to\{\pm1\}$ the **random binary phase state** is $|\psi_h\rangle = N^{-1/2}\sum_x h(x)|x\rangle$.
--
--   For an isometry $V:\mathbb C^N\to\mathbb C^M$, a projection $\Pi$ on $\mathbb C^M$, a phase function $f:[M]\to\{\pm1\}$ and an oracle $R:[K]\times[N]\to\{\pm1\}$, the distinguishing advantage of the **oracle state distinguishing game** for this $f$ is
--   $$
--   \Big|\,\mathbb E_k\langle\psi_{R,k}|V^\dagger O_f^\dagger\Pi O_f V|\psi_{R,k}\rangle-\mathbb E_h\langle\psi_h|V^\dagger O_f^\dagger\Pi O_f V|\psi_h\rangle\Big|,
--   $$
--   with $k$ uniform on $[K]$ and $h$ uniform on $\{\pm1\}^N$, independent of $R$. The paper's $\Delta_{\mathcal A}(R)$ is the maximum of this quantity over $f$.
--
--   **Formalization Note** Each quadratic form is taken as the real part of $\langle v,\Pi v\rangle$ (it is real for Hermitian $\Pi$).
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 9.4, pp.37–38 (PDF pp.40–41)

import Mathlib
import Definitions.Def_PreprocOWS_Supplement_searchWin
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The **random binary phase state** `|ψ_h⟩ = N^{-1/2} ∑_x h(x) |x⟩` for a sign vector
`h : [N] → {±1}` (arXiv:2610.02101, §9.2, p.38, PDF p.41: "`h` is an independent random binary
phase vector, and defines `|ψ_h⟩` as a random binary phase state"). -/
noncomputable def phaseVec {N : ℕ} (h : Fin N → Bool) : Fin N → ℂ :=
  fun x => ((Real.sqrt N : ℝ) : ℂ)⁻¹ * sgn (h x)

/-- The distinguishing advantage of the **oracle state distinguishing game** for a fixed phase
function `f`, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
Definition 9.4, pp.37–38 (PDF pp.40–41):
`| E_k ⟨ψ_{R,k}| V†O_f†ΠO_fV |ψ_{R,k}⟩ − E_h ⟨ψ_h| V†O_f†ΠO_fV |ψ_h⟩ |`.
The page's `Δ_𝒜(R)` is the maximum of this over `f`.

**Formalization Note.** `k` is uniform on `[K]` and `h` uniform on `{±1}^N`, independent of `R`.
`V` and the projection `Π` (measurement `{Π, I − Π}`) are fixed independently of `R`; only `f` may
depend on `R`. Each term is the real part of the quadratic form `⟨v, Π v⟩`. -/
noncomputable def distAdv {K N M : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (P : Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (R : Oracle K N) : ℝ :=
  |avg (fun k : Fin K =>
      (star (phaseF f *ᵥ (V *ᵥ chal R k)) ⬝ᵥ (P *ᵥ (phaseF f *ᵥ (V *ᵥ chal R k)))).re) -
    avg (fun h : Fin N → Bool =>
      (star (phaseF f *ᵥ (V *ᵥ phaseVec h)) ⬝ᵥ (P *ᵥ (phaseF f *ᵥ (V *ᵥ phaseVec h)))).re)|

end PreprocOWS.Supplement


