-- Prove2me | Definitions.Def_SparseSDP_TwoSided_sdpSolve
-- name    : SparseSDP_TwoSided_sdpSolve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:12.680966+00:00
-- url     : https://prove2.me/theorems/5f451dd3-8a1a-48ca-bb25-3f3bc538e215
-- title:
--   The end-to-end solver of Corollary 7.11, as a charged program
-- statement:
--   The program of the proof of Corollary 7.11 (pp. 63–64). With $\eta=\varepsilon/2$, $\xi=\zeta=\varepsilon/(8(1+r))$, $K=1+\max\{0,\lceil\log_2(2R/\eta)\rceil\}$ and $\delta'=\delta/(2K)$, it runs the gapped search. At each queried $g$ it runs Algorithm 7 on the realified lifted game, with radius $R$, simplex radius one, $\omega_D=2$, row sparsity $2s+1$, failure $\delta'$ and
--   $$
--   T=\lceil C_T\gamma_D^2\Lambda\rceil,\quad \gamma_D=\frac{R\omega_D}{\xi},\quad \Lambda=\log\frac{16(m+1)(2n+1)}{\delta'},
--   $$
--   then the certificate of Lemma 2.5, with the product by $M_g=H_{T+1}/T$ reusing the final Hamiltonian.
--
--   The output is the list of factors $z_t=\sqrt{R/T}\,(x_t+iy_t)$ of the retained solution, where $\tilde\psi_t=(x_t,y_t,\cdot)$: cutting $Y^{\mathrm{out}}=T^{-1}\sum_tR\tilde\psi_t\tilde\psi_t^\top$ to its leading block and applying $\Psi$ gives $\sum_tz_tz_t^\dagger$ by Eq. (383).
--
--   **Formalization Note** The instance is read only through `gameAccess`.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Corollary 7.11, proof, pp. 63–64; Eq. (362), p. 63; Eq. (383), p. 68

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7
import Definitions.Def_SparseSDP_TwoSided_certProg
import Definitions.Def_SparseSDP_TwoSided_gappedSearch
import Definitions.Def_SparseSDP_TwoSided_gameAccess

open Matrix

namespace SparseSDP.TwoSided

variable {n m : ℕ} {I : Instance ℂ n m}

/-- The rounds of each game: `T = ⌈C_T γ_D² Λ⌉` with `γ_D = Rω_D/ξ`, `ω_D = 2` (Eq. (362), p. 63) and
`Λ = log(16(m + 1)(2n + 1)/δ')`, for `m + 1` payoff matrices of size `2n + 1`. -/
noncomputable def gameRounds (P : Consts) (n m : ℕ) (R ξ δ' : ℝ) : ℕ :=
  ⌈P.CT * (R * 2 / ξ) ^ 2 * lamP (m + 1) (n + n + 1) δ'⌉₊

/-- The complex factor `z = √(R/T)(x + iy)` of a round with `ψ̃ = (x, y, ·)` (Eq. (383), p. 68). The
retained `Y^out = T⁻¹ ∑ₜ Rψ̃ₜψ̃ₜᵀ` has leading block `(R/T) ∑ₜ wₜwₜᵀ` with `wₜ = (xₜ, yₜ)`, and `Ψ` maps it
to `∑ₜ zₜzₜ†`. -/
noncomputable def factor (R : ℝ) (T : ℕ) (ψ : Vec (n + n + 1)) : Fin n → ℂ :=
  fun i => (√(R / T) : ℝ) * ((ψ (pos (Sum.inl i)) : ℂ) + Complex.I * (ψ (pos (Sum.inr i)) : ℂ))

/-- **The end-to-end solver** of the proof of Corollary 7.11 (pp. 63–64): `η = ε/2`,
`ξ = ζ = ε/(8(1 + r))`, `K` queries at most, failure `δ/(2K)` per call; at each queried `g` Algorithm 7
with radius `R`, simplex radius one and `ω_D = 2` on the realified lifted game (row sparsity
`2s + 1`), then the certificate of Lemma 2.5, whose product with `M_g = H_{T+1}/T` reuses the
final Hamiltonian (p. 64). The output is the list of factors of the retained solution. -/
noncomputable def sdpSolve (P : Consts) (s : ℕ) (R r ε δ : ℝ) (orc : SparseOracle I) :
    Prog (List (Fin n → ℂ)) := do
  let η ← op 1 (ε / 2)
  let ξ ← op 3 (ε / (8 * (1 + r)))
  let K ← op 6 (searchBudget R η)
  let δ' ← op 2 (δ / (2 * K))
  let T ← op 12 (gameRounds P n m R ξ δ')
  let res ← gappedSearch
    (fun g => alg7 P (gameAccess orc R g) (2 * s + 1) 2 R 1 T δ')
    (fun g out => certProg P R 2 ξ δ'
      (fun v => do
        let h ← applyH (gameAccess orc R g) 1 out.rep v
        scale (1 / T) h))
    R η ξ
  let mut L : List (Fin n → ℂ) := []
  for x in res.sol.rounds do
    tick 1
    let z ← op (6 * n + 2) (factor R T x.ψ)
    L := z :: L
  pure L

end SparseSDP.TwoSided


