-- Prove2me | Definitions.Def_FermiHubbardMix_FRData
-- name    : FermiHubbardMix_FRData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:34:17.736027+00:00
-- url     : https://prove2.me/theorems/86ba6e2d-406b-4abc-b388-351f2ef932bf
-- title:
--   Field-resonant Lindbladian $\mathcal L_{\mathrm{FR}}$ (onsite eigenbasis, $\Delta_{\mu\nu}$, $\sigma_{\mu\nu}=\eta_{\mu\nu}$), $\kappa_\star$, $z_i$
-- statement:
--   Let $H=V+W$ be a local fermionic Hamiltonian with onsite terms. Since each $v_i$ is even and Hermitian, there is an even unitary $U_i\in\mathfrak A_{\{i\}}$ with
--   $$
--   U_iv_iU_i^\dagger=\sum_{\mu\in F_i}\lambda_i(\mu)\,P^i_{\mu\mu}
--   $$
--   (Remark 13.3); such data $(U_i,\lambda_i)_i$ is an **onsite eigenbasis**. Set $\varepsilon_\mu=\lambda_i(\mu)-\min_\nu\lambda_i(\nu)$, so $\min_\mu\varepsilon_\mu=0$, and (Definition 13.4)
--   $$
--   a_\mu=\sqrt{\varepsilon_\mu+\tfrac1{4\beta}},\qquad \Delta_{\mu\nu}=(a_\mu+a_\nu)^2,\qquad \sigma_{\mu\nu}=\eta_{\mu\nu}=\sqrt{\Delta_{\mu\nu}/\beta}.
--   $$
--   The **field-resonant Lindbladian** is $\mathcal L_{\mathrm{FR}}=\sum_i\mathcal L_{\mathrm{FR},i}$, where $\mathcal L_{\mathrm{FR},i}=\sum_{\mu,\nu}\mathcal L_{B}$ is the site contribution of Definition 13.1 for the Hamiltonian $H$, the jumps $B=U_i^\dagger P^i_{\mu\nu}U_i$ and the parameters $\Delta_{\mu\nu},\sigma_{\mu\nu},\eta_{\mu\nu}$. Also $\kappa_\star=e^{-1/4}/\sqrt2$ and $z_i=\sum_\mu e^{-\beta\varepsilon_\mu}$.
--
--   Each filter is tuned to the two onsite levels its jump connects, which is what makes the mixing bounds independent of the onsite energies.
--
--   **Formalization Note** Definition 13.4 assumes $v_i$ diagonal; Remark 13.3 reduces the general case to it by conjugation with $U=\prod_iU_i$. Since $e^{i\tilde Ht}Pe^{-i\tilde Ht}=Ue^{iHt}(U_i^\dagger PU_i)e^{-iHt}U^\dagger$ for $\tilde H=UHU^\dagger$, the paper's $U^\dagger\tilde{\mathcal L}(U\rho U^\dagger)U$ is exactly Definition 13.1 for $H$ with the jumps $U_i^\dagger P^i_{\mu\nu}U_i$, which is what is formalized; $U_i=I$ is admissible when $v_i$ is diagonal. The shift by $\min\lambda$ changes $H$ by a scalar and is not applied to $H$.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Remark 13.3, p.60; Definition 13.4, pp.60–61; §14, p.62; Lemma 14.4, p.66

import Mathlib
import Definitions.Def_FermiHubbardMix_HamData
import Definitions.Def_FermiHubbardMix_ckgLind
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {m N : ℕ}

/-- An onsite eigenbasis for the onsite terms of `H` (arXiv:2604.08408, held version sha256
055b8f8f…, Remark 13.3, p.60): for every site `i`, an even unitary `U_i ∈ 𝔄_{{i}}` and reals `λ_i(µ)`
with `U_i v_i U_i† = ∑_µ λ_i(µ) P^i_{µµ}` (diagonal in the local occupation basis).

**Formalization Note** Definition 13.4 assumes every `v_i` already diagonal; Remark 13.3 reduces
the general case to it by conjugating with such `U_i`. This structure records that reduction, so
that the field-resonant Lindbladian is defined for arbitrary onsite terms; for a diagonal `v_i`
(e.g. Fermi–Hubbard), `U_i = I` is admissible. -/
structure FRData (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) where
  /-- the onsite unitaries `U_i` -/
  U : Λ → Op N
  /-- the onsite eigenvalues `λ_i(µ)` -/
  lam : Λ → LocCfg m → ℝ
  U_mem : ∀ i, U i ∈ localAlg ord {i}
  U_even : ∀ i, IsEven (U i)
  U_unitary : ∀ i, (U i)ᴴ * U i = 1 ∧ U i * (U i)ᴴ = 1
  diag : ∀ i, U i * H.v i * (U i)ᴴ = ∑ μ, ((lam i μ : ℝ) : ℂ) • matUnit ord i μ μ

namespace FRData

variable {ord : Λ × Fin m ≃ Fin N} {H : HamData Λ N}

/-- The shifted onsite energies `ε_µ = λ_i(µ) - min_ν λ_i(ν)`, so that `min_µ ε_µ = 0`
(arXiv:2604.08408, held version sha256 055b8f8f…, Remark 13.3 and Definition 13.4, p.60). -/
def eps (F : FRData ord H) (i : Λ) (μ : LocCfg m) : ℝ :=
  F.lam i μ - Finset.univ.inf' Finset.univ_nonempty (F.lam i)

/-- `a_µ = √(ε_µ + 1/(4β))` (arXiv:2604.08408, held version sha256 055b8f8f…, Definition 13.4,
p.60). -/
def aPar (F : FRData ord H) (β : ℝ) (i : Λ) (μ : LocCfg m) : ℝ :=
  Real.sqrt (F.eps i μ + 1 / (4 * β))

/-- `Δ_{µν} = (a_µ + a_ν)²` (arXiv:2604.08408, held version sha256 055b8f8f…, Definition 13.4,
p.60). -/
def delta (F : FRData ord H) (β : ℝ) (i : Λ) (μ ν : LocCfg m) : ℝ :=
  (F.aPar β i μ + F.aPar β i ν) ^ 2

/-- `σ_{µν} = η_{µν} = √(Δ_{µν}/β)` (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 13.4, p.60). -/
def sigma (F : FRData ord H) (β : ℝ) (i : Λ) (μ ν : LocCfg m) : ℝ :=
  Real.sqrt (F.delta β i μ ν / β)

/-- The field-resonant jump at site `i` for the pair `(µ, ν)`: `U_i† P^i_{µν} U_i`, i.e. the matrix
unit `P^i_{µν}` of Definition 13.4 in the onsite eigenbasis of Remark 13.3 (arXiv:2604.08408, held
version sha256 055b8f8f…, pp.60–61). -/
def jump (F : FRData ord H) (i : Λ) (μ ν : LocCfg m) : Op N :=
  (F.U i)ᴴ * matUnit ord i μ ν * F.U i

end FRData

/-- The site contribution `L_FR,i = ∑_{µ,ν} L_{P^i_{µν}}` of the **field-resonant Lindbladian**
(arXiv:2604.08408, held version sha256 055b8f8f…, Definition 13.4, p.61): Definition 13.1 for the
Hamiltonian `H`, the jumps `P^i_{µν}` (in the onsite eigenbasis, Remark 13.3) and the parameters
`Δ_{µν}`, `σ_{µν} = η_{µν}`.

**Formalization Note** The paper conjugates `H` and the jumps by `U = ∏_i U_i` (Remark 13.3) and works
with the rotated `H̃ = U H U†` and jumps `P^i_{µν}`, the Lindbladian of the original problem being
`ρ ↦ U† L̃(U ρ U†) U`. Since `e^{iH̃t} P e^{-iH̃t} = U e^{iHt}(U_i† P U_i)e^{-iHt} U†` (the `U_j`,
`j ≠ i`, are even and commute with `P^i_{µν}`), this equals Definition 13.1 for `H` with the jumps
`U_i† P^i_{µν} U_i`, which is what is written here. The shift `ε = λ - min λ` changes `H` only by a
scalar and is not applied to `H`. -/
def lindFRSite (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) (i : Λ) :
    Op N →ₗ[ℂ] Op N :=
  ∑ μ, ∑ ν, jumpLind H.ham (F.jump i μ ν) β (F.sigma β i μ ν) (F.sigma β i μ ν) (F.delta β i μ ν)

/-- **Definition 13.4 (Field-resonant Lindbladian)** `L_FR = ∑_{i ∈ Λ} L_FR,i` of `H` at inverse
temperature `β` (arXiv:2604.08408, held version sha256 055b8f8f…, p.61). -/
def lindFR (ord : Λ × Fin m ≃ Fin N) (H : HamData Λ N) (F : FRData ord H) (β : ℝ) :
    Op N →ₗ[ℂ] Op N :=
  ∑ i, lindFRSite ord H F β i

/-- The constant `κ⋆ = e^{-1/4}/√2` (arXiv:2604.08408, held version sha256 055b8f8f…, §14, p.62). -/
def kappaStar : ℝ := Real.exp (-(1 / 4)) / Real.sqrt 2

/-- `z_i = ∑_{µ ∈ F_i} e^{-βε_µ}` (arXiv:2604.08408, held version sha256 055b8f8f…, Lemma 14.4,
p.66). -/
def FRData.zSite {ord : Λ × Fin m ≃ Fin N} {H : HamData Λ N} (F : FRData ord H) (β : ℝ) (i : Λ) :
    ℝ :=
  ∑ μ, Real.exp (-(β * F.eps i μ))

end FermiHubbardMix


