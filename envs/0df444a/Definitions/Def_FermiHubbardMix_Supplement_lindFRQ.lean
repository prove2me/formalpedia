-- Prove2me | Definitions.Def_FermiHubbardMix_Supplement_lindFRQ
-- name    : FermiHubbardMix_Supplement_lindFRQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:02:05.557309+00:00
-- url     : https://prove2.me/theorems/569c464c-bc74-4c69-a3c6-7ad02e7f4964
-- title:
--   Field-resonant Lindbladian $\mathcal L_{\mathrm{FR}}=\sum_j\mathcal L_{\mathrm{FR},j}$ for qubits
-- statement:
--   Let $H=\sum_j v_j+W$ be an $n$-qubit Hamiltonian with external field and $\beta>0$. For each qubit $j$ set
--   $$
--   \Delta_j=\max\Bigl(\tfrac1\beta,\ \lambda_{\max}(v_j)-\lambda_{\min}(v_j)\Bigr),\qquad \eta_j=\sigma_j=\sqrt{\Delta_j/\beta},
--   $$
--   so that $\beta(\eta_j^2+\sigma_j^2)=2\Delta_j$. For a Pauli $P\in\{\sigma_X^{(j)},\sigma_Y^{(j)},\sigma_Z^{(j)}\}$ at site $j$, with filter $f_j(t)=(2/\pi)^{1/4}\sigma_j^{1/2}e^{-\sigma_j^2t^2}$, jump operator $A^P(\omega)=\frac1{\sqrt{2\pi}}\int e^{iHt}Pe^{-iHt}e^{-i\omega t}f_j(t)\,dt$, transition weight $\gamma_j(\omega)=\exp(-(\omega+\Delta_j)^2/(2\eta_j^2))$ and coherent term $C^P$ (built from the kernels $b_{1,j}$, $b_{2,j}$ of Definition 6.1),
--   $$
--   \mathcal L^P(\rho)=-i[C^P,\rho]+\int\gamma_j(\omega)\Bigl(A^P(\omega)\rho A^P(\omega)^\dagger-\tfrac12\{A^P(\omega)^\dagger A^P(\omega),\rho\}\Bigr)d\omega .
--   $$
--   The site contribution is $\mathcal L_{\mathrm{FR},j}=\sum_{P\in\{\sigma_X^{(j)},\sigma_Y^{(j)},\sigma_Z^{(j)}\}}\mathcal L^P$ and the **field-resonant Lindbladian** is $\mathcal L_{\mathrm{FR}}=\sum_j\mathcal L_{\mathrm{FR},j}$. All Heisenberg evolutions use the full Hamiltonian $H$.
--
--   The parameters are tuned to the onsite spectral gap, which is what makes the mixing guarantees of the paper independent of the field strength.
--
--   **Formalization Note** Each $\mathcal L^P$ is the published per-jump Lindbladian `FermiHubbardMix.jumpLind H P β σ_j η_j Δ_j` of the base mission (Definition 13.1 has the same formulas as Definition 6.1). $\lambda_{\max}$, $\lambda_{\min}$ are the supremum and infimum of the real spectrum of the Hermitian operator $v_j$.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 6.1, pp.17–18; Definition 6.3, p.18

import Mathlib
import Definitions.Def_FermiHubbardMix_Supplement_IsSuppOn
import Definitions.Def_FermiHubbardMix_HamData
import Definitions.Def_FermiHubbardMix_ckgLind
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

/-- The spectral spread `λ_max(A) - λ_min(A)` of a Hermitian operator `A` (arXiv:2604.08408, held
version sha256 055b8f8f…, Definition 6.3, p.18).

**Formalization Note** For Hermitian `A` the real spectrum `spectrum ℝ A` is the (finite, nonempty)
set of eigenvalues, so `sSup` and `sInf` are `λ_max` and `λ_min`. It is applied only to the onsite
terms `v_j`, which are Hermitian under `IsQubitLocal`. -/
def specSpread {n : ℕ} (A : Op n) : ℝ := sSup (spectrum ℝ A) - sInf (spectrum ℝ A)

/-- `Δ_j = max(1/β, λ_max(v_j) - λ_min(v_j))` (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 6.3, p.18). -/
def deltaQ {n : ℕ} (H : HamData (Fin n) n) (β : ℝ) (j : Fin n) : ℝ :=
  max (1 / β) (specSpread (H.v j))

/-- `η_j = σ_j = √(Δ_j/β)` (arXiv:2604.08408, held version sha256 055b8f8f…, Definition 6.3,
p.18). With this choice `β(η_j² + σ_j²) = 2Δ_j`. -/
def sigmaQ {n : ℕ} (H : HamData (Fin n) n) (β : ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (deltaQ H β j / β)

/-- The site contribution `L_FR,j` of the **field-resonant Lindbladian** (arXiv:2604.08408, held
version sha256 055b8f8f…, Definition 6.3, p.18, with Definition 6.1, pp.17–18):
`L_j = ∑_{P ∈ {σ_X^{(j)}, σ_Y^{(j)}, σ_Z^{(j)}}} L^P`, `L^P(ρ) = -i[C^P, ρ] + L^P_diss(ρ)`, all built from the full
Hamiltonian `H = V + W` at inverse temperature `β` with the parameters `σ_j = η_j = √(Δ_j/β)`, `Δ_j`.

**Formalization Note** Each `L^P` is the published per-jump CKG Lindbladian
`FermiHubbardMix.jumpLind H.ham P β σ_j η_j Δ_j` (filter `f_j`, jump `A^P(ω)`, weight `γ_j`, dissipator,
kernels `b_{1,j}`, `b_{2,j}` and coherent term `C^P` of Definition 6.1, identical to Definition 13.1),
with `P` the single-site Pauli `sitePauli j σ_P`. -/
def lindFRQSite {n : ℕ} (H : HamData (Fin n) n) (β : ℝ) (j : Fin n) : Op n →ₗ[ℂ] Op n :=
  jumpLind H.ham (sitePauli j FermiCap.Gaussian.pauliX) β (sigmaQ H β j) (sigmaQ H β j) (deltaQ H β j) +
  jumpLind H.ham (sitePauli j FermiCap.Gaussian.pauliY) β (sigmaQ H β j) (sigmaQ H β j) (deltaQ H β j) +
  jumpLind H.ham (sitePauli j FermiCap.Gaussian.pauliZ) β (sigmaQ H β j) (sigmaQ H β j) (deltaQ H β j)

/-- **Definition 6.3 (Field-resonant Lindbladian)** `L_FR = ∑_j L_FR,j` of the `n`-qubit Hamiltonian
`H` at inverse temperature `β` (arXiv:2604.08408, held version sha256 055b8f8f…, p.18). -/
def lindFRQ {n : ℕ} (H : HamData (Fin n) n) (β : ℝ) : Op n →ₗ[ℂ] Op n :=
  ∑ j, lindFRQSite H β j

end FermiHubbardMix.Supplement


