-- Prove2me | Definitions.Def_SysBathGibbs_KMS
-- name    : SysBathGibbs_KMS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:41.9438+00:00
-- url     : https://prove2.me/theorems/e114a62d-989c-4787-8752-5bd9849f347d
-- title:
--   KMS inner product, $\Gamma^s$, induced norms, complex-time evolution and Bohr sums
-- statement:
--   For the Gibbs state $\rho_\beta$ of a Hermitian $H$, the **KMS inner product** and norm are
--   $$
--   \langle O,P\rangle_{\rho_\beta}=\operatorname{Tr}(\rho_\beta^{1/2}O^\dagger\rho_\beta^{1/2}P),\qquad \|O\|_{\rho_\beta}=\|\rho_\beta^{1/4}O\rho_\beta^{1/4}\|_2,
--   $$
--   and a superoperator $\mathcal T$ has the induced norm $\|\mathcal T\|_{\rho_\beta\to\rho_\beta}=\sup_{O\ne0}\|\mathcal T(O)\|_{\rho_\beta}/\|O\|_{\rho_\beta}$. The change of coordinates is $\Gamma^s(O)=\rho_\beta^{s/2}O\rho_\beta^{s/2}$ for $s\in\mathbb R$, with $\Gamma=\Gamma^1$ and $\Gamma^{-1}$; a map $\mathcal T$ acts on relative densities as $\hat{\mathcal T}=\Gamma^{-1}\mathcal T\Gamma$. The Hilbert–Schmidt adjoint $\mathcal T^\dagger$ is defined by $\operatorname{Tr}(O^\dagger\mathcal T(P))=\operatorname{Tr}((\mathcal T^\dagger(O))^\dagger P)$.
--
--   The evolutions are $O(z)=e^{izH}Oe^{-izH}$ for $z\in\mathbb C$ and $\mathcal U(t)(O)=e^{-itH}Oe^{itH}=O(-t)$. A Bohr sum $\sum_\nu f(\nu)O_\nu$ uses the components $O_\nu=\sum_{E-E'=\nu}\Pi_EO\Pi_{E'}$ of $O$ in the spectral decomposition of $H$. The module also fixes the commutator, the anticommutator and the exponential $e^{s\mathcal L}$ of a superoperator.
--
--   **Formalization Note** Real powers are $\rho_\beta^{s}=Z^{-s}e^{-s\beta H}$ with $Z=\operatorname{Tr}e^{-\beta H}$, exact for Hermitian $H$. Induced norms take values in $[0,\infty]$, so a supremum is never a junk real $0$. The Hilbert–Schmidt adjoint is computed on matrix units, which is the adjoint of every linear map. Bohr sums are computed entrywise in an eigenbasis of $H$, which does not depend on the choice of eigenbasis.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), §2.1 eqs. (2.1)–(2.3), (2.6)–(2.9), pp.10–11

import Definitions.Def_SysBathGibbs_Algorithm

open Matrix

namespace SysBathGibbs

/-!
# The KMS geometry and the conventions of §2.1

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), §2.1, (2.1)–(2.3), (2.7), (2.9),
pp.10–11.

**Formalization Note.** Fractional powers are `ρ_β^s = Z^{-s} e^{-sβH}` with
`Z = Tr e^{-βH}`, which is exact for Hermitian `H` and needs no functional calculus. Induced norms
take values in `ℝ≥0∞`, so an unbounded ratio is `⊤` rather than a junk real `0`. A superoperator
is a plain function on matrices; every superoperator of the paper is linear. The Bohr components are
read in an eigenbasis of the Hermitian `H`.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The real power `ρ_β^s = Z^{-s} e^{-sβH}`, `Z = Tr e^{-βH}`, of the Gibbs state. -/
noncomputable def gibbsPow (β : ℝ) (H : Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  ((((Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • H))).re ^ (-s) : ℝ) : ℂ)) •
    NormedSpace.exp ((-((s * β : ℝ) : ℂ)) • H)

/-- The change of coordinates `Γ^s(O) = ρ_β^{s/2} O ρ_β^{s/2}`, (2.3), `s ∈ ℝ`.
`Γ = Γ^1`, `Γ⁻¹ = Γ^{-1}`. -/
noncomputable def Gam (β : ℝ) (H : Matrix ι ι ℂ) (s : ℝ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  gibbsPow β H (s / 2) * O * gibbsPow β H (s / 2)

/-- The KMS inner product `⟨O, P⟩_{ρ_β} = Tr(ρ_β^{1/2} O† ρ_β^{1/2} P)`, (2.2). -/
noncomputable def kmsInner (β : ℝ) (H O P : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (gibbsPow β H (1 / 2) * Oᴴ * gibbsPow β H (1 / 2) * P)

/-- The Hilbert–Schmidt norm `‖M‖₂ = √(Tr M†M)`, p.10. -/
noncomputable def hsNorm (M : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (Matrix.trace (Mᴴ * M)).re

/-- The KMS norm `‖O‖_{ρ_β} = ‖ρ_β^{1/4} O ρ_β^{1/4}‖₂`, (2.2). -/
noncomputable def kmsNorm (β : ℝ) (H O : Matrix ι ι ℂ) : ℝ :=
  hsNorm (gibbsPow β H (1 / 4) * O * gibbsPow β H (1 / 4))

/-- The induced norm `‖T‖_{ρ_β→ρ_β} = sup_{O≠0} ‖T(O)‖_{ρ_β} / ‖O‖_{ρ_β}`, (2.2), valued in
`ℝ≥0∞`. -/
noncomputable def kmsOpNorm (β : ℝ) (H : Matrix ι ι ℂ) (T : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    ENNReal :=
  ⨆ O : {O : Matrix ι ι ℂ // O ≠ 0},
    ENNReal.ofReal (kmsNorm β H (T O.1) / kmsNorm β H O.1)

/-- The map on relative densities `T̂ = Γ⁻¹ T Γ`, p.11. -/
noncomputable def onRelDens (β : ℝ) (H : Matrix ι ι ℂ) (T : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    Matrix ι ι ℂ → Matrix ι ι ℂ :=
  fun O => Gam β H (-1) (T (Gam β H 1 O))

/-- The Hilbert–Schmidt adjoint `T†`, determined by `Tr(O† T(P)) = Tr((T†(O))† P)`, (2.1).
Taking `P` a matrix unit `E_{kl}` gives `(T†(O))_{kl} = conj Tr(O† T(E_{kl}))`, which is this
definition. -/
noncomputable def hsAdjoint (T : Matrix ι ι ℂ → Matrix ι ι ℂ) : Matrix ι ι ℂ → Matrix ι ι ℂ :=
  fun O => Matrix.of fun k l =>
    star (Matrix.trace (Oᴴ * T (Matrix.single k l 1)))

/-- Complex-time evolution `O(z) = e^{izH} O e^{-izH}`, (2.7). -/
noncomputable def evo (H : Matrix ι ι ℂ) (z : ℂ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((Complex.I * z) • H) * O * NormedSpace.exp ((-(Complex.I * z)) • H)

/-- The forward evolution `U(t)(O) = e^{-itH} O e^{itH} = O(-t)`, (2.7). -/
noncomputable def fwd (H : Matrix ι ι ℂ) (t : ℝ) (O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  evo H (-(t : ℂ)) O

/-- The commutator `[B, C] = BC - CB`, p.11. -/
def comm {κ : Type} [Fintype κ] (B C : Matrix κ κ ℂ) : Matrix κ κ ℂ := B * C - C * B

/-- The anticommutator `{B, C} = BC + CB`, p.11. -/
def acomm {κ : Type} [Fintype κ] (B C : Matrix κ κ ℂ) : Matrix κ κ ℂ := B * C + C * B

/-- A sum over Bohr frequencies, `∑_ν f(ν) O_ν`, with `O_ν = ∑_{E-E'=ν} Π_E O Π_{E'}`, (2.9). In an
eigenbasis `U` of the Hermitian `H`, with eigenvalues `λ`, the entry `(i, j)` of `U†OU` belongs to
the frequency `λ_i - λ_j`; so the sum is computed entrywise there and conjugated back. The result
does not depend on the eigenbasis. For non-Hermitian `H`, which never occurs, the value is `0`. -/
noncomputable def bohrSum (f : ℝ → ℂ) (H O : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if hH : H.IsHermitian then
    (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      (Matrix.of fun i j =>
        f (hH.eigenvalues i - hH.eigenvalues j) *
          (((hH.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ * O *
            (hH.eigenvectorUnitary : Matrix ι ι ℂ)) i j) *
      ((hH.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ
  else 0

/-- The exponential `e^{sL} = ∑_k (s^k/k!) L^k` of a superoperator. -/
noncomputable def superExp (s : ℝ) (L : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    Matrix ι ι ℂ → Matrix ι ι ℂ :=
  fun O => Matrix.of fun i j =>
    ∑' k : ℕ, ((s ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) * (L^[k] O) i j

end SysBathGibbs


