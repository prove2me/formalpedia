-- Prove2me | Definitions.Def_StationarityTest_Fisher
-- name    : StationarityTest_Fisher
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:18.30467+00:00
-- url     : https://prove2.me/theorems/1cadd2d0-dcaa-423c-8ea4-9ed00164f5de
-- title:
--   Weighted inner products $\langle X,Y\rangle_{\rho,s}$, the KMS norm, the Fisher information $\mathrm{FI}_{G,a}$ and the functional $\mathcal Q_a$
-- statement:
--   For a full-rank state $\rho$ and $s\in[-\tfrac12,\tfrac12]$,
--
--   $$\langle X,Y\rangle_{\rho,s}=\operatorname{tr}\big[X^\dagger\rho^{1/2+s}Y\rho^{1/2-s}\big],\qquad\|X\|_{\rho,s}^2=\langle X,X\rangle_{\rho,s},\qquad\|X\|_\rho=\|X\|_{\rho,0}.$$
--
--   $\|X\|_\tau$ denotes the KMS norm of the maximally mixed state $\tau=I/2^{nq}$, that is, the normalized Hilbert–Schmidt norm. An operator is **supported on** $R\subseteq[n]$ if it is a combination of Pauli strings supported in $R$. The **Fisher information** of a full-rank state $\sigma$ relative to $\rho_G$, for the jump $A^a$, is
--
--   $$\mathrm{FI}_{G,a}(\sigma\|\rho_G)=-\operatorname{Tr}\big[\mathcal L_{G,a}[\sigma](\log\sigma-\log\rho_G)\big],\qquad \mathrm{FI}_{G,i}=\sum_{a\in S_i}\mathrm{FI}_{G,a}.$$
--
--   With $h(\omega)=e^{-\sigma^2\beta^2/8}e^{-|\omega|\beta/2}$,
--
--   $$h_s(\omega)=\exp\Big(\frac{s\beta(2\omega-s\beta\sigma^2)}2\Big)h(\omega-s\beta\sigma^2),\qquad g_s(t)=\frac2\beta\,\frac{\cos(\pi s)\cosh(2\pi t/\beta)}{\cosh(4\pi t/\beta)+\cos(2\pi s)},$$
--
--   the functional is
--
--   $$\mathcal Q_a(X,G;\sigma)=\int_{-1/2}^{1/2}\int_{\mathbb R}\int_{\mathbb R}\big\|[\hat A^a_G(\omega,t),X]\big\|^2_{\sigma,s}\,h_s(\omega)g_s(t)\,dt\,d\omega\,ds.$$
--
--   Throughout $\sigma=\beta^{-1}$ for the energy width.
--
--   These quantities carry the soundness analysis: the Fisher information is measured by stationarity tests and controls local coefficient errors.
--
--   **Formalization Note** Powers and logarithms of states use the continuous functional calculus, and every state they are applied to is full rank. Squared norms are real parts. The Fisher information is defined by the first expression of (47), and its equality with $\mathcal Q_a$ is a milestone. At $s=\pm\frac12$, $g_s$ is $0/0$ only at $t=0$, a null set. The paper does not define $\tau_R$ in Lemma 3.6; reading it as the maximally mixed state is recorded there.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Definition 2.4, (26)–(27), p.15; (46), Definition 2.21, (47)–(49), p.18; Lemma 3.6, p.21

import Definitions.Def_StationarityTest_Lindbladian

open Matrix MeasureTheory

namespace StationarityTest

/-!
# Weighted inner products, the Fisher information and the functional `Q_a`

T. Bergamaschi, *The stationarity test*, arXiv:2610.01074 (held file sha256 0b7e46fb…),
Definition 2.4, (26)–(27), p.15; (46), Definition 2.21, (47)–(49), p.18; Lemma 3.6, (59), p.21.

**Formalization Note.** Real powers and the logarithm of a state are the continuous functional
calculus (`cfc`) of the Hermitian matrix; all states they are applied to are full rank (positive
definite), as the paper assumes throughout §2.2. `∥X∥²_{ρ,s}` is the real part of
`⟨X, X⟩_{ρ,s}` (which is real and nonnegative). The Fisher information is defined by the first
expression of (47), `−Tr[L_{G,a}[σ](log σ − log ρ_G)]` (real part); its equality with `Q_a` is a
claimed identity, posed as a milestone. In (48) the energy width is the paper's `σ := β^{−1}`.
The `s`-integral runs over `[−1/2, 1/2]`; at `s = ±1/2` the kernel `g_s(t)` vanishes for `t ≠ 0`
and is `0/0` at `t = 0`, where Lean's `x/0 = 0` gives `0` (a null set). The iterated integrals
are Bochner integrals of real functions. The norm `∥B∥_{τ_R}` of Lemma 3.6 (τ is not defined in
the paper) is read as the KMS norm (27) of the maximally mixed state `τ = I/2^{nq}`, i.e. the
normalized Hilbert–Schmidt norm, which for `B` supported on `R` equals that of the maximally
mixed state on `R`.
-/

variable {n q : ℕ}

/-- The real power `ρ^p` of a positive (definite) matrix. -/
noncomputable def rpowM (ρ : Op n q) (p : ℝ) : Op n q :=
  cfc (fun x : ℝ => x ^ p) ρ

/-- The matrix logarithm `log ρ` of a positive definite matrix. -/
noncomputable def logM (ρ : Op n q) : Op n q :=
  cfc Real.log ρ

/-- Definition 2.4, (26): `⟨X, Y⟩_{ρ,s} := tr[X† ρ^{1/2+s} Y ρ^{1/2−s}]`. -/
noncomputable def wInner (ρ : Op n q) (s : ℝ) (X Y : Op n q) : ℂ :=
  trace (Xᴴ * rpowM ρ (1 / 2 + s) * Y * rpowM ρ (1 / 2 - s))

/-- `∥X∥²_{ρ,s}`, the square of the `(ρ, s)`-weighted 2-norm (26). -/
noncomputable def wNormSq (ρ : Op n q) (s : ℝ) (X : Op n q) : ℝ :=
  (wInner ρ s X X).re

/-- (27): the KMS norm `∥X∥_ρ = ∥X∥_{ρ,0}`. -/
noncomputable def kmsNorm (ρ : Op n q) (X : Op n q) : ℝ :=
  Real.sqrt (wNormSq ρ 0 X)

/-- The maximally mixed state `I/2^{nq}`. -/
noncomputable def maxMixed (n q : ℕ) : Op n q :=
  (((2 : ℝ) ^ (n * q))⁻¹ : ℂ) • (1 : Op n q)

/-- `∥B∥_{τ}`: the KMS norm of the maximally mixed state (Lemma 3.6, read as above). -/
noncomputable def tauNorm (X : Op n q) : ℝ :=
  kmsNorm (maxMixed n q) X

/-- `B` is a local operator with support on the region `R ⊆ [n]`: a linear combination of Pauli
strings supported in `R` (equivalently `B = B_R ⊗ I`). -/
def SupportedOn (B : Op n q) (R : Finset (Fin n)) : Prop :=
  ∃ c : PauliString n q → ℂ, (∀ P, c P ≠ 0 → siteSupport P ⊆ R) ∧ B = ∑ P, c P • P.mat

/-- The commutator `[A, X] = AX − XA`. -/
def comm (A X : Op n q) : Op n q := A * X - X * A

/-- (46): `h(ω) = e^{−σ²β²/8} e^{−|ω|β/2}`. -/
noncomputable def hFilt (β σ ω : ℝ) : ℝ :=
  Real.exp (-(σ ^ 2 * β ^ 2 / 8)) * Real.exp (-(|ω| * β / 2))

/-- (49): `h_s(ω) := exp(sβ(2ω − sβσ²)/2) h(ω − sβσ²)`. -/
noncomputable def hS (β σ s ω : ℝ) : ℝ :=
  Real.exp (s * β * (2 * ω - s * β * σ ^ 2) / 2) * hFilt β σ (ω - s * β * σ ^ 2)

/-- (49): `g_s(t) := (2/β) cos(πs) cosh(2πt/β) / (cosh(4πt/β) + cos(2πs))`. -/
noncomputable def gS (β s t : ℝ) : ℝ :=
  2 / β * (Real.cos (Real.pi * s) * Real.cosh (2 * Real.pi * t / β)) /
    (Real.cosh (4 * Real.pi * t / β) + Real.cos (2 * Real.pi * s))

/-- (48): the functional
`Q_a(X, G; σ) := ∫_{−1/2}^{1/2} ∫_ℝ ∫_ℝ ∥[Â^a_G(ω, t), X]∥²_{σ,s} h_s(ω) g_s(t) dt dω ds`
(energy width `β^{−1}`), for the jump `A`. -/
noncomputable def funcQ (G : Op n q) (β : ℝ) (A : Op n q) (X σ : Op n q) : ℝ :=
  ∫ s in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), ∫ ω, ∫ t,
    wNormSq σ s (comm (oftT G β⁻¹ A ω t) X) * hS β β⁻¹ s ω * gS β s t

/-- Definition 2.21, (47), first expression: the Fisher information
`FI_{G,a}(σ ∥ ρ_G) := −Tr[L_{G,a}[σ](log σ − log ρ_G)]` of a full-rank state `σ` relative to the
Gibbs state `ρ_G`, for the jump `A`. -/
noncomputable def fisherInfo (G : Op n q) (β : ℝ) (A : Op n q) (σ : Op n q) : ℝ :=
  -(trace (lindblad G β A σ * (logM σ - logM (gibbs β G)))).re

/-- `FI_{G,i} := Σ_{a∈S_i} FI_{G,a}`, the Fisher information of the site generator
`L_{G,i}` (Remark 1.3, Lemma 3.3). -/
noncomputable def fisherSite (G : Op n q) (β : ℝ) (i : Fin n) (σ : Op n q) : ℝ :=
  ∑ a ∈ singleSite i, fisherInfo G β a.mat σ

end StationarityTest


