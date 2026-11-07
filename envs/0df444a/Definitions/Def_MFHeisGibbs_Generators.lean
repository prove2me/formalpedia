-- Prove2me | Definitions.Def_MFHeisGibbs_Generators
-- name    : MFHeisGibbs_Generators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:16.841+00:00
-- url     : https://prove2.me/theorems/ed6632c6-ccc2-470a-a66e-d8addd45c107
-- title:
--   The Lindbladians $\mathcal L_C$, $\mathcal L_D$, $\mathcal L_{F,\sigma}$, their $\beta=0,\infty$ forms, $\mathcal L_{IP}$ and $C_{\mathrm{ad}}$
-- statement:
--   All generators have the Heisenberg-picture form $\mathcal L[\cdot]=\mathcal T'[\cdot]-\frac12\{\mathcal T'[I],\cdot\}$, with $\mathcal T'$ summed over all sites $i$ and directions $\alpha$:
--
--   1. **Coherent**: $\mathcal T'_C[X]=\sum_{i,\alpha}(L^{(i,\alpha)})^\dagger XL^{(i,\alpha)}$, with $L^{(i,\alpha)}=\sum_\nu f(\beta\nu)\sigma^{(i,\alpha)}_\nu$.
--   2. **Davies**: $\mathcal T'_D[X]=\sum_{i,\alpha}\sum_\nu|f(\beta\nu)|^2(\sigma^{(i,\alpha)}_\nu)^\dagger X\sigma^{(i,\alpha)}_\nu$; with $f=f_M$ this is $\mathcal L_{DM}$.
--   3. **OFT**, for $\beta>0$ and width $\sigma>0$: $\mathcal T'_F=\sum_{i,\alpha}\int_{\mathbb R}\big(f(\beta\omega+\sigma^2/2)\widehat{\sigma^{(i,\alpha)}}(\omega)\big)^\dagger[\cdot]\big(f(\beta\omega+\sigma^2/2)\widehat{\sigma^{(i,\alpha)}}(\omega)\big)d\omega$, with $\widehat K(\omega)=\sum_\nu\hat g_\sigma(\omega-\nu)K_\nu$ and $\hat g_\sigma(\omega)=\sqrt{\beta/(\sigma\sqrt{2\pi})}\,e^{-\beta^2\omega^2/(4\sigma^2)}$.
--   4. **OFT at $\beta=0$**: $\mathcal L_{F,\sigma,0}[X]=b_\sigma\sum_{i,\alpha}(\sigma^{(i,\alpha)}X\sigma^{(i,\alpha)}-X)$, with $b_\sigma=\mathbb E|f(\xi_\sigma)|^2$, $\xi_\sigma\sim N(\sigma^2/2,\sigma^2)$.
--   5. **At $\beta=\infty$**: $\mathcal L_{C,\infty}$ has jumps $f_\infty(\mathrm{ad}_{H_n})(\sigma^{(i,\alpha)})$; $\mathcal L_{D,\infty}$ and $\mathcal L_{F,\sigma,\infty}$ are Davies generators with weights $c_-^2$ on $\nu<0$, $0$ on $\nu>0$ and, at $\nu=0$, $c_0^2$ and $b_\sigma$ respectively.
--
--   Also defined are the interchange generator $-\mathcal L_{IP}[\cdot]=\sum_{i<j}(\mathcal I[\cdot]-\Delta_{e,(ij)}[\cdot])$, the Casimir $C_{\mathrm{ad}}[\cdot]=\sum_\alpha[S^\alpha_{\mathrm{tot}},[S^\alpha_{\mathrm{tot}},\cdot]]$, the symmetrized jump $B^{(i,\alpha)}=\tilde f(\beta\,\mathrm{ad}_{H_n})(\sigma^{(i,\alpha)})$ and the evolution $A(t)=e^{itH_n}Ae^{-itH_n}$.
--
--   **Formalization Note** The OFT integral is stored through its Bohr expansion $\sum_{\nu,\mu}\kappa(\nu,\mu)K_\nu^\dagger[\cdot]K_\mu$, with scalar integrals $\kappa(\nu,\mu)=\int|f(\beta\omega+\sigma^2/2)|^2\hat g_\sigma(\omega-\nu)\hat g_\sigma(\omega-\mu)d\omega$, the expansion the paper uses on p.40. For bounded continuous $f$ the integrand is bounded by a Gaussian. At $\beta=0$ the printed $\hat g_\sigma$ vanishes, so literal (10) is the zero map and `LF0` is used instead. The forms at $\beta=0,\infty$ are tied to the finite-temperature generators by the milestone `eq_101_113_limits`.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (3), p.3 (PDF 4); (5), (7), (9), p.4 (PDF 5); (10), (11), p.5 (PDF 6); (100), (101), p.36 (PDF 37); (113), §7.4, pp.39–41 (PDF 40–42); Lemma 3, p.15 (PDF 16); Lemma 14, p.27 (PDF 28)

import Definitions.Def_MFHeisGibbs_Bohr
import Definitions.Def_MFHeisGibbs_Filter

open Matrix MeasureTheory ProbabilityTheory

namespace MFHeisGibbs

/-!
# The coherent, Davies and OFT Lindbladians

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(3), p.3; (5), (7), (9), p.4; (10), (11), p.5; (100), (101), p.36; (113), §7.4, pp.39–41.

**Formalization Note.** All generators are in the Heisenberg picture, as on the page.

*OFT (10).* The operator `f(βω + σ²/2) K̂(ω)` with `K̂(ω) = ∑_ν ĝ_σ(ω − ν) K_ν` (the Bohr form of (11))
gives, on expanding the integrand, `∑_{ν,μ} κ(ν, μ) (K_ν)† [·] K_μ`, with the scalar integral
`κ(ν, μ) = ∫ |f(βω + σ²/2)|² ĝ_σ(ω − ν) ĝ_σ(ω − μ) dω`. Here `transF` uses this expansion. For bounded
continuous `f` the integrand is bounded by a Gaussian, so nothing is a junk value.

*β = 0.* At `β = 0` the printed `ĝ_σ` vanishes identically, so literal (10) is the zero map. The page
defines `L_{F,σ,0}` as the limit `β → 0⁺` (p.41), and `LF0` is the formula it gives; the limit is the
milestone `eq_101_113_limits`.

*β = ∞.* `LCinf`, `LDinf`, `LFinf` are the formulas (100), (101), (113), which the page obtains as
limits, again stated in `eq_101_113_limits`. `(101)` and `(113)` are written on the page for the
Schrödinger-picture adjoint, `L†_A[X] = AXA† − ½{A†A, X}`; these are their Heisenberg-picture forms.
By Fact 2.1 of the paper, `fInf c₀ c₋ (ad_{H_n})(σ)` equals the operator of (100).
-/

/-- The Heisenberg-picture Lindbladian form `L[·] = T′[·] − ½{T′[I], ·}`, (3). -/
noncomputable def lindbladOf {n : ℕ} (T : Op n →ₗ[ℂ] Op n) : Module.End ℂ (Op n) :=
  T - (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ (T 1) + LinearMap.mulRight ℂ (T 1))

/-- The completely positive map `X ↦ A† X A`. -/
noncomputable def sandwich {n : ℕ} (A : Op n) : Op n →ₗ[ℂ] Op n := conjMap Aᴴ A

/-- The coherent transition map `∑_{i,α} (∑_ν h(ν) σ^(i,α)_ν)† [·] (∑_ν h(ν) σ^(i,α)_ν)`, (9). -/
noncomputable def transC (h : ℝ → ℂ) (n : ℕ) : Op n →ₗ[ℂ] Op n :=
  ∑ i : Fin n, ∑ α : Fin 3, sandwich (sigFilter h i α)

/-- The Davies transition map `∑_{i,α} ∑_ν w(ν) (σ^(i,α)_ν)† [·] σ^(i,α)_ν`, with real weights, (5). -/
noncomputable def transD (w : ℝ → ℝ) (n : ℕ) : Op n →ₗ[ℂ] Op n :=
  ∑ i : Fin n, ∑ α : Fin 3, ∑ ν ∈ bohr n, (w ν : ℂ) • sandwich (sig i α ν)

/-- The coherent Lindbladian `L_C` at inverse temperature `β`, (9), (37). -/
noncomputable def LC (β : ℝ) (f : ℝ → ℂ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transC (fun ν => f (β * ν)) n)

/-- The Davies Lindbladian `L_D` at inverse temperature `β`, (5), (7): the weight is
`|f(βν)|²`. -/
noncomputable def LD (β : ℝ) (f : ℝ → ℂ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transD (fun ν => ‖f (β * ν)‖ ^ 2) n)

/-- The Davies–Metropolis generator `L_DM`, p.4. -/
noncomputable def LDM (β : ℝ) (n : ℕ) : Module.End ℂ (Op n) := LD β fM n

/-- The Gaussian `ĝ_σ(ω) = √(β/(σ√(2π))) e^{−β²ω²/(4σ²)}`, (11). The width `σ` is `s` in Lean, as
`σ` is the Pauli operator. -/
noncomputable def gHat (β s ω : ℝ) : ℝ :=
  Real.sqrt (β / (s * Real.sqrt (2 * Real.pi))) * Real.exp (-(β ^ 2 * ω ^ 2) / (4 * s ^ 2))

/-- The coefficient `κ(ν, μ) = ∫ |f(βω + σ²/2)|² ĝ_σ(ω − ν) ĝ_σ(ω − μ) dω` obtained by expanding (10)
in Bohr frequencies. -/
noncomputable def oftKernel (β s : ℝ) (f : ℝ → ℂ) (ν μ : ℝ) : ℝ :=
  ∫ ω : ℝ, ‖f (β * ω + s ^ 2 / 2)‖ ^ 2 * gHat β s (ω - ν) * gHat β s (ω - μ)

/-- The OFT transition map of (10), summed over `i, α`, in its Bohr expansion. -/
noncomputable def transF (β s : ℝ) (f : ℝ → ℂ) (n : ℕ) : Op n →ₗ[ℂ] Op n :=
  ∑ i : Fin n, ∑ α : Fin 3, ∑ ν ∈ bohr n, ∑ μ ∈ bohr n,
    (oftKernel β s f ν μ : ℂ) • conjMap (sig i α ν)ᴴ (sig i α μ)

/-- The OFT Lindbladian `L_{F,σ}` at inverse temperature `β > 0`, (10). -/
noncomputable def LF (β s : ℝ) (f : ℝ → ℂ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transF β s f n)

/-- `b_σ = E[|f(ξ_σ)|²]`, `ξ_σ ~ N(σ²/2, σ²)`, p.40. -/
noncomputable def bSigma (s : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, ‖f u‖ ^ 2 ∂(gaussianReal (s ^ 2 / 2) (s ^ 2).toNNReal)

/-- The infinite-temperature OFT generator `L_{F,σ,0}[X] = b_σ ∑_{i,α} (σ^{i,α} X σ^{i,α} − X)`,
p.41. -/
noncomputable def LF0 (s : ℝ) (f : ℝ → ℂ) (n : ℕ) : Module.End ℂ (Op n) :=
  (bSigma s f : ℂ) • ∑ i : Fin n, ∑ α : Fin 3, (conjMap (pauliAt i α) (pauliAt i α) - LinearMap.id)

/-- The OFT generator at every finite `β ≥ 0`: `LF` for `β > 0` and `LF0` at `β = 0`. -/
noncomputable def LFall (β s : ℝ) (f : ℝ → ℂ) (n : ℕ) : Module.End ℂ (Op n) :=
  if β = 0 then LF0 s f n else LF β s f n

/-- The zero-temperature coherent generator `L_{C,∞}`, (100), (101). -/
noncomputable def LCinf (c₀ cm : ℝ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transC (fun ν => (fInf c₀ cm ν : ℂ)) n)

/-- The zero-temperature Davies generator `L_{D,∞}`, (101): weights `c₋²` on `ν < 0`, `c₀²` on
`ν = 0`, `0` on `ν > 0`. -/
noncomputable def LDinf (c₀ cm : ℝ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transD (fun ν => fInf c₀ cm ν ^ 2) n)

/-- The zero-temperature OFT generator `L_{F,σ,∞}`, (113), with `b = b_σ`: weights `c₋²` on `ν < 0`,
`b` on `ν = 0`, `0` on `ν > 0`. -/
noncomputable def LFinf (cm b : ℝ) (n : ℕ) : Module.End ℂ (Op n) :=
  lindbladOf (transD (fun ν => if ν < 0 then cm ^ 2 else if ν = 0 then b else 0) n)

/-- The interchange Lindbladian `−L_IP[·] = ∑_{i<j} (I[·] − ∆_{e,(ij)}[·])`, p.15, with
`∆_{e,(ij)}[·] = U_(ij) [·] U_(ij)†`. -/
noncomputable def LIP (n : ℕ) : Module.End ℂ (Op n) :=
  -∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (LinearMap.id - conjMap (swapOp i j) (swapOp i j)ᴴ)

/-- The Casimir `C_ad[·] = ∑_α [S^α_tot, [S^α_tot, ·]]`, Lemma 14. -/
noncomputable def Cad (n : ℕ) : Module.End ℂ (Op n) :=
  ∑ α : Fin 3, (LinearMap.mulLeft ℂ (Stot n α) - LinearMap.mulRight ℂ (Stot n α)) ^ 2

/-- The symmetrized jump `B^(i,α) = f̃(β ad_{H_n})(σ^(i,α))`, (36). -/
noncomputable def Bjump (β : ℝ) (f : ℝ → ℂ) {n : ℕ} (i : Fin n) (α : Fin 3) : Op n :=
  sigFilter (fun ν => fTilde f (β * ν)) i α

/-- The Heisenberg evolution `A(t) = e^{itH_n} A e^{−itH_n}`, p.42. -/
noncomputable def heisEvol {n : ℕ} (t : ℝ) (A : Op n) : Op n :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • Hn n) * A * NormedSpace.exp ((-(Complex.I * (t : ℂ))) • Hn n)

end MFHeisGibbs


