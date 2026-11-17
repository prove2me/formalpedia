-- Prove2me | Definitions.Def_MFHeisGibbs_Supplement_Generators
-- name    : MFHeisGibbs_Supplement_Generators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:16:08.584453+00:00
-- url     : https://prove2.me/theorems/ea718160-b81d-4c86-a128-374f2d722474
-- title:
--   Coherent and OFT Lindbladians with coherent correction for a general Hamiltonian and self-adjoint jumps
-- statement:
--   Let $H$ be a Hermitian matrix on $\mathcal H_n$ with Bohr frequencies $B(H)$ and Bohr components $A_\nu$, and $0<\beta<\infty$. For a completely positive map $\mathcal T$ put $D=\mathcal T[I]$ and the coherent correction
--
--   $$C=\mathcal C_s[D]=\sum_{\xi\in B(H)}\frac i2\tanh\Big(\frac{\beta\xi}4\Big)D_\xi .$$
--
--   The KMS-detailed-balanced generator built from $\mathcal T$ is, in the Heisenberg picture,
--
--   $$\mathcal L_{\mathcal T}[X]=\mathcal T[X]-\tfrac12\{D,X\}+i[C,X].$$
--
--   1. **Coherent Lindbladian.** For a self-adjoint jump $K$ and a filter $h:\mathbb R\to\mathbb C$, the filtered jump is $L_h=\sum_{\nu\in B(H)}h(\beta\nu)K_\nu$, and $\mathcal L^{K,h}_C=\mathcal L_{\mathcal T}$ for $\mathcal T[X]=L_h^\dagger XL_h$.
--   2. **OFT Lindbladian.** With the Gaussian $\hat g_\sigma$ of (11) and $\hat K(\omega)=\sum_\nu\hat g_\sigma(\omega-\nu)K_\nu$, the map $\mathcal T^K_{F,\sigma}[X]=\int_{\mathbb R}(f(\beta\omega+\sigma^2/2)\hat K(\omega))^\dagger X(f(\beta\omega+\sigma^2/2)\hat K(\omega))\,d\omega$ gives $\mathcal L^K_{F,\sigma}=\mathcal L_{\mathcal T^K_{F,\sigma}}$.
--   3. For a finite family $\{K^{(a)}\}_{a\in A}$ of jumps, $\mathcal L^h_C=\sum_a\mathcal L^{K^{(a)},h}_C$ and $\mathcal L_{F,\sigma}=\sum_a\mathcal L^{K^{(a)}}_{F,\sigma}$.
--
--   These are the generators of Appendix B, in which no symmetry of $H$ is assumed, so the coherent correction is kept.
--
--   **Formalization Note** The OFT map is written in its Bohr expansion $\sum_{\nu,\mu\in B(H)}\kappa(\nu,\mu)K_\nu^\dagger XK_\mu$ with $\kappa(\nu,\mu)=\int|f(\beta\omega+\sigma^2/2)|^2\hat g_\sigma(\omega-\nu)\hat g_\sigma(\omega-\mu)\,d\omega$, obtained by expanding the integrand. The published mean-field generators (form (3), no correction) are not used. The width $\sigma$ is `s` in Lean.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (116), p.47 (PDF 48); Appendix B.1, p.50 (PDF 51); (10), (11), p.5 (PDF 6); (36), p.12 (PDF 13)

import Definitions.Def_MFHeisGibbs_Generators

open Matrix

namespace MFHeisGibbs

namespace Supplement

/-!
# Lindbladians with coherent correction for a general Hamiltonian and general self-adjoint jumps

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
(116), p.47 (PDF 48); Appendix B.1, p.50 (PDF 51); (10), (11), p.5 (PDF 6); (36), p.12 (PDF 13).

For a completely positive map `T`, `L_T[X] = T[X] − ½{D, X} + i[C, X]` with `D = T[I]` and
`C = Cs[D] = ∑_{ξ ∈ B(H)} (i/2) tanh(βξ/4) D_ξ` (Heisenberg picture). The coherent Lindbladian with
filter `h` and jump `K` is `L^{K,h}_C = L_T` for `T[X] = L_h† X L_h`, `L_h = ∑_ν h(βν) K_ν`; the OFT
Lindbladian is `L^K_{F,σ} = L_{T^K_{F,σ}}` with `T^K_{F,σ}` as in (10). For a finite family of jumps both
are summed over the family.

**Formalization Note.** Appendix B keeps the coherent correction, since `T[I]` need not commute with a
general `H`; the published `MFHeisGibbs.lindbladOf` has no correction and is not used. The Bohr
quantities are the published `bohrFreqs`, `bohrComp`, `bohrFilter` for the Hermitian `H`. The OFT map is
written in its Bohr expansion: `(f(βω + σ²/2) K̂(ω))† X (f(βω + σ²/2) K̂(ω))` with `K̂(ω) = ∑_ν ĝ_σ(ω − ν) K_ν`
(the Bohr form of (11)) integrates to `∑_{ν,μ} κ(ν, μ) K_ν† X K_μ`, `κ` the published `oftKernel`. The
width `σ` is `s` in Lean.
-/

variable {n : ℕ} {H : Op n}

/-- The coherent correction `Cs[D] = ∑_{ξ ∈ B(H)} (i/2) tanh(βξ/4) D_ξ`, (116), p.50. -/
noncomputable def cohCorr (hH : H.IsHermitian) (β : ℝ) (D : Op n) : Op n :=
  ∑ ξ ∈ bohrFreqs hH, ((Complex.I / 2) * (Real.tanh (β * ξ / 4) : ℂ)) • bohrComp hH D ξ

/-- The KMS-detailed-balanced generator `L_T[X] = T[X] − ½{T[I], X} + i[Cs[T[I]], X]`, (116), p.50. -/
noncomputable def genT (hH : H.IsHermitian) (β : ℝ) (T : Op n →ₗ[ℂ] Op n) : Module.End ℂ (Op n) :=
  T - (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ (T 1) + LinearMap.mulRight ℂ (T 1)) +
    Complex.I • (LinearMap.mulLeft ℂ (cohCorr hH β (T 1)) - LinearMap.mulRight ℂ (cohCorr hH β (T 1)))

/-- The filtered jump `L_h = h(β ad_H)(K) = ∑_{ν ∈ B(H)} h(βν) K_ν`, (36) with `(H_n, σ^(i,α), f)`
replaced by `(H, K, h)`. -/
noncomputable def filtJump (hH : H.IsHermitian) (β : ℝ) (h : ℝ → ℂ) (K : Op n) : Op n :=
  bohrFilter hH (fun ν => h (β * ν)) K

/-- The coherent Lindbladian `L^{K,h}_C = L_T`, `T[X] = L_h† X L_h`, of one jump, p.50. -/
noncomputable def LCK (hH : H.IsHermitian) (β : ℝ) (h : ℝ → ℂ) (K : Op n) : Module.End ℂ (Op n) :=
  genT hH β (sandwich (filtJump hH β h K))

/-- The coherent Lindbladian `L^h_C = ∑_a L^{K^(a),h}_C` of a finite family of jumps, p.50. -/
noncomputable def LCh {A : Type} [Fintype A] (hH : H.IsHermitian) (β : ℝ) (h : ℝ → ℂ)
    (K : A → Op n) : Module.End ℂ (Op n) :=
  ∑ a, LCK hH β h (K a)

/-- The OFT transition map `T^K_{F,σ}` of (10) for one jump `K`, in its Bohr expansion
`∑_{ν,μ ∈ B(H)} κ(ν, μ) K_ν† [·] K_μ`. -/
noncomputable def transFK (hH : H.IsHermitian) (β s : ℝ) (f : ℝ → ℂ) (K : Op n) :
    Op n →ₗ[ℂ] Op n :=
  ∑ ν ∈ bohrFreqs hH, ∑ μ ∈ bohrFreqs hH,
    (oftKernel β s f ν μ : ℂ) • conjMap (bohrComp hH K ν)ᴴ (bohrComp hH K μ)

/-- The OFT Lindbladian `L^K_{F,σ} = L_{T^K_{F,σ}}` of one jump, with coherent correction, p.50. -/
noncomputable def LFK (hH : H.IsHermitian) (β s : ℝ) (f : ℝ → ℂ) (K : Op n) :
    Module.End ℂ (Op n) :=
  genT hH β (transFK hH β s f K)

/-- The OFT Lindbladian `L_{F,σ} = ∑_a L^{K^(a)}_{F,σ}` of a finite family of jumps, p.50. -/
noncomputable def LFfam {A : Type} [Fintype A] (hH : H.IsHermitian) (β s : ℝ) (f : ℝ → ℂ)
    (K : A → Op n) : Module.End ℂ (Op n) :=
  ∑ a, LFK hH β s f (K a)

end Supplement

end MFHeisGibbs


