-- Prove2me | Definitions.Def_Weinberg1965_Defs
-- name    : Weinberg1965_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T22:52:18.263388+00:00
-- url     : https://prove2.me/theorems/0ef762ed-300e-4f20-8b99-22211d33e4be
-- title:
--   Weinberg (1965): Minkowski products, relative velocity, soft angular functions $A(\hat q)$, $B(\hat q)$ and exponents $A$, $B$
-- statement:
--   Shared definitions for the mission on S. Weinberg, *Infrared Photons and Gravitons* (1965). Units $\hbar=c=1$ and the paper's metric (footnote 7): for four-vectors $p=(\mathbf p,p^0)$, $q=(\mathbf q,q^0)$, $p\cdot q=\mathbf p\cdot\mathbf q-p^0q^0$, so $p\cdot p=-m^2$ on the mass shell.
--
--   The external lines of a process $\alpha\to\beta$ are indexed by a finite set; line $n$ has mass $m_n$, three-momentum $\mathbf p_n\in\mathbb R^3$, charge $e_n$ and sign $\eta_n=+1$ (outgoing) or $-1$ (incoming).
--
--   1. **`Vec3`** — Euclidean space $\mathbb R^3$.
--   2. **`solidAngleIntegral F`** — $\int d^2\Omega\,F(\hat q)$, the integral of $F$ over the unit sphere $S^2$ against surface measure (total solid angle $4\pi$).
--   3. **`energy m p`** — the on-shell energy $E=\sqrt{|\mathbf p|^2+m^2}$.
--   4. **`mdot m₁ p₁ m₂ p₂`** — the Minkowski product $p_1\cdot p_2=\mathbf p_1\cdot\mathbf p_2-E_1E_2$ of on-shell four-momenta.
--   5. **`mdotNull m p q`** — $p\cdot q=\mathbf p\cdot\mathbf q-E|\mathbf q|$ for the null four-vector $q=(\mathbf q,|\mathbf q|)$ of a soft photon or graviton.
--   6. **`relVel`** — Eq. (2.17): $\beta_{nm}=\bigl[1-m_n^2m_m^2/(p_n\cdot p_m)^2\bigr]^{1/2}$, the relative velocity of $n$ and $m$ in the rest frame of either.
--   7. **`photonAngular`** — Eq. (2.15):
--   $$A(\hat q)=\frac{1}{2(2\pi)^3}\sum_{n,m}\frac{e_ne_m\eta_n\eta_m\,(p_n\cdot p_m)}{[E_n-\mathbf p_n\cdot\hat q][E_m-\mathbf p_m\cdot\hat q]}.$$
--   8. **`photonIndex`** — Eq. (2.14): $A=\int d^2\Omega\,A(\hat q)$.
--   9. **`gravitonAngular`** — Eq. (2.25):
--   $$B(\hat q)=\frac{8\pi G}{2(2\pi)^3}\sum_{n,m}\frac{\eta_n\eta_m\,\{(p_n\cdot p_m)^2-\tfrac12m_n^2m_m^2\}}{[E_n-\mathbf p_n\cdot\hat q][E_m-\mathbf p_m\cdot\hat q]}.$$
--   10. **`gravitonIndex`** — Eq. (2.24): $B=\int d^2\Omega\,B(\hat q)$.
--   11. **`photonKernel β`** — the pair kernel of Eq. (2.16), $\beta^{-1}\ln\frac{1+\beta}{1-\beta}$ for $\beta\ne0$, and its limiting value $2$ at $\beta=0$.
--   12. **`fWeinberg β`** — Eq. (4.6): $f(\beta)=\dfrac{1+\beta^2}{2\beta(1-\beta^2)^{1/2}}\ln\dfrac{1+\beta}{1-\beta}$ for $\beta\ne0$, and its limiting value $1$ at $\beta=0$.
--
--   These are the angular functions and spectral indices $A$, $B$ that control the infrared factors $(\lambda/\Lambda)^A$, $(\lambda/\Lambda)^B$ of Eqs. (2.18), (2.27) and the soft emission spectra (2.51), (2.52).
--
--   **Formalization Note** The printed Eq. (4.6) carries an exponent $1/2$ on the argument of the logarithm; with it, $f(0)=\tfrac12$, which contradicts both Eq. (2.26) (via (4.5)) and the expansion (4.9) $f=1+\tfrac{11}{6}\beta^2+\cdots$. The definition drops that exponent, which is the reading consistent with (2.26), (4.5) and (4.9). The diagonal terms $n=m$ have $\beta_{nn}=0$; the kernels are extended there by their limits ($2$ and $1$), as the paper's sums implicitly require.
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, Sec. II (Eqs. (2.14)–(2.17), (2.24)–(2.25)), footnote 7; Sec. IV (Eq. (4.6))

import Mathlib

/-!
# Weinberg (1965), *Infrared Photons and Gravitons* — definitions

Conventions of the paper (footnote 7): `ħ = c = 1`, and the Minkowski product of
four-vectors `p = (𝐩, p⁰)`, `q = (𝐪, q⁰)` is `p · q = 𝐩 · 𝐪 − p⁰ q⁰`, so a particle of
mass `m` has `p · p = −m²`.

The external lines of a process `α → β` are indexed by a finite type `ι`.  Line `n` carries
a mass `m n`, a three-momentum `p n ∈ ℝ³`, an energy `E_n = √(|𝐩_n|² + m_n²)` (on the mass
shell), a charge `e n`, and a sign `η n` (`+1` outgoing, `−1` incoming).

Solid-angle integrals `∫ d²Ω` are integrals over the unit sphere `S² ⊂ ℝ³` against the
surface-area measure (total mass `4π`), realised in Mathlib as `volume.toSphere`.
-/

namespace Weinberg1965

open MeasureTheory

/-- Three-dimensional Euclidean space `ℝ³` (spatial momenta and directions). -/
abbrev Vec3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The solid-angle integral `∫ d²Ω F(q̂)` of a real function over the unit sphere
`S² ⊂ ℝ³`, taken with respect to the surface-area measure (total solid angle `4π`). -/
noncomputable def solidAngleIntegral (F : Vec3 → ℝ) : ℝ :=
  ∫ u : Metric.sphere (0 : Vec3) 1, F (u : Vec3) ∂(volume.toSphere)

/-- On-shell energy `E = √(|𝐩|² + m²)` of a particle of mass `m` and three-momentum `𝐩`. -/
noncomputable def energy (m : ℝ) (p : Vec3) : ℝ :=
  Real.sqrt (‖p‖ ^ 2 + m ^ 2)

/-- Minkowski product (footnote 7) of the on-shell four-momenta `(𝐩₁, E₁)` and `(𝐩₂, E₂)`
of particles of masses `m₁, m₂`: `p₁ · p₂ = 𝐩₁ · 𝐩₂ − E₁ E₂`. -/
noncomputable def mdot (m₁ : ℝ) (p₁ : Vec3) (m₂ : ℝ) (p₂ : Vec3) : ℝ :=
  inner ℝ p₁ p₂ - energy m₁ p₁ * energy m₂ p₂

/-- Minkowski product `p · q = 𝐩 · 𝐪 − E |𝐪|` of the on-shell four-momentum of a particle of
mass `m` and three-momentum `𝐩` with the null four-vector `q = (𝐪, |𝐪|)` (a soft photon or
graviton of three-momentum `𝐪`). -/
noncomputable def mdotNull (m : ℝ) (p : Vec3) (q : Vec3) : ℝ :=
  inner ℝ p q - energy m p * ‖q‖

/-- Eq. (2.17): the relative velocity of particles `n` and `m` in the rest frame of either,
`β_{nm} = [1 − m_n² m_m² / (p_n · p_m)²]^{1/2}`. -/
noncomputable def relVel (m₁ : ℝ) (p₁ : Vec3) (m₂ : ℝ) (p₂ : Vec3) : ℝ :=
  Real.sqrt (1 - m₁ ^ 2 * m₂ ^ 2 / (mdot m₁ p₁ m₂ p₂) ^ 2)

/-- Eq. (2.15): the photon angular function
`A(q̂) = (1 / (2(2π)³)) ∑_{n,m} e_n e_m η_n η_m (p_n · p_m) / ([E_n − 𝐩_n · q̂][E_m − 𝐩_m · q̂])`. -/
noncomputable def photonAngular {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ) (u : Vec3) : ℝ :=
  (1 / (2 * (2 * Real.pi) ^ 3)) *
    ∑ n, ∑ k, e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
      ((energy (m n) (p n) - inner ℝ (p n) u) * (energy (m k) (p k) - inner ℝ (p k) u))

/-- Eq. (2.14): the infrared-photon exponent `A = ∫ d²Ω A(q̂)`. -/
noncomputable def photonIndex {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ) : ℝ :=
  solidAngleIntegral (photonAngular m p e η)

/-- Eq. (2.25): the graviton angular function
`B(q̂) = (8πG / (2(2π)³)) ∑_{n,m} η_n η_m [(p_n · p_m)² − ½ m_n² m_m²] /
([E_n − 𝐩_n · q̂][E_m − 𝐩_m · q̂])`. -/
noncomputable def gravitonAngular {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ) (u : Vec3) : ℝ :=
  (8 * Real.pi * G / (2 * (2 * Real.pi) ^ 3)) *
    ∑ n, ∑ k, η n * η k *
      ((mdot (m n) (p n) (m k) (p k)) ^ 2 - (1 / 2) * m n ^ 2 * m k ^ 2) /
      ((energy (m n) (p n) - inner ℝ (p n) u) * (energy (m k) (p k) - inner ℝ (p k) u))

/-- Eq. (2.24): the infrared-graviton exponent `B = ∫ d²Ω B(q̂)`. -/
noncomputable def gravitonIndex {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ) : ℝ :=
  solidAngleIntegral (gravitonAngular G m p η)

/-- The photon pair kernel of Eq. (2.16): `β⁻¹ ln((1+β)/(1−β))` for `β ≠ 0`, extended by its
limiting value `2` at `β = 0` (the value relevant for the diagonal terms `n = m`). -/
noncomputable def photonKernel (β : ℝ) : ℝ :=
  if β = 0 then 2 else β⁻¹ * Real.log ((1 + β) / (1 - β))

/-- Eq. (4.6), in the form consistent with Eqs. (2.26), (4.5) and (4.9) (the printed exponent
`1/2` on the argument of the logarithm is dropped):
`f(β) = (1 + β²) / (2β(1 − β²)^{1/2}) · ln((1+β)/(1−β))` for `β ≠ 0`, extended by its limiting
value `1` at `β = 0`. -/
noncomputable def fWeinberg (β : ℝ) : ℝ :=
  if β = 0 then 1
  else (1 + β ^ 2) / (2 * β * Real.sqrt (1 - β ^ 2)) * Real.log ((1 + β) / (1 - β))

end Weinberg1965


