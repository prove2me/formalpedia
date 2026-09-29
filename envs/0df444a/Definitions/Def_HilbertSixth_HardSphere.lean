-- Prove2me | Definitions.Def_HilbertSixth_HardSphere
-- name    : HilbertSixth_HardSphere
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T03:41:04.433017+00:00
-- url     : https://prove2.me/theorems/8caf7bf3-604f-41c0-8636-d79e424b15d0
-- title:
--   Hard-sphere dynamics, grand canonical ensemble and correlation functions
-- statement:
--   Formalization of the microscopic model: Definition 1.1 (hard-sphere dynamics and flow maps) and Definition 1.3 (grand canonical ensemble, evolved densities, rescaled correlation functions) of arXiv:2503.01800.
--
--   A *hard-sphere trajectory* of $N$ spheres of diameter $\varepsilon$ is a motion in which the spheres never overlap, every particle travels at its current velocity, velocities are left-continuous and change only at contacts, and at a simple binary contact the outgoing velocities are the elastic reflections
--
--   $$v_i^{+} = v_i - ((v_i - v_j)\cdot\omega)\,\omega, \qquad v_j^{+} = v_j + ((v_i - v_j)\cdot\omega)\,\omega, \qquad \omega = \frac{x_i - x_j}{\varepsilon}.$$
--
--   A *hard-sphere flow* bundles the flow maps $H_N(t)$ with the properties listed in Proposition 1.2: they form a semigroup of measure-preserving bijections of the non-overlapping domain, and for almost every initial configuration the orbit is a hard-sphere trajectory.
--
--   On top of the flow, the grand canonical ensemble with one-particle profile $n_0$, collision rate $\alpha$ and diameter $\varepsilon$ is defined by the partition function and the initial densities
--
--   $$Z = \sum_{N\ge 0} \frac{(\alpha \varepsilon^{-(d-1)})^N}{N!} \int_{\mathcal{D}_N} \prod_j n_0(z_j)\,\mathrm{d}z_N, \qquad W_{0,N}(z_N) = \frac{(\alpha\varepsilon^{-(d-1)})^N}{Z} \prod_j n_0(z_j)\, \mathbf{1}_{\mathcal{D}_N}(z_N),$$
--
--   transported by the flow, $W_N(t) = W_{0,N}\circ H_N(t)^{-1}$, and by the rescaled $s$-particle correlation functions
--
--   $$f_s(t, z_s) = (\alpha^{-1}\varepsilon^{d-1})^s \sum_{n \ge 0} \frac{1}{n!} \int W_{s+n}(t, z_s, y_n)\,\mathrm{d}y_n .$$
--
--   All definitions are parameterized by the separation function and by the region over which positions are integrated, so that the torus model and the whole-space model of arXiv:2408.07818 share them.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, Section 1.2, Definition 1.1, Proposition 1.2, Definition 1.3 (eq. 1.3-1.13); Deng--Hani--Ma, Long time derivation of the Boltzmann equation from hard sphere dynamics, https://arxiv.org/abs/2408.07818, Definitions 1.1, 1.3 (eq. 1.1-1.11)

import Definitions.Def_HilbertSixth_Geometry

/-!
# The hard-sphere particle system and its grand canonical ensemble

Formalization of Definition 1.1 (hard-sphere dynamics), Definition 1.3 (grand
canonical ensemble, evolved densities and rescaled correlation functions) of
Deng–Hani–Ma, *Hilbert's sixth problem: derivation of fluid equations via
Boltzmann's kinetic theory* (arXiv:2503.01800); the same definitions, read with
`sep = euclSep` and `R = Set.univ`, are Definitions 1.1 and 1.3 of the companion
paper arXiv:2408.07818.

Everything is parameterized by the separation function `sep` used for the particle
centres and by the region `R` over which positions are integrated, so that the
periodic model (`sep = torusDist`, `R = box d`) and the whole-space model
(`sep = euclSep`, `R = Set.univ`) share one set of definitions.
-/

open MeasureTheory Filter

namespace HilbertSixth

/-- **Definition 1.1 (hard-sphere dynamics).**  `IsHardSphereTrajectory N ε sep z`
says that `z : ℝ → Config d N`, restricted to `t ≥ 0`, is a trajectory of the system
of `N` hard spheres of diameter `ε`:

* the spheres never overlap: `sep (x_i t) (x_j t) ≥ ε` for `i ≠ j`;
* velocities are left-continuous, `v_j t = v_j t⁻`;
* positions travel at the current velocity, `x_j t = x_j 0 + ∫₀ᵗ v_j`;
* a particle involved in no collision at time `t` keeps its velocity there;
* at a simple binary collision of `i` and `j` at time `t` (i.e. the centres of `i`
  and `j` are exactly `ε` apart and no third particle touches either of them), the
  outgoing velocities are given by the elastic reflection law
  `v_i t⁺ = v_i t - ((v_i t - v_j t) · ω) ω`, `v_j t⁺ = v_j t + ((v_i t - v_j t) · ω) ω`
  with `ω = (x_i t - x_j t)/ε ∈ S^{d-1}` (shortest representative of the difference). -/
def IsHardSphereTrajectory {d : ℕ} (N : ℕ) (ε : ℝ) (sep : Vec d → Vec d → ℝ)
    (z : ℝ → Config d N) : Prop :=
  (∀ t : ℝ, 0 ≤ t → z t ∈ domain sep N ε) ∧
  (∀ (j : Fin N) (t : ℝ), 0 ≤ t →
      ContinuousWithinAt (fun s : ℝ => (z s j).2) (Set.Iic t) t) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ j : Fin N,
      (z t j).1 = (z 0 j).1 + ∫ s in (0 : ℝ)..t, (z s j).2) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ j : Fin N,
      (∀ i : Fin N, i ≠ j → sep (z t i).1 (z t j).1 ≠ ε) →
      ContinuousWithinAt (fun s : ℝ => (z s j).2) (Set.Ici t) t) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ i j : Fin N, i ≠ j →
      sep (z t i).1 (z t j).1 = ε →
      (∀ k : Fin N, k ≠ i → k ≠ j →
        sep (z t k).1 (z t i).1 ≠ ε ∧ sep (z t k).1 (z t j).1 ≠ ε) →
      Tendsto (fun s : ℝ => (z s i).2) (nhdsWithin t (Set.Ioi t))
          (nhds ((z t i).2 -
            dotp ((z t i).2 - (z t j).2) (ε⁻¹ • repVec ((z t i).1 - (z t j).1)) •
              (ε⁻¹ • repVec ((z t i).1 - (z t j).1)))) ∧
      Tendsto (fun s : ℝ => (z s j).2) (nhdsWithin t (Set.Ioi t))
          (nhds ((z t j).2 +
            dotp ((z t i).2 - (z t j).2) (ε⁻¹ • repVec ((z t i).1 - (z t j).1)) •
              (ε⁻¹ • repVec ((z t i).1 - (z t j).1)))))

/-- **Definition 1.1 (4) / Proposition 1.2.**  A hard-sphere flow: a family of maps
`H_N(t)` on `N`-particle configurations which, for almost every initial
configuration in the non-overlapping domain, produces the hard-sphere trajectory of
Definition 1.1, and which is a measure-preserving bijective semigroup on that
domain. -/
structure HardSphereFlow (d N : ℕ) (ε : ℝ) (sep : Vec d → Vec d → ℝ) where
  /-- The flow map `H_N(t)`. -/
  H : ℝ → Config d N → Config d N
  /-- `H_N(0)` is the identity. -/
  H_zero : H 0 = id
  /-- The non-overlapping domain is preserved. -/
  maps_domain : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ domain sep N ε, H t z ∈ domain sep N ε
  /-- The semigroup (flow) property `H_N(t + s) = H_N(t) ∘ H_N(s)` for `t, s ≥ 0`. -/
  semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → H (t + s) = H t ∘ H s
  /-- Each `H_N(t)` is a bijection. -/
  bijective : ∀ t : ℝ, 0 ≤ t → Function.Bijective (H t)
  /-- Each `H_N(t)` preserves Lebesgue measure on the non-overlapping domain. -/
  measure_preserving : ∀ t : ℝ, 0 ≤ t →
    MeasurePreserving (H t) (volume.restrict (domain sep N ε))
      (volume.restrict (domain sep N ε))
  /-- For almost every initial configuration the orbit is a hard-sphere trajectory. -/
  trajectory : ∀ᵐ z ∂(volume.restrict (domain sep N ε)),
    IsHardSphereTrajectory N ε sep (fun t => H t z)

/-- **Definition 1.3 (1.10) — the partition function.**
`Z = ∑_{N ≥ 0} (α ε^{-(d-1)})^N / N! ∫_{D_N} ∏_j n₀(z_j) dz_N`, the positions being
integrated over `R` (a fundamental domain of the torus, or all of `ℝ^d`).  The term
`N = 0` contributes `1`. -/
noncomputable def partitionFunction (d : ℕ) (α ε : ℝ) (sep : Vec d → Vec d → ℝ)
    (R : Set (Vec d)) (n₀ : Vec d → Vec d → ℝ) : ℝ :=
  ∑' N : ℕ, ((Nat.factorial N : ℝ))⁻¹ * (α * ε ^ (1 - (d : ℤ))) ^ N *
    ∫ z in region R N ∩ domain sep N ε, ∏ j, n₀ (z j).1 (z j).2

/-- **Definition 1.3 (1.9) — the initial density of the grand canonical ensemble.**
`W_{0,N}(z_N) = Z⁻¹ (α ε^{-(d-1)})^N ∏_j n₀(z_j) 1_{D_N}(z_N)`. -/
noncomputable def initialDensity (d : ℕ) (α ε : ℝ) (sep : Vec d → Vec d → ℝ)
    (R : Set (Vec d)) (n₀ : Vec d → Vec d → ℝ) (N : ℕ) (z : Config d N) : ℝ :=
  (partitionFunction d α ε sep R n₀)⁻¹ * (α * ε ^ (1 - (d : ℤ))) ^ N *
    (∏ j, n₀ (z j).1 (z j).2) * domainIndicator sep N ε z

/-- **Definition 1.3 (1.12) — the evolved density.**
`W_N(t) = S_N(t) W_{0,N}`, that is `W_N(t, z_N) = W_{0,N}(H_N(t)⁻¹ z_N)`. -/
noncomputable def evolvedDensity {d : ℕ} {ε : ℝ} {sep : Vec d → Vec d → ℝ}
    (Φ : ∀ N, HardSphereFlow d N ε sep) (W₀ : ∀ N, Config d N → ℝ) (t : ℝ) (N : ℕ)
    (z : Config d N) : ℝ :=
  W₀ N (Function.invFun ((Φ N).H t) z)

/-- **Definition 1.3 (1.13) — the rescaled `s`-particle correlation function.**
`f_s(z_s) = (α⁻¹ ε^{d-1})^s ∑_{n ≥ 0} (1/n!) ∫ W_{s+n}(z_s, y_n) dy_n`, the extra
positions being integrated over `R`. -/
noncomputable def correlation (d : ℕ) (α ε : ℝ) (R : Set (Vec d))
    (W : ∀ N, Config d N → ℝ) (s : ℕ) (zs : Config d s) : ℝ :=
  (α⁻¹ * ε ^ ((d : ℤ) - 1)) ^ s *
    ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ * ∫ y in region R n, W (s + n) (Fin.append zs y)

/-- The `s`-particle correlation function at time `t` of the hard-sphere system with
collision rate `α`, diameter `ε` and one-particle initial profile `n₀`, i.e. the
composite of `initialDensity`, `evolvedDensity` and `correlation`. -/
noncomputable def corrOfFlow (d : ℕ) (α ε : ℝ) (sep : Vec d → Vec d → ℝ)
    (R : Set (Vec d)) (n₀ : Vec d → Vec d → ℝ)
    (Φ : ∀ N, HardSphereFlow d N ε sep) (t : ℝ) (s : ℕ) (zs : Config d s) : ℝ :=
  correlation d α ε R
    (evolvedDensity Φ (initialDensity d α ε sep R n₀) t) s zs

/-- The one-particle correlation function `f₁(t, x, v)` of the hard-sphere system,
i.e. `corrOfFlow` with `s = 1` evaluated at the single state `(x, v)`. -/
noncomputable def oneCorr (d : ℕ) (α ε : ℝ) (sep : Vec d → Vec d → ℝ)
    (R : Set (Vec d)) (n₀ : Vec d → Vec d → ℝ)
    (Φ : ∀ N, HardSphereFlow d N ε sep) (t : ℝ) (x v : Vec d) : ℝ :=
  corrOfFlow d α ε sep R n₀ Φ t 1 (fun _ => (x, v))

end HilbertSixth


