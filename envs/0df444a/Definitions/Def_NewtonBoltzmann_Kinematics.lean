-- Prove2me | Definitions.Def_NewtonBoltzmann_Kinematics
-- name    : NewtonBoltzmann_Kinematics
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T03:13:32.161144+00:00
-- url     : https://prove2.me/theorems/8e59aba8-6659-56f1-a56e-80ee837e5c7a
-- title:
--   Canonical marginals, collision operators and series solutions for Lanford's theorem
-- statement:
--   Core kinematic objects for Volchan's *De Newton a Boltzmann* (28º CBM, 2011), Chapter 3–4: the canonical $s$-particle marginal (eq. (3.19)); the factorized family $\prod_i f$ (Prop. 3.5); the Boltzmann–Grad relation $N\sigma^{d-1}=\alpha$; the Gaussian bound of Thm. 4.1(ii); free transport; the BBGKY collision operator $Q^\sigma_{s+1}$ (eqs. (3.33),(4.9)) and its limit $Q_{s+1}$ (eq. (4.3)); and the BBGKY/Boltzmann series (Duhamel) solutions (eqs. (4.6),(4.7)). Built on the platform hard-sphere geometry and flow interface.
-- source:
--   Volchan, De Newton a Boltzmann: o Teorema de Lanford, 28º CBM, IMPA 2011, https://library.impa.br/cbm/28CBM/28CBM_03.pdf, pp. 47–58, eqs. (3.19),(3.33),(4.3),(4.6),(4.7),(4.9); Prop. 3.5; Thm. 4.1(ii)

import Definitions.Def_HilbertSixth_Geometry
import Definitions.Def_HilbertSixth_HardSphere
import Definitions.Def_HilbertSixth_Boltzmann

open MeasureTheory HilbertSixth

namespace NewtonBoltzmann

/-- The canonical `s`-particle marginal (Volchan eq. (3.19)) of an `(s+k)`-particle
density: integrate out the last `k` particles, positions over the fundamental domain
`box d` of the torus, velocities over all of `ℝ^d`. -/
noncomputable def marginal {d : ℕ} (s k : ℕ) (P : Config d (s + k) → ℝ)
    (zs : Config d s) : ℝ :=
  ∫ y in region (box d) k, P (Fin.append zs y)

/-- The factorized `s`-particle function `∏ i, f (z i)` attached to a one-particle
profile `f` (Volchan Prop. 3.5 and the hypothesis of Thm. 4.1). -/
noncomputable def factorized {d : ℕ} (s : ℕ) (f : Phase d → ℝ) (zs : Config d s) : ℝ :=
  ∏ i, f (zs i)

/-- The Boltzmann–Grad scaling `N σ^{d-1} = α` (Volchan §3.4, §4.1); for `d = 3`,
`N σ² = α`. -/
def BoltzmannGrad (d : ℕ) (α : ℝ) (N : ℕ) (σ : ℝ) : Prop :=
  (N : ℝ) * σ ^ (d - 1) = α

/-- The Gaussian bound, hypothesis (ii) of Volchan Thm. 4.1:
`sup_{z_s} P₀^{(s)}(z_s) exp (β/2 ∑ i, ‖v i‖²) ≤ c b^s` for every `s`. -/
def GaussianBound {d : ℕ} (β c b : ℝ) (P0 : ∀ s, Config d s → ℝ) : Prop :=
  ∀ (s : ℕ) (zs : Config d s),
    P0 s zs * Real.exp (β / 2 * ∑ i, ‖(zs i).2‖ ^ 2) ≤ c * b ^ s

/-- Free transport of an `s`-particle configuration back by time `t`:
`x i ↦ x i - t • v i`, velocities unchanged (the flow `T⁰`). -/
noncomputable def freeTransport {d : ℕ} (s : ℕ) (t : ℝ) (zs : Config d s) : Config d s :=
  fun i => ((zs i).1 - t • (zs i).2, (zs i).2)

/-- The BBGKY collision operator `Q^σ_{s+1}` (Volchan eqs. (3.33), (4.9)):
`(N-s) σ^{d-1} ∑ i, ∫ dv' ∫_{S^{d-1}} dn, ((v i - v') · n) P(z_s, (x i - σ n, v'))`. -/
noncomputable def bbgkyCollisionOp (d N s : ℕ) (σ : ℝ)
    (P : Config d (s + 1) → ℝ) (zs : Config d s) : ℝ :=
  ((N - s : ℝ) * σ ^ (d - 1)) * ∑ i : Fin s,
    ∫ v' : Vec d, ∫ n in Metric.sphere (0 : Vec d) 1,
      dotp ((zs i).2 - v') n * P (Fin.snoc zs ((zs i).1 - σ • n, v'))
      ∂(μH[(d : ℝ) - 1])

/-- The Boltzmann collision operator `Q_{s+1}` (Volchan eq. (4.3)), the formal
`σ → 0` limit of `Q^σ_{s+1}`: the added particle sits at `x i`. -/
noncomputable def boltzmannCollisionOp (d s : ℕ) (α : ℝ)
    (f : Config d (s + 1) → ℝ) (zs : Config d s) : ℝ :=
  α * ∑ i : Fin s,
    ∫ v' : Vec d, ∫ n in Metric.sphere (0 : Vec d) 1,
      dotp ((zs i).2 - v') n * f (Fin.snoc zs ((zs i).1, v'))
      ∂(μH[(d : ℝ) - 1])

/-- The `n`-th term of the BBGKY series solution (Volchan eq. (4.6)), built by
iterating the Duhamel form along the hard-sphere flow `Φ`. -/
noncomputable def bbgkyTerm {d : ℕ} (sep : Vec d → Vec d → ℝ) (N : ℕ) (σ : ℝ)
    (Φ : ∀ s, HardSphereFlow d s σ sep) (P0 : ∀ k, Config d k → ℝ) :
    ℕ → ℝ → ∀ s, Config d s → ℝ
  | 0, t => fun s zs => P0 s (Function.invFun ((Φ s).H t) zs)
  | n + 1, t => fun s zs =>
      ∫ t1 in (0 : ℝ)..t,
        bbgkyCollisionOp d N s σ (bbgkyTerm sep N σ Φ P0 n t1 (s + 1))
          (Function.invFun ((Φ s).H (t - t1)) zs)

/-- The BBGKY series solution `P^{(s)}(z_s, t) = ∑ n, (n-th term)` (Volchan (4.6)). -/
noncomputable def bbgkySeries {d : ℕ} (sep : Vec d → Vec d → ℝ) (N : ℕ) (σ : ℝ)
    (Φ : ∀ s, HardSphereFlow d s σ sep) (P0 : ∀ k, Config d k → ℝ)
    (t : ℝ) (s : ℕ) (zs : Config d s) : ℝ :=
  ∑' n, bbgkyTerm sep N σ Φ P0 n t s zs

/-- The `n`-th term of the Boltzmann series solution (Volchan eq. (4.7)), along free
transport. -/
noncomputable def boltzmannTerm {d : ℕ} (α : ℝ) (f0 : ∀ k, Config d k → ℝ) :
    ℕ → ℝ → ∀ s, Config d s → ℝ
  | 0, t => fun s zs => f0 s (freeTransport s t zs)
  | n + 1, t => fun s zs =>
      ∫ t1 in (0 : ℝ)..t,
        boltzmannCollisionOp d s α (boltzmannTerm α f0 n t1 (s + 1))
          (freeTransport s (t - t1) zs)

/-- The Boltzmann series solution `f^{(s)}(z_s, t) = ∑ n, (n-th term)` (Volchan (4.7)). -/
noncomputable def boltzmannSeries {d : ℕ} (α : ℝ) (f0 : ∀ k, Config d k → ℝ)
    (t : ℝ) (s : ℕ) (zs : Config d s) : ℝ :=
  ∑' n, boltzmannTerm α f0 n t s zs

end NewtonBoltzmann


