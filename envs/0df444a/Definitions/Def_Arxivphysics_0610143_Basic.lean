-- Prove2me | Definitions.Def_Arxivphysics_0610143_Basic
-- name    : Arxivphysics_0610143_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T19:38:36.098523+00:00
-- url     : https://prove2.me/theorems/fbe97c52-290e-5c6b-acff-15d78411007c
-- title:
--   Reciprocal periodic slab media, TM/TE scalar reductions, weak quasi-periodic solutions with Rayleigh expansions (Eq. (4)) for incidence from above and below, and the amplitude ratio of Eq. (9)
-- statement:
--   Objects of M. Iwanaga, A. S. Vengurlekar, T. Hatano and T. Ishihara, *Reciprocal transmittances and reflectances: An elementary proof* (arXiv:physics/0610143v4), Sections II–III, in the plane-wave limit of the paper's far-field dipole arrays. Points of the plane of incidence are $(x,z)\in\mathbb R^2$; the structure is uniform along $y$.
--
--   1. **Harmonics (Eq. (4)).** For period $d$, wavenumber $k$ and incident tangential wavenumber $\alpha$: $k_{x,m}=\alpha+2\pi m/d$ ($m\in\mathbb Z$), and $\beta(a)=\sqrt{k^2-a^2}$ if $a^2\le k^2$, $\beta(a)=i\sqrt{a^2-k^2}$ otherwise; $\beta_m=\beta(k_{x,m})$. The up-going harmonic is $e^{i(k_{x,m}x+\beta_mz)}$ and the down-going one $e^{i(k_{x,m}x-\beta_mz)}$; closed channels decay away from the object.
--   2. **Media (Sec. II, Figs. 3–4).** Relative permittivity and permeability tensor fields $\varepsilon,\mu:\mathbb R^2\to\mathbb C^{3\times3}$ (indices $x,y,z$), each satisfying:
--      - entries, and entries of the inverse of the $xz$ block, are measurable and bounded; the $xz$ block is invertible;
--      - symmetric, $M_{ij}=M_{ji}$, with $M_{xy}=M_{zy}=0$ ($y$ decoupled from the $xz$ plane);
--      - periodic: $M(x+d,z)=M(x,z)$;
--      - vacuum outside the slab: $M=1$ for $|z|>h$.
--
--      Complex entries (absorption) are allowed; the unit cell is otherwise arbitrary. The configuration without object is $\varepsilon=\mu=1$ everywhere.
--   3. **Scalar equations.** With $J(a,b)=(-b,a)$ and $M_{xz}$ the $xz$ block of $M$:
--      - TM polarization ($\mathbf E$ in the $xz$ plane), field $u=H_y$: $\nabla\cdot(A\nabla u)+k^2\mu_{yy}u=0$ with $A=J^{\mathsf T}\varepsilon_{xz}^{-1}J$;
--      - TE polarization ($\mathbf E\parallel y$), field $u=E_y$: the same with $A=J^{\mathsf T}\mu_{xz}^{-1}J$ and $\mu_{yy}$ replaced by $\varepsilon_{yy}$.
--   4. **Weak solution.** $u$ and a weak gradient $g$ are in $L^2$ on every ball, and $\int (Ag)\cdot\nabla\varphi-k^2 s\,u\,\varphi=0$ for every real-valued smooth compactly supported $\varphi$ (by complex linearity, equivalently for complex $\varphi$); the weak gradient satisfies $\int u\,\partial_i\varphi=-\int g_i\varphi$ for the same $\varphi$.
--   5. **Quasi-periodicity.** $u(x+d,z)=e^{i\alpha d}u(x,z)$.
--   6. **Incidence from above** (coefficients $A,s$, tangential wavenumber $\alpha$, amplitudes $r_m,t_m$): $u$ is a quasi-periodic weak solution with
--      - $u=e^{i(\alpha x-\beta_0z)}+\sum_m r_m e^{i(k_{x,m}x+\beta_mz)}$ for $z>h$;
--      - $u=\sum_m t_m e^{i(k_{x,m}x-\beta_mz)}$ for $z<-h$;
--
--      the series converging (unconditionally) at every point.
--   7. **Incidence from below**: the same with up and down exchanged: $u=e^{i(\alpha x+\beta_0z)}+\sum_m r_me^{i(k_{x,m}x-\beta_mz)}$ for $z<-h$ and $u=\sum_m t_me^{i(k_{x,m}x+\beta_mz)}$ for $z>h$.
--   8. **Eq. (9).** $\mathrm{ratio}(a,b)=|a/b|^2$, so that $T_i=|E_i^{(0)}/E_i^{\rm no,(0)}|^2$ is the ratio of zeroth-order amplitudes with and without object.
--
--   **Formalization Note** The paper's sources are finite arrays of point dipoles whose far fields are 'to a good approximation' plane waves. The formalization works in the exact plane-wave limit that this approximation targets, which is also the setting of the paper's numerics (Sec. IV). The paper writes the fields in terms of $\mathbf E$. In vacuum the zeroth-order $\mathbf E$ and $\mathbf H$ amplitudes are proportional with the same factor with and without object, so the ratios of Eq. (9) agree for $H_y$ and $\mathbf E$. Symmetry of $\varepsilon,\mu$ is not stated in the paper but is the hypothesis of the reciprocal theorem it cites (Landau–Lifshitz). Writing the radiated harmonics as $e^{+i\beta_m|z|}$ corresponds to the time factor $e^{-i\omega t}$. Since $\varepsilon,\mu$ range over all complex values, the statements cover either sign convention for absorption.
-- source:
--   M. Iwanaga, A. S. Vengurlekar, T. Hatano, T. Ishihara, Reciprocal transmittances and reflectances: An elementary proof, arXiv:physics/0610143v4, Sec. II (linear local media, Eq. (1)); Sec. III, Eq. (4), Eqs. (8)-(9), Figs. 1, 3, 4, PDF pp. 1-3

import Mathlib

/-!
M. Iwanaga, A. S. Vengurlekar, T. Hatano and T. Ishihara, *Reciprocal transmittances and reflectances: An elementary proof* (arXiv:physics/0610143v4),
Sections II–III: the reciprocal configurations of Fig. 1 for a one-dimensionally periodic object
(period `d` along `x`, finite thickness along `z`) in vacuum, illuminated by a plane wave of
wavenumber `k` in the `xz` plane, in the plane-wave limit of the paper's far-field dipole arrays.

Points of the plane of incidence are `(x, z) : ℝ × ℝ`. The structure is uniform along `y`.
The media are linear and local, `D_i = ∑_j ε_ij E_j`, `B_i = ∑_j μ_ij H_j` (Sec. II), with
relative tensors `ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ`, indices `0, 1, 2 = x, y, z`. They are
taken symmetric (the hypothesis of the reciprocal theorem in Landau–Lifshitz, Ref. 4) and with
`y` decoupled from the `xz` plane, so that TM (`E` in the `xz` plane) and TE (`E ∥ y`) fields
separate (Sec. III, polarization paragraph).

For TM polarization the field `u = H_y` satisfies `∇·(A∇u) + k² μ_yy u = 0` with
`A = Jᵀ ε_xz⁻¹ J`, where `ε_xz` is the `xz` block of `ε` and `J(a, b) = (-b, a)`
(from `curl H = iωε₀εE`, `curl E = -iωμ₀μH`); for TE polarization `u = E_y` satisfies the same
equation with `A = Jᵀ μ_xz⁻¹ J` and `μ_yy` replaced by `ε_yy`. In vacuum `A = 1` and the
equation is `Δu + k²u = 0`. The equation is taken in the weak sense, with `u ∈ H¹_loc`.

Outside the slab `|z| ≤ h` the field is the Rayleigh (Fourier-harmonic) expansion of Eq. (4),
`k_{x,m} = α + 2πm/d`, `k_{z,m} = ±β_m`, `β_m = √(k² − k_{x,m}²)` (with `β_m = i√(k_{x,m}² − k²)`
for closed channels, so that these harmonics decay away from the object).
-/

open MeasureTheory Matrix

noncomputable section

namespace Arxivphysics_0610143

/-- The coordinate directions `e_x = (1, 0)` and `e_z = (0, 1)` of the plane of incidence. -/
def coordDir : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- Eq. (4), PDF p. 2: `k_{x,m} = α + 2πm/d` for the incident tangential wavenumber `α`. -/
def kxm (d α : ℝ) (m : ℤ) : ℝ := α + 2 * Real.pi * m / d

/-- Eq. (4), PDF p. 2: `β = √(k² − a²)` if `a² ≤ k²` (open channel) and `β = i√(a² − k²)`
otherwise (closed channel), so that `k_z = ±β`. -/
def kzOf (k a : ℝ) : ℂ :=
  if a ^ 2 ≤ k ^ 2 then (Real.sqrt (k ^ 2 - a ^ 2) : ℂ)
  else Complex.I * (Real.sqrt (a ^ 2 - k ^ 2) : ℂ)

/-- Eq. (4): the harmonic `exp(i(k_{x,m} x + β_m z))`, travelling (or decaying) towards `+z`. -/
def upMode (d k α : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * ((kxm d α m : ℂ) * p.1 + kzOf k (kxm d α m) * p.2))

/-- Eq. (4): the harmonic `exp(i(k_{x,m} x − β_m z))`, travelling (or decaying) towards `−z`. -/
def downMode (d k α : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * ((kxm d α m : ℂ) * p.1 - kzOf k (kxm d α m) * p.2))

/-- The `xz` block `[[M_xx, M_xz], [M_zx, M_zz]]` of a `3 × 3` tensor (indices `0, 1, 2 = x, y, z`). -/
def xzBlock (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 0 0, M 0 2; M 2 0, M 2 2]

/-- The rotation `J(a, b) = (-b, a)`, which maps `∇u = (∂ₓu, ∂_z u)` to the `xz` part of
`curl (u e_y) = (-∂_z u, ∂ₓu)`. -/
def rotJ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The coefficient `Jᵀ M⁻¹ J` of the scalar equation `∇·(A∇u) + k² s u = 0` obtained from
Maxwell's equations for a field `u e_y` when the other field lies in the `xz` plane and the
corresponding material tensor has `xz` block `M`. -/
def inPlaneCoeff (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotJᵀ * M⁻¹ * rotJ

/-- TM polarization (Fig. 3, `E` in the `xz` plane), field `u = H_y`: coefficient
`A = Jᵀ ε_xz⁻¹ J`. -/
def tmCoeff (ε : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  inPlaneCoeff (xzBlock (ε p))

/-- TM polarization, field `u = H_y`: zeroth-order coefficient `μ_yy`. -/
def tmPot (μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (p : ℝ × ℝ) : ℂ := μ p 1 1

/-- TE polarization (`E ∥ y`), field `u = E_y`: coefficient `A = Jᵀ μ_xz⁻¹ J`. -/
def teCoeff (μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  inPlaneCoeff (xzBlock (μ p))

/-- TE polarization, field `u = E_y`: zeroth-order coefficient `ε_yy`. -/
def tePot (ε : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) (p : ℝ × ℝ) : ℂ := ε p 1 1

/-- Sec. II and Figs. 3–4: `M` is the relative tensor field (permittivity or permeability) of a
linear, local, reciprocal medium containing a one-dimensionally periodic object of period `d`
along `x` inside the slab `|z| ≤ h`, with vacuum outside:
* the entries of `M` and of the inverse of its `xz` block are measurable and bounded, the `xz`
  block is invertible;
* `M` is symmetric, `M_ij = M_ji` (reciprocal medium) and `y` is decoupled:
  `M_xy = M_zy = 0`;
* `M(x + d, z) = M(x, z)`;
* `M = 1` for `|z| > h`.
Absorption (complex entries) is allowed, and the unit cell is arbitrary. -/
def IsPeriodicSlabTensor (d h : ℝ) (M : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  (∀ i j, Measurable fun p => M p i j) ∧
  (∀ i j, Measurable fun p => (xzBlock (M p))⁻¹ i j) ∧
  (∃ C : ℝ, ∀ p, (∀ i j, ‖M p i j‖ ≤ C) ∧ ∀ i j, ‖(xzBlock (M p))⁻¹ i j‖ ≤ C) ∧
  (∀ p, IsUnit (xzBlock (M p)).det) ∧
  (∀ p, (M p)ᵀ = M p) ∧
  (∀ p, M p 0 1 = 0 ∧ M p 2 1 = 0) ∧
  (∀ x z : ℝ, M (x + d, z) = M (x, z)) ∧
  (∀ x z : ℝ, h < |z| → M (x, z) = 1)

/-- The medium of Figs. 3–4: permittivity `ε` and permeability `μ` both of the form
`IsPeriodicSlabTensor d h`. -/
def IsReciprocalGratingMedium (d h : ℝ) (ε μ : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  IsPeriodicSlabTensor d h ε ∧ IsPeriodicSlabTensor d h μ

/-- The configuration without object (Eq. (8)): vacuum everywhere, `ε = μ = 1`. -/
def vacuumTensor : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℂ := fun _ => 1

/-- `u ∈ H¹_loc(ℝ²)` is a weak solution of `∇·(A∇u) + k² s u = 0`: `u` and a weak gradient
`g = (∂ₓu, ∂_z u)` are locally square integrable, and for every smooth compactly supported test
function `φ`, `∫ (A g)·∇φ − k² s u φ = 0`. -/
def IsWeakSolution (A : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ × ℝ → ℂ) (k : ℝ)
    (u : ℝ × ℝ → ℂ) : Prop :=
  (∀ R : ℝ, MemLp u 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) R))) ∧
  ∃ g : ℝ × ℝ → Fin 2 → ℂ,
    (∀ (i : Fin 2) (R : ℝ),
      MemLp (fun p => g p i) 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) R))) ∧
    (∀ (i : Fin 2) (φ : ℝ × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ p, u p * ((fderiv ℝ φ p (coordDir i) : ℝ) : ℂ) = -∫ p, g p i * ((φ p : ℝ) : ℂ)) ∧
    (∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ p, ((∑ i : Fin 2, ∑ j : Fin 2,
          A p i j * g p j * ((fderiv ℝ φ p (coordDir i) : ℝ) : ℂ)) -
        (k : ℂ) ^ 2 * s p * u p * ((φ p : ℝ) : ℂ)) = 0)

/-- `u` is quasi-periodic with tangential wavenumber `α`: `u(x + d, z) = e^{iαd} u(x, z)`. -/
def IsQuasiPeriodic (d α : ℝ) (u : ℝ × ℝ → ℂ) : Prop :=
  ∀ x z : ℝ, u (x + d, z) = Complex.exp (Complex.I * α * d) * u (x, z)

/-- Fig. 1(a), Figs. 3–4, Eq. (4): `u` is a field of the grating problem with coefficients `A`, `s`
for the unit plane wave `exp(i(αx − β₀z))` incident from above (`z > h`): `u` is a weak
solution, `α`-quasi-periodic, and
* `u = exp(i(αx − β₀z)) + ∑_m r_m exp(i(k_{x,m}x + β_m z))` for `z > h`;
* `u = ∑_m t_m exp(i(k_{x,m}x − β_m z))` for `z < −h`.
`r m`, `t m` are the reflected and transmitted Fourier amplitudes of order `m`. -/
def IsDownScattering (d k h α : ℝ) (A : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℂ) (r t : ℤ → ℂ) : Prop :=
  IsWeakSolution A s k u ∧ IsQuasiPeriodic d α u ∧
  (∀ x z : ℝ, h < z →
    HasSum (fun m : ℤ => r m * upMode d k α m (x, z)) (u (x, z) - downMode d k α 0 (x, z))) ∧
  (∀ x z : ℝ, z < -h → HasSum (fun m : ℤ => t m * downMode d k α m (x, z)) (u (x, z)))

/-- Fig. 1(b), Fig. 3, Eq. (4): `u` is a field of the grating problem with coefficients `A`, `s`
for the unit plane wave `exp(i(αx + β₀z))` incident from below (`z < −h`): `u` is a weak
solution, `α`-quasi-periodic, and
* `u = exp(i(αx + β₀z)) + ∑_m r_m exp(i(k_{x,m}x − β_m z))` for `z < −h`;
* `u = ∑_m t_m exp(i(k_{x,m}x + β_m z))` for `z > h`. -/
def IsUpScattering (d k h α : ℝ) (A : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℂ) (r t : ℤ → ℂ) : Prop :=
  IsWeakSolution A s k u ∧ IsQuasiPeriodic d α u ∧
  (∀ x z : ℝ, z < -h →
    HasSum (fun m : ℤ => r m * downMode d k α m (x, z)) (u (x, z) - upMode d k α 0 (x, z))) ∧
  (∀ x z : ℝ, h < z → HasSum (fun m : ℤ => t m * upMode d k α m (x, z)) (u (x, z)))

/-- Eq. (9), PDF p. 2: `|a / b|²`, the transmittance `T = |E^{(0)} / E^{no,(0)}|²` (and the
reflectance) as the squared modulus of a zeroth-order amplitude relative to its value without
object. -/
def ampRatioSq (a b : ℂ) : ℝ := Complex.normSq (a / b)

end Arxivphysics_0610143


