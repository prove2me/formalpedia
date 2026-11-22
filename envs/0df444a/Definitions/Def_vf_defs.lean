-- Prove2me | Definitions.Def_vf_defs
-- name    : vf_defs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T19:50:11.232461+00:00
-- url     : https://prove2.me/theorems/60e39f8f-cc0c-47c0-a165-84ea41efe6b1
-- title:
--   Vaidya-Farina 1991: fields, boosts and Maxwell systems
-- statement:
--   Foundational definitions for the Vaidya–Farina (1991) analysis of Galilean covariance of Maxwell's equations. Spacetime is $\mathrm{ST}=\mathbb R^3\times\mathbb R$; fields are maps $\mathrm{ST}\to\mathbb R^3$. Partial derivatives are taken along coordinate lines, and $\varepsilon_{ijk}$ is the Levi-Civita symbol, giving divergence, curl and time-derivative operators. In Gaussian units with $c=1$, `FullMaxwell` is the system $\nabla\cdot H=0,\ \partial_tH=-\nabla\times E,\ \nabla\cdot E=4\pi\rho,\ \nabla\times H-\partial_tE=4\pi j$; `rhoOf` and `jOf` read the last two equations as definitions of the sources. `boostE`/`boostH` implement the Galilean boost laws $E'=E+v\times H,\ H'=H$ together with the coordinate change $x'=x-vt$. `jMod` and `MagneticSystem` drop the displacement current (eq. (17)); `ElectricSystem`, `boostEelec`, `boostBelec` encode the electric Galilean limit with constants $\varepsilon_0,\mu_0$ (eqs. (20)–(22)). The algebraic layer (`magH`, `crossA`, `elecOf`) expresses the Feynman–Dyson definitions $H_i=-\frac{im^2}{2\hbar}\varepsilon_{ijk}[\dot x_j,\dot x_k]$ and $F_i=E_i+\varepsilon_{ijk}\dot x_jH_k$ over a complex algebra.
-- source:
--   A. Vaidya and C. Farina, Can Galilean mechanics and full Maxwell equations coexist peacefully?, Phys. Lett. A 153 (1991) 265-267, https://doi.org/10.1016/0375-9601(91)90940-A, eqs. (3),(4),(5),(6),(13),(14),(17),(20),(22)

import Mathlib

namespace VaidyaFarina

abbrev Space := Fin 3 → ℝ
abbrev ST := Space × ℝ

noncomputable def eps (i j k : Fin 3) : ℝ :=
  if i = j ∨ j = k ∨ k = i then 0
  else if ((i : ℕ) + 1) % 3 = (j : ℕ) ∧ ((j : ℕ) + 1) % 3 = (k : ℕ) then 1 else -1

noncomputable def dX (f : ST → ℝ) (i : Fin 3) (p : ST) : ℝ :=
  deriv (fun s : ℝ => f (Function.update p.1 i s, p.2)) (p.1 i)

noncomputable def dT (f : ST → ℝ) (p : ST) : ℝ :=
  deriv (fun s : ℝ => f (p.1, s)) (p.2)

noncomputable def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3, eps i j k * a j * b k

noncomputable def vdiv (F : ST → (Fin 3 → ℝ)) (p : ST) : ℝ :=
  ∑ i : Fin 3, dX (fun q => F q i) i p

noncomputable def curl (F : ST → (Fin 3 → ℝ)) (p : ST) : Fin 3 → ℝ :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3, eps i j k * dX (fun q => F q k) j p

noncomputable def vdt (F : ST → (Fin 3 → ℝ)) (p : ST) : Fin 3 → ℝ :=
  fun i => dT (fun q => F q i) p

noncomputable def rhoOf (E : ST → (Fin 3 → ℝ)) : ST → ℝ :=
  fun p => vdiv E p / (4 * Real.pi)

noncomputable def jOf (E H : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => (4 * Real.pi)⁻¹ • (curl H p - vdt E p)

noncomputable def jMod (H : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => (4 * Real.pi)⁻¹ • curl H p

noncomputable def boostH (v : Fin 3 → ℝ) (H : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => H (p.1 + p.2 • v, p.2)

noncomputable def boostE (v : Fin 3 → ℝ) (E H : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => E (p.1 + p.2 • v, p.2) + cross v (H (p.1 + p.2 • v, p.2))

noncomputable def boostEelec (v : Fin 3 → ℝ) (E : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => E (p.1 + p.2 • v, p.2)

noncomputable def boostBelec (e0 mu0 : ℝ) (v : Fin 3 → ℝ) (E B : ST → (Fin 3 → ℝ)) : ST → (Fin 3 → ℝ) :=
  fun p => B (p.1 + p.2 • v, p.2) - (e0 * mu0) • cross v (E (p.1 + p.2 • v, p.2))

def FullMaxwell (E H : ST → (Fin 3 → ℝ)) (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) : Prop :=
  (∀ p, vdiv H p = 0) ∧
  (∀ p, vdt H p = -curl E p) ∧
  (∀ p, vdiv E p = 4 * Real.pi * rho p) ∧
  (∀ p, curl H p - vdt E p = (4 * Real.pi) • j p)

def MagneticSystem (E H : ST → (Fin 3 → ℝ)) (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) : Prop :=
  (∀ p, vdiv H p = 0) ∧
  (∀ p, vdt H p = -curl E p) ∧
  (∀ p, vdiv E p = 4 * Real.pi * rho p) ∧
  (∀ p, curl H p = (4 * Real.pi) • j p)

def ElectricSystem (e0 mu0 : ℝ) (E B : ST → (Fin 3 → ℝ)) (rho : ST → ℝ) (j : ST → (Fin 3 → ℝ)) : Prop :=
  (∀ p, vdiv E p = rho p / e0) ∧
  (∀ p, curl E p = 0) ∧
  (∀ p, vdiv B p = 0) ∧
  (∀ p, curl B p = mu0 • j p + (e0 * mu0) • vdt E p)

variable {A : Type*} [Ring A] [Algebra ℂ A]

noncomputable def crossA (a b : Fin 3 → A) : Fin 3 → A :=
  fun i => ∑ j : Fin 3, ∑ k : Fin 3, Complex.ofReal (eps i j k) • (a j * b k)

noncomputable def magH (m hbar : ℂ) (vel : Fin 3 → A) : Fin 3 → A :=
  fun i => (-(Complex.I * m ^ 2 / (2 * hbar))) •
    ∑ j : Fin 3, ∑ k : Fin 3, Complex.ofReal (eps i j k) • (vel j * vel k - vel k * vel j)

noncomputable def elecOf (F vel H : Fin 3 → A) : Fin 3 → A :=
  fun i => F i - crossA vel H i

end VaidyaFarina


