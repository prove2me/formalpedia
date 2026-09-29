-- Prove2me | Definitions.Def_DFT_HohenbergKohn
-- name    : DFT_HohenbergKohn
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T19:54:09.535362+00:00
-- url     : https://prove2.me/theorems/12580853-befa-4f3c-89a8-74723eb4ba6d
-- title:
--   Hohenberg-Kohn variational model and one-particle density
-- statement:
--   This file fixes the objects the Hohenberg-Kohn theorems are stated about.
--
--   A *Hohenberg-Kohn model* consists of three sets and three maps: a set of admissible
--   (normalized) many-electron wavefunctions, a set of external potentials, a set of
--   one-particle densities, a universal functional $F(\Psi)$ giving the expectation value of the
--   kinetic and electron-electron interaction operators in the state $\Psi$, a density map
--   $\Psi \mapsto \rho_\Psi$, and an external-energy pairing $\operatorname{ext}(v,\rho)$
--   representing $\int v\rho$. Nothing else is assumed: in particular the model records exactly
--   the two structural facts the Hohenberg-Kohn argument uses, namely that $F$ does not depend
--   on the external potential and that the external energy depends on the state only through its
--   density.
--
--   On top of these data the file defines:
--
--   1. the total energy $E_v(\Psi) = F(\Psi) + \operatorname{ext}(v, \rho_\Psi)$;
--   2. *ground state*: $\Psi$ with $E_v(\Psi) \le E_v(\Phi)$ for all admissible $\Phi$;
--   3. *nondegenerate ground state*: $\Psi$ with $E_v(\Psi) < E_v(\Phi)$ for all $\Phi \ne \Psi$;
--   4. *$v$-representable density*: a density that is $\rho_\Psi$ for some nondegenerate ground
--      state $\Psi$ of some potential;
--   5. the *Hohenberg-Kohn functional* $F[\rho]$, defined on $v$-representable densities as
--      $F(\Psi)$ for a nondegenerate ground state $\Psi$ with $\rho_\Psi=\rho$;
--   6. the *Levy constrained-search functional*
--      $F_{\mathrm{LL}}[\rho] = \inf\{F(\Psi) : \rho_\Psi = \rho\}$.
--
--   Separately, for the concrete setting of $N = n+1$ electrons in $\mathbb R^3$, the file
--   defines the one-particle density of a wavefunction $\Psi$ on $(\mathbb R^3)^{N}$:
--
--   $$\rho_\Psi(r) \;=\; \sum_{i=1}^{N} \int_{(\mathbb R^3)^{N-1}}
--       \bigl|\Psi(y_1,\dots,y_{i-1},r,y_{i},\dots,y_{N-1})\bigr|^2 \, dy .$$
--
--   **Formalization Note.** The universal functional is only determined on $v$-representable
--   densities; off that set it is given the value $0$. The constrained-search functional is an
--   infimum, so it takes the value $0$ on a density that is the density of no admissible
--   wavefunction. Integrals of non-integrable functions are $0$ by convention, so the one-particle
--   density is a total function.
-- source:
--   Wikipedia, 'Density functional theory' (uploaded PDF), sections 'Derivation and formalism', 'Hohenberg-Kohn theorems' (Theorem 1, Corollary 1, Theorem 2) and 'Kohn-Sham equations'; https://en.wikipedia.org/wiki/Density_functional_theory . Primary sources cited there: P. Hohenberg and W. Kohn, 'Inhomogeneous electron gas', Phys. Rev. 136 (1964) B864, https://doi.org/10.1103/PhysRev.136.B864 ; W. Kohn and L. J. Sham, Phys. Rev. 140 (1965) A1133, https://doi.org/10.1103/PhysRev.140.A1133 ; M. Levy, Proc. Natl. Acad. Sci. USA 76 (1979) 6062, https://doi.org/10.1073/pnas.76.12.6062 .

import Mathlib

noncomputable section

namespace DFT

open MeasureTheory

universe u

/-- An abstract Hohenberg–Kohn model.

`Wf` is the set of admissible (normalized) many-electron wavefunctions, `Pot` the set of
external potentials, `Dens` the set of one-particle electron densities.  `F Ψ` is the
expectation value of the universal operators (kinetic energy plus electron–electron
interaction) in the state `Ψ`, `dens Ψ` is the one-particle density of `Ψ`, and `ext v n`
is the external-potential energy `∫ v n`, which depends on the state only through its
density. -/
structure HKModel where
  /-- admissible (normalized) many-electron wavefunctions -/
  Wf : Type u
  /-- external potentials -/
  Pot : Type u
  /-- one-particle electron densities -/
  Dens : Type u
  /-- expectation value of the universal (kinetic + interaction) operators -/
  F : Wf → ℝ
  /-- one-particle density of a wavefunction -/
  dens : Wf → Dens
  /-- external-potential energy `∫ v n` -/
  ext : Pot → Dens → ℝ

namespace HKModel

variable (M : HKModel)

/-- Total energy of the state `Ψ` in the external potential `v`. -/
def energy (v : M.Pot) (Ψ : M.Wf) : ℝ := M.F Ψ + M.ext v (M.dens Ψ)

/-- `Ψ` is a ground state for the external potential `v`: it minimizes the energy. -/
def IsGroundState (v : M.Pot) (Ψ : M.Wf) : Prop := ∀ Φ : M.Wf, M.energy v Ψ ≤ M.energy v Φ

/-- `Ψ` is a nondegenerate ground state for `v`: it is the strict minimizer of the energy. -/
def IsNondegenerateGroundState (v : M.Pot) (Ψ : M.Wf) : Prop :=
  ∀ Φ : M.Wf, Φ ≠ Ψ → M.energy v Ψ < M.energy v Φ

/-- A density is `v`-representable if it is the density of a nondegenerate ground state of
some external potential. -/
def VRepresentable (n : M.Dens) : Prop :=
  ∃ Ψ : M.Wf, (∃ v : M.Pot, M.IsNondegenerateGroundState v Ψ) ∧ M.dens Ψ = n

open Classical in
/-- The Hohenberg–Kohn universal functional `F[n]`: on a `v`-representable density it is the
universal energy of a nondegenerate ground state with that density, and `0` elsewhere. -/
def hkFunctional (n : M.Dens) : ℝ := if h : M.VRepresentable n then M.F h.choose else 0

/-- The Levy constrained-search functional: the infimum of the universal energy over all
wavefunctions whose density is `n`. -/
def levyFunctional (n : M.Dens) : ℝ := sInf (M.F '' {Ψ : M.Wf | M.dens Ψ = n})

end HKModel

/-- Position space of a single electron. -/
abbrev Pos : Type := EuclideanSpace ℝ (Fin 3)

/-- Configuration space of `n + 1` electrons. -/
abbrev Config (n : ℕ) : Type := Fin (n + 1) → Pos

/-- The one-particle density of an `(n+1)`-electron wavefunction `Ψ`:
`ρ(r) = ∑ᵢ ∫ |Ψ(x₁,…,r,…,x_{n+1})|² d(x_j)_{j≠i}`, where in the `i`-th summand the `i`-th
argument is set to `r` and the remaining `n` arguments are integrated out. -/
def oneParticleDensity {n : ℕ} (Ψ : Config n → ℂ) (r : Pos) : ℝ :=
  ∑ i : Fin (n + 1), ∫ y : Fin n → Pos, ‖Ψ (i.insertNth r y)‖ ^ 2

end DFT

end


