-- Prove2me | Definitions.Def_ModularCurve_AbelFibreSum
-- name    : ModularCurve_AbelFibreSum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/7cf71f58-350d-53fa-a71a-ac4730b53b6c
-- title:
--   Fibre multiplicities, orbifold indices and Abel fibre sums
-- statement:
--   Three definitions are made for a level $N$, a function $F:\mathbb H\to\mathbb C$ and a value $t\in\mathbb C$, all relative to $\Gamma_0(N)$ acting on the upper half plane.
--
--   First, `valueMultiplicity F t τ` is a natural number attached to a point $\tau\in\mathbb H$: it is the meromorphic order at $\tau$, in the sense of Mathlib's `meromorphicOrderAt`, of the function of a complex variable $z\mapsto F(\mathrm{ofComplex}\,z)-t$, with the resulting element of `WithTop ℤ` pushed into $\mathbb N$ (the top value, i.e. local vanishing of $F-t$ or failure of meromorphy in the relevant sense, and all negative orders both yield $0$). Thus at a point where $F$ is holomorphic and takes the value $t$ to order $n$ the number is $n$, and it is $0$ wherever $F(\tau)\ne t$ or a pole occurs. Two lemmas record the two cases: the value is $0$ when the order is $\top$, and is $n$ when the order is the integer $n\ge 0$.
--
--   Second, `orbifoldIndex N τ` is the cardinality of the stabiliser of $\tau$ in $\Gamma_0(N)$ divided by $2$ (natural-number division), i.e. the ramification index of $\mathbb H\to\Gamma_0(N)\backslash\mathbb H$ at $\tau$, the factor $2$ accounting for $\pm 1$.
--
--   Third, `abelFibreSum N F t` is an element of the dual space $\mathrm{Hom}_{\mathbb C}(S_2(\Gamma_0(N)),\mathbb C)$, where $S_2(\Gamma_0(N))$ is `CuspForm (CongruenceSubgroup.Gamma0 N) 2`: it is the `finsum` over the orbit space $\Gamma_0(N)\backslash\mathbb H$ of the scalar $\mathrm{valueMultiplicity}\,F\,t\,\xi_{\mathrm{out}}$ divided by $\mathrm{orbifoldIndex}\,N\,\xi_{\mathrm{out}}$, times the period functional `periodAlong N UpperHalfPlane.I ξ.out`, the latter being $f\mapsto\int_0^1 f(\gamma(s))(\xi_{\mathrm{out}}-i)\,ds$ along the straight segment from $i$ to the chosen orbit representative $\xi_{\mathrm{out}}$. By the convention for `finsum`, the value is the finite sum when only finitely many orbits contribute a nonzero term and $0$ otherwise. Unfolding lemmas for the three definitions are also recorded.
--
--   **Relation to Mathlib.** The multiplicity is built from Mathlib's `meromorphicOrderAt` and the orbifold index from Mathlib's `MulAction.stabilizer` for `CongruenceSubgroup.Gamma0`; the combination into a functional on weight-two cusp forms, like the period functional `periodAlong` it uses, is the project's own.
--
--   **Where it is used.** These quantities express, as a functional on weight-two cusp forms for $\Gamma_0(N)$, the Abel–Jacobi image with base point $i$ of the fibre divisor of $F$ over $t$ on the modular curve $X_0(N)$, the multiplicities being the ones computed on the quotient. They feed into the treatment of the period lattice of $X_0(N)$ and of its Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AbelFibreSum.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

noncomputable def valueMultiplicity (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) : ℕ :=
  (meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)).untop₀.toNat

noncomputable def orbifoldIndex (N : ℕ) (τ : ℍ) : ℕ :=
  Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2

noncomputable def abelFibreSum (N : ℕ) (F : ℍ → ℂ) (t : ℂ) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  ∑ᶠ ξ : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ),
    ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndex N ξ.out : ℂ)) •
      periodAlong N UpperHalfPlane.I ξ.out

theorem valueMultiplicity_def (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) :
    valueMultiplicity F t τ =
      (meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)).untop₀.toNat :=
  rfl

theorem orbifoldIndex_def (N : ℕ) (τ : ℍ) :
    orbifoldIndex N τ = Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 :=
  rfl

theorem abelFibreSum_def (N : ℕ) (F : ℍ → ℂ) (t : ℂ) :
    abelFibreSum N F t =
      ∑ᶠ ξ : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ),
        ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndex N ξ.out : ℂ)) •
          periodAlong N UpperHalfPlane.I ξ.out :=
  rfl

theorem valueMultiplicity_of_eq_top {F : ℍ → ℂ} {t : ℂ} {τ : ℍ}
    (h : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤) :
    valueMultiplicity F t τ = 0 := by
  simp [valueMultiplicity, h]

theorem valueMultiplicity_of_eq_coe {F : ℍ → ℂ} {t : ℂ} {τ : ℍ} {n : ℕ}
    (h : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ((n : ℤ) : WithTop ℤ)) :
    valueMultiplicity F t τ = n := by
  simp [valueMultiplicity, h]

end ModularCurve


