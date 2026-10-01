-- Prove2me | Definitions.Def_ChapterSmHamiltonian
-- name    : ChapterSmHamiltonian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:08:17.165001+00:00
-- url     : https://prove2.me/theorems/9011c20d-fdb9-4b46-8d21-fd7565446ea9
-- title:
--   Chapter SmHamiltonian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmHamiltonian.lean`): generated def bundle for ChapterSmHamiltonian. See BookProof/ChapterSmHamiltonian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmHamiltonian.lean

import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockEsa
import Mathlib


/-!
# The Standard Model one-particle Hamiltonian in temporal gauge

Step 1 of the Standard-Model work order of `CONSOLIDATED_PLAN.md`
(§“State of the project — 2026-09-22d”, D6b-SM.1 / D6b-SM.4): the **bosonic** one-particle
operator `h` of the record, written on the Gauss–polynomial core of `L²(ℝ¹⁶³)` by genuine
multiplication and differentiation operators, in the temporal (Weyl) gauge
`A₀ = W₀ = B₀ = 0`.

## The operator

`h = h_Gauge + h_Higgs` with, in the notation of D6b-SM.1,

```
h_Gauge = ½(π^G π^G + B^G B^G) + ½(π^W π^W + B^W B^W) + ½(π^B π^B + B^B B^B)
h_Higgs = ½ π^φ_a π^φ_a + ½ (D_i φ)_a (D_i φ)_a + V(φ)
```

* `smMagG` — `B^G_{a,i} = ½ ε_{ijk}(G^a_{k,j} − G^a_{j,k} + g_s f^{abc} G^b_j G^c_k)`, at
  **arbitrary real structure constants**, so the genuinely non-abelian (quartic) case is
  the one proved;
* `smMagW` — the same for the weak field with the `SU(2)` structure constants;
* `smMagB` — the abelian hypercharge field strength `½ ε_{ijk}(B_{k,j} − B_{j,k})`;
* `smCovD` — the covariant Higgs derivative
  `(D_i φ)_a = φ_{a,i} + g W^j_i (τ_j/2 φ)_a + g' B_i (σ₃/2 φ)_a`, with the action of the
  electroweak generators on the four real components of the doublet carried by the real
  matrices `tgen`, `ygen` of `SmParams` (any real generators are allowed: the operator
  theory below does not use their Lie algebra);
* `smWall` — the Higgs potential in its **square** form `√(λ/2)(‖φ‖² − v²)`, whose square
  contributes `V(φ) + μ⁴/(4λ) = (λ/4)(‖φ‖² − v²)²` with `v² = μ²/λ`.  The two conventions
  differ by the constant `μ⁴/(4λ)`, and that identity is `higgs_mexican_hat`; the operator
  of record here is the one measured from the classical vacuum, which is the one bounded
  below by `0`.

## What is proved

* `card_smMom = 40`, `card_smForm = 49` — the recount of the momentum-carrying coordinates
  (`G`, `W`, `B`, `φ`) and of the squared forms (`24 + 9 + 3 + 12 + 1`);
* `realCoeff_*` — every field polynomial has real coefficients, hence acts as a symmetric
  multiplication operator;
* `smHamiltonian` — the one-particle Hamiltonian on the Gauss–polynomial core of
  `L²(ℝ¹⁶³)`, `smHamiltonian_symmetricOn`, `smHamiltonian_quadForm`,
  `smHamiltonian_quadForm_nonneg` — symmetric, with a sum-of-squares quadratic form, hence
  bounded below;
* **`sm_friedrichs_extension`** — the Standard-Model one-particle Hamiltonian has a
  positive self-adjoint (Friedrichs) extension, for every set of couplings, structure
  constants and generators;
* `higgs_mexican_hat` — the relation between the two ways of writing the Higgs potential.
* **Accounting identity (why `h` carries no separate BRST gauge-fixing term).**  The
  book's BRST-exact contribution `{Ω, Ψ}` with `Ψ = i ψ_a A_{0a}` vanishes identically on
  the temporal-gauge slice `A₀ = 0` (`BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0`,
  with the `su(2)`/SM instances in `ChapterBookBrstInstances.lean`); the temporal gauge
  used here therefore already accounts for the gauge-fixing/ghost sector, and `h` as
  defined above needs no extra summand.  For pure Yang–Mills the same identity is why the
  Weyl-gauge Hamiltonian is the sum of squares of the *spatial* fields only
  (`ChapterQymTimeIndependentFlow.lean`).  Quantum gravity is *not* treated by this
  identity: its book 3D reduction is non-ADM (constant-in-timepiece ghosts; see
  `ChapterQuantumGravityBrstCharge.lean` and `Book/Starobinsky.lean`).

## Honest boundary

This is the **bosonic** sector: gauge fields, their spatial derivatives, and the Higgs
doublet.  `h_Dirac` and `h_Yukawa` are *not* included as operators: they need the CAR /
Grassmann algebra, which the plan lists as an open boundary (D6b-SM.4, “honest boundaries
that stay open”).  What the fermionic sector contributes at this level — the unitarity
algebra of the CKM and PMNS matrices — is formalized in `BookProof.ChapterSmOneParticle`.
No spectral information, no symmetry breaking as dynamics, and no mass gap is claimed.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmHamiltonian

open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

/-! ## 1. The parameters -/

/-- The parameters of the Standard-Model one-particle operator: the three gauge couplings,
the Higgs quartic and vacuum expectation value, the structure constants of `SU(3)` and
`SU(2)`, and the real `4 × 4` matrices by which the electroweak generators `τ_j/2` and
`σ₃/2` act on the four real components of the Higgs doublet.  Nothing below uses the Lie
algebra relations: every statement holds for arbitrary real data, the physical values
included. -/
structure SmParams where
  /-- the strong coupling `g_s` -/
  gs : ℝ
  /-- the weak coupling `g` -/
  gw : ℝ
  /-- the hypercharge coupling `g'` -/
  gy : ℝ
  /-- the Higgs quartic `λ ≥ 0` -/
  lam : ℝ
  /-- the Higgs vacuum expectation value `v`, with `v² = μ²/λ` -/
  vev : ℝ
  /-- the `SU(3)` structure constants `f^{abc}` -/
  fabc : Fin 8 → Fin 8 → Fin 8 → ℝ
  /-- the `SU(2)` structure constants `ε^{abc}` -/
  eabc : Fin 3 → Fin 3 → Fin 3 → ℝ
  /-- the action of `τ_j/2` on the four real Higgs components -/
  tgen : Fin 3 → Fin 4 → Fin 4 → ℝ
  /-- the action of `σ₃/2` on the four real Higgs components -/
  ygen : Fin 4 → Fin 4 → ℝ
  /-- the quartic coupling is non-negative -/
  lam_nonneg : 0 ≤ lam

/-! ## 2. The field polynomials -/





variable {D : ℕ}

/-- **The gluon magnetic field** of one excitation,
`B^G_{a,i} = ½ ε_{ijk}(G^a_{k,j} − G^a_{j,k} + g_s f^{abd} G^b_j G^d_k)`, as a polynomial in
the coordinates reached through the embedding `co` (the identity for the one-particle
space, the parcel embedding for a Fock sector).  The structure constants are arbitrary
reals, so the quartic non-abelian magnetic energy is included. -/
def smMagG (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 8) (i : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (co (smDG a k j)) - X (co (smDG a j k))
      + ((P.gs : ℝ) : ℂ) • ∑ b : Fin 8, ∑ d : Fin 8, ((P.fabc a b d : ℝ) : ℂ) •
          (X (co (smG b j)) * X (co (smG d k))))

/-- **The weak magnetic field** `B^W_{k,i}`, the `SU(2)` analogue of `smMagG`. -/
def smMagW (P : SmParams) (co : Fin 163 → Fin D) (m : Fin 3) (i : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (co (smDW m k j)) - X (co (smDW m j k))
      + ((P.gw : ℝ) : ℂ) • ∑ b : Fin 3, ∑ d : Fin 3, ((P.eabc m b d : ℝ) : ℂ) •
          (X (co (smW b j)) * X (co (smW d k))))

/-- **The hypercharge field strength** `B^B_i = ½ ε_{ijk}(B_{k,j} − B_{j,k})`: abelian, so
linear in the coordinates. -/
def smMagB (co : Fin 163 → Fin D) (i : Fin 3) : MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (co (smDB k j)) - X (co (smDB j k)))

/-- **The covariant Higgs derivative**
`(D_i φ)_a = φ_{a,i} + g W^j_i (τ_j/2 φ)_a + g' B_i (σ₃/2 φ)_a`, written in the four real
components of the doublet. -/
def smCovD (P : SmParams) (co : Fin 163 → Fin D) (a : Fin 4) (i : Fin 3) :
    MvPolynomial (Fin D) ℂ :=
  X (co (smDPhi a i))
    + ((P.gw : ℝ) : ℂ) • ∑ j : Fin 3, ∑ b : Fin 4, ((P.tgen j a b : ℝ) : ℂ) •
        (X (co (smW j i)) * X (co (smPhi b)))
    + ((P.gy : ℝ) : ℂ) • ∑ b : Fin 4, ((P.ygen a b : ℝ) : ℂ) •
        (X (co (smB i)) * X (co (smPhi b)))

/-- **The Higgs potential as a square**: `√(λ/2)(‖φ‖² − v²)`, whose square contributes
`(λ/4)(‖φ‖² − v²)²` to the Hamiltonian. -/
def smWall (P : SmParams) (co : Fin 163 → Fin D) : MvPolynomial (Fin D) ℂ :=
  ((Real.sqrt (P.lam / 2) : ℝ) : ℂ) •
    ((∑ a : Fin 4, X (co (smPhi a)) * X (co (smPhi a))) - C ((P.vev ^ 2 : ℝ) : ℂ))











/-! ## 3. The index types: momenta and squared forms -/

/-- The coordinates carrying a conjugate momentum: the gauge fields `G^a_i`, `W^k_i`, `B_i`
and the Higgs components `φ_a`.  The spatial coordinates and the derivative coordinates
carry none. -/
abbrev SmMom : Type := (Fin 8 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ Fin 3 ⊕ Fin 4

/-- **The recount of the momentum-carrying coordinates**: `24 + 9 + 3 + 4 = 40`. -/
theorem card_smMom : Fintype.card SmMom = 40 := by simp

/-- The squared forms of the Hamiltonian: the `24` gluon magnetic components, the `9` weak
ones, the `3` hypercharge ones, the `12` covariant Higgs derivatives and the single Higgs
wall. -/
abbrev SmForm : Type := (Fin 8 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ Fin 3 ⊕ (Fin 4 × Fin 3) ⊕ Unit

/-- **The recount of the squared forms**: `24 + 9 + 3 + 12 + 1 = 49`. -/
theorem card_smForm : Fintype.card SmForm = 49 := by simp

/-- The coordinate of a momentum label. -/
def smMomCoord : SmMom → Fin 163
  | Sum.inl (a, i) => smG a i
  | Sum.inr (Sum.inl (k, i)) => smW k i
  | Sum.inr (Sum.inr (Sum.inl i)) => smB i
  | Sum.inr (Sum.inr (Sum.inr a)) => smPhi a

/-- The polynomial of a form label. -/
def smFormPoly (P : SmParams) (co : Fin 163 → Fin D) : SmForm → MvPolynomial (Fin D) ℂ
  | Sum.inl (a, i) => smMagG P co a i
  | Sum.inr (Sum.inl (k, i)) => smMagW P co k i
  | Sum.inr (Sum.inr (Sum.inl i)) => smMagB co i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (a, i)))) => smCovD P co a i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => smWall P co



/-- The labelling of the `40` momenta. -/
def smMomFin : SmMom ≃ Fin 40 := Fintype.equivFinOfCardEq card_smMom

/-- The labelling of the `49` squared forms. -/
def smFormFin : SmForm ≃ Fin 49 := Fintype.equivFinOfCardEq card_smForm

/-! ## 4. The one-particle Hamiltonian on the Gauss–polynomial core of `L²(ℝ¹⁶³)` -/

/-- The momentum operators `π = −i ∂/∂q`, one for each of the `40` momentum-carrying
coordinates. -/
def smPi (m : Fin 40) : (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163)) :=
  (coreRepPoly 163).op (momOp (smMomCoord (smMomFin.symm m)))

/-- The field operators: multiplication by the `49` real field polynomials. -/
def smField (P : SmParams) (r : Fin 49) :
    (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163)) :=
  (coreRepPoly 163).op (mulOp (smFormPoly P (id : Fin 163 → Fin 163) (smFormFin.symm r)))





/-- **The Standard-Model one-particle Hamiltonian** in temporal gauge, on the
Gauss–polynomial core of `L²(ℝ¹⁶³)`:
`h = ½ Σ_m π_m² + ½ Σ_r Φ_r²` with the `40` momenta of the gauge and Higgs fields and the
`49` squared forms of §2 — the three magnetic energies (non-abelian included), the
covariant Higgs kinetic energy, and the Higgs wall. -/
def smHamiltonian (P : SmParams) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  weylOp smPi (smField P)









/-! ## 5. The two ways of writing the Higgs potential -/





end

end BookProof.SmHamiltonian


