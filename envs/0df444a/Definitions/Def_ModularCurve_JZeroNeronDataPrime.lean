-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronDataPrime
-- name    : ModularCurve_JZeroNeronDataPrime
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/9c203303-09f9-5dde-a03b-43fd099e9a8b
-- title:
--   Néron data for J0​(p) at the prime level
-- statement:
--   Throughout, $p$ is a prime, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`A.LiesOverPrime p`), and $J=$ `JZero p` is the degree-zero divisor class group attached to the level-$p$ modular function field over $\overline{\mathbb{Q}}$, carrying the Galois action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and the action of the polynomial Hecke algebra `HeckeAlg` through `heckeModuleBar p`. First, `inertiaInvariantPoints p A` is the subgroup of all $x\in J$ fixed by every element of the inertia subgroup `A.inertiaSubgroupIn ℚ` (no torsion condition), with `mem_inertiaInvariantPoints` its membership criterion.
--
--   The structure `JZeroNeronDataPrime p A hA` bundles, purely in terms of subgroups of $J$ and additive maps out of them, the data one extracts from the Néron model of $J_0(p)$ at $A$: two families of subgroups `toric m ≤ finPart m` of the $m$-torsion `jZeroTorsion p m`, each cut out from higher level by intersection with $m$-torsion; the inclusion of the inertia-invariant $m$-torsion in `finPart m`, with equality when $\gcd(m,p)=1$; stability of both families under Hecke operators and under the decomposition subgroup; inertia acting on `toric m` through the cyclotomic character and unipotently on $m$-torsion for $m$ prime to $p$; a rank `toricRank` with $\#\,$`toric m`$=m^{\text{toricRank}}$ for $m>0$; a finite `HeckeAlg`-module $\Phi$ of order prime to $p$ together with maps $\mathrm{spec}_m:\,$`finPart m`$\to\Phi$ having kernel `toric m`, image $\Phi[m]$, Hecke-equivariant, inertia-invariant and compatible in $m$; a homomorphism `redComponent` on all inertia-invariant points extending the $\mathrm{spec}_m$, Hecke-equivariant, whose kernel consists of the points divisible by $\#\Phi$ inside the inertia-invariant points; Eisenstein annihilation $(T_\ell-(\ell+1))\Phi=0$ for $\ell\neq p$; the relations $\sigma^2=p^2$ and $\sigma=p\,T_p$ on prime-to-$p$ toric torsion for $\sigma$ a Frobenius at $p$; and, for $p\neq 2$, a prolongation clause: a subgroup $V$ of $J[p]$ realised, compatibly with addition and the Galois action, as the convolution group of $\overline{\mathbb{Q}}$-points of a finite flat cocommutative Hopf algebra over the subring of $\mathbb{Q}$ with denominators prime to $p$ lies in `finPart p`. The last two clauses and the Eisenstein clause are conditional on `HeckeInputsAll p` and `HeckeOperatorsCommuteBar p`.
--
--   `HasJZeroNeronDataPrime p` asserts that such data exist for every such $A$. Finally `fixedPoints_le_inertiaInvariantPoints` places the Galois-fixed points of $J$ inside the inertia-invariant points; `redComponentRat` is the restriction of `redComponent` along this inclusion, and `M0` is its kernel inside the Galois-fixed points. Compared with the composite-level `JZeroNeronData`, the present structure has two layers rather than three, carries no degeneracy maps to lower level and no toric monodromy clause, and adds the toric rank, the coprimality of $\#\Phi$ with $p$, and the component map on all inertia-invariant points.
--
--   **Relation to Mathlib.** Mathlib has no Néron models, component groups or finite parts of quasi-finite flat groups; this structure is the project's own bundling of the relevant properties as subgroups of a class group together with maps to a finite Hecke module. It is built on Mathlib's `ValuationSubring.decompositionSubgroup`, on the project notions `LiesOverPrime`, `inertiaSubgroupIn` and `IsFrobeniusAt`, and, for the rational points, on Mathlib's `FixedPoints.addSubgroup`.
--
--   **Where it is used.** Nothing is asserted here: the structure is inhabited only by a separate existence statement, and its fields are what later arguments at level $p$ consume — the Eisenstein quotient and specialisation arguments for $J_0(p)$, and the finite-index input $M_0 \le J_0(p)(\mathbb{Q})$ used by the fppf/Kummer part of the level-lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronDataPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring

def inertiaInvariantPoints (p : ℕ) [NeZero p] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (JZero p) where
  carrier := {x | ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := by
    intro x y hx hy σ hσ
    rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := by
    intro x hx σ hσ
    rw [smul_neg, hx σ hσ]

theorem mem_inertiaInvariantPoints {p : ℕ} [NeZero p] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {x : JZero p} : x ∈ inertiaInvariantPoints p A ↔ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  Iff.rfl

structure JZeroNeronDataPrime (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) : Type 1 where

  toric : ℕ → AddSubgroup (JZero p)

  finPart : ℕ → AddSubgroup (JZero p)
  toric_le_finPart : ∀ m, toric m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion p m

  toric_inf : ∀ m m' : ℕ, m ∣ m' → toric m = toric m' ⊓ jZeroTorsion p m
  finPart_inf : ∀ m m' : ℕ, m ∣ m' → finPart m = finPart m' ⊓ jZeroTorsion p m

  invariants_le_finPart : ∀ m, inertiaInvariantTorsion p A m ≤ finPart m

  finPart_eq_of_coprime : ∀ m, m.Coprime p → finPart m = inertiaInvariantTorsion p A m

  toric_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero p), x ∈ toric m →
    (letI := heckeModuleBar p; t • x) ∈ toric m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero p), x ∈ finPart m →
    (letI := heckeModuleBar p; t • x) ∈ finPart m

  toric_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ toric m, σ • x ∈ toric m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  inertia_unipotent : ∀ (m : ℕ), m.Coprime p → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion p m, σ • x - x ∈ toric m

  toricRank : ℕ

  card_toric : ∀ m : ℕ, 0 < m → Nat.card ↥(toric m) = m ^ toricRank

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  card_Φ_coprime : (Nat.card Φ).Coprime p

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero p) ∈ toric m

  spec_range : ∀ (m : ℕ), 0 < m → (spec m).range = (Submodule.torsionBy ℤ Φ (m : ℤ)).toAddSubgroup

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar p; t • (x : JZero p)), finPart_hecke m t x x.2⟩ = t • spec m x

  spec_inertia : ∀ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : ↥(finPart m)) (hσx : σ • (x : JZero p) ∈ finPart m), spec m ⟨_, hσx⟩ = spec m x

  spec_compat : ∀ (m m' : ℕ) (h : m ∣ m') (x : ↥(finPart m)) (hx : (x : JZero p) ∈ finPart m'),
    spec m' ⟨x, hx⟩ = spec m x

  redComponent : ↥(inertiaInvariantPoints p A) →+ Φ

  red_spec : ∀ (m : ℕ) (x : ↥(finPart m)) (hx : (x : JZero p) ∈ inertiaInvariantPoints p A),
    redComponent ⟨x, hx⟩ = spec m x

  red_ker_iff : ∀ x : ↥(inertiaInvariantPoints p A),
    redComponent x = 0 ↔ ∃ y : ↥(inertiaInvariantPoints p A), (Nat.card Φ) • y = x

  red_hecke : ∀ (t : HeckeAlg) (x : JZero p) (hx : x ∈ inertiaInvariantPoints p A)
    (htx : (letI := heckeModuleBar p; t • x) ∈ inertiaInvariantPoints p A),
    redComponent ⟨_, htx⟩ = t • redComponent ⟨x, hx⟩

  Φ_eisenstein : HeckeInputsAll p → HeckeOperatorsCommuteBar p →
    ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

  toric_frob_sq : ∀ (m : ℕ), m.Coprime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
    ∀ x ∈ toric m, σ • σ • x = ((p : ℤ) ^ 2) • x

  toric_frob_hecke : HeckeInputsAll p → HeckeOperatorsCommuteBar p →
    ∀ (m : ℕ), m.Coprime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
      ∀ x ∈ toric m, σ • x = (letI := heckeModuleBar p; (((p : ℕ) : HeckeAlg) * heckeGen ⟨p, Fact.out⟩) • x)

  raynaud : p ≠ 2 → ∀ (V : AddSubgroup (JZero p)), V ≤ jZeroTorsion p p →
    ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
      [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
      (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V),
      (∀ f g, e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero p) = σ • ((e f : ↥V) : JZero p)) →
      V ≤ finPart p

attribute [instance] JZeroNeronDataPrime.instAddCommGroupΦ JZeroNeronDataPrime.instFiniteΦ
  JZeroNeronDataPrime.instModuleΦ

def HasJZeroNeronDataPrime (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), Nonempty (JZeroNeronDataPrime p A hA)

section RationalPoints

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

theorem fixedPoints_le_inertiaInvariantPoints :
    FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p) ≤ inertiaInvariantPoints p A :=
  fun _ hx σ _ => hx σ

def JZeroNeronDataPrime.redComponentRat (D : JZeroNeronDataPrime p A hA) :
    ↥(FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p)) →+ D.Φ :=
  D.redComponent.comp (AddSubgroup.inclusion (fixedPoints_le_inertiaInvariantPoints p A))

def JZeroNeronDataPrime.M0 (D : JZeroNeronDataPrime p A hA) :
    AddSubgroup ↥(FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p)) :=
  (D.redComponentRat p A hA).ker

end RationalPoints

end ModularCurve

end


