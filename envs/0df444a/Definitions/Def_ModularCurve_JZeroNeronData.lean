-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronData
-- name    : ModularCurve_JZeroNeronData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/c7dfa314-f5b1-580c-9590-5be1572483b8
-- title:
--   Néron data for the torsion of JZero (N·q) at q
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and write $J=\mathrm{JZero}\,(Nq)$ for the degree-zero class group attached to the modular function field of level $Nq$ over $\overline{\mathbb Q}$, with its Galois action and with the $\mathrm{HeckeAlg}=\mathbb Z[X_\ell:\ell\text{ prime}]$-action `heckeModuleBar` (in which $X_\ell$ acts by `heckeOperatorBar`, provided these operators commute). Two helpers are introduced: `jZeroTorsion M m`, the subgroup of $\mathrm{JZero}\,M$ killed by $m$, and `inertiaInvariantTorsion M A m`, the subgroup of $m$-torsion points fixed by every element of `A.inertiaSubgroupIn ℚ`, for a valuation subring $A$ of $\overline{\mathbb Q}$. The structure `JZeroNeronData N q hqN A hA`, for $A$ lying over $q$ (i.e. $q$ is a non-unit of $A$), bundles as fields: three families of subgroups `toric m ≤ fin m ≤ finPart m ≤ jZeroTorsion (N*q) m`, each cut out of its level-$m'$ member by the $m$-torsion whenever $m\mid m'$, stable under $\mathrm{HeckeAlg}$ and under the decomposition group of $A$; the inclusion of the inertia-invariant $m$-torsion into `finPart m`, with equality when $\gcd(m,q)=1$; the clauses that inertia acts on `toric m` through the cyclotomic character ($\sigma\zeta=\zeta^{c}$ on $\mu_m$ forces $\sigma x=c\,x$) and that $\sigma x-x\in$ `toric m` for all $m$-torsion $x$ with $\gcd(m,q)=1$; for such $m$, maps `abq m` from `fin m` to $\mathrm{JZero}\,N\times \mathrm{JZero}\,N$ with kernel `toric m`, image the $m$-torsion of the product, compatible in $m$ and equivariant for $X_\ell$ ($\ell\nmid Nq$) and for the decomposition group; a finite abelian $\mathrm{HeckeAlg}$-module $\Phi$ with maps `spec m` from `finPart m` onto $\Phi[m]$ (for $m>0$) with kernel `fin m`, Hecke-equivariant, inertia-invariant and compatible in $m$.
--
--   Further fields record, as hypotheses-and-conclusions rather than as derived results: $X_\ell-(\ell+1)$ annihilates $\Phi$ for $\ell\nmid Nq$; on `toric m` with $\gcd(m,q)=1$, a Frobenius at $q$ acts with square $q^2$ and indeed as $q\,X_q$; elements of `toric m` lying in the $\mathfrak m$-torsion, for a maximal $\mathfrak m$ with $\Phi[\mathfrak m]=0$, lie in `toricMonodromyPart`, the $\mathrm{HeckeAlg}$-span of the differences $\sigma x-x$ with $\sigma$ inertial and $x$ killed by some positive integer coprime to $q$; and a Raynaud clause: for $q\ne 2$, a subgroup $V$ of the $q$-torsion admitting an additive, Galois-compatible bijection with the $\overline{\mathbb Q}$-points of a finite flat cocommutative Hopf algebra over the subring of $\mathbb Q$ of elements with denominator prime to $q$ (points taken with the convolution group law, `WithConv`) satisfies $V\le$ `finPart q`. The clauses mentioning the Hecke action take `HeckeInputsAll (N*q)` and `HeckeOperatorsCommuteBar (N*q)` as explicit hypotheses. Finally, `HasJZeroNeronData N q hqN` asserts that such a datum exists for every valuation subring of $\overline{\mathbb Q}$ lying over $q$.
--
--   **Relation to Mathlib.** Mathlib has no Néron model of $J_0(N)$ or component group at a prime of bad reduction; the filtration by toric, connected-finite and finite parts, the specialisation maps and the component group are packaged here as fields of a project-specific structure. `jZeroTorsion` is Mathlib's `Submodule.torsionBy ℤ` read as an additive subgroup, and the inertia subgroup used is the project's [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21), built from Mathlib's `ValuationSubring.inertiaSubgroup`.
--
--   **Where it is used.** These data encode the local structure at $q$ of the torsion of the Jacobian of level $Nq$ that is used for level lowering: the toric part with its Frobenius and monodromy behaviour, the abelian quotient mapping to two copies of level $N$, and the component group with its Eisenstein annihilator. The Raynaud clause supplies the finite-flat input at $q\neq 2$ needed to place a $q$-torsion subgroup inside the finite part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronData.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section

namespace ModularCurve

open ValuationSubring

section JZeroNeronAux
variable (M : ℕ) [NeZero M]

abbrev jZeroTorsion (m : ℕ) : AddSubgroup (JZero M) :=
  (Submodule.torsionBy ℤ (JZero M) (m : ℤ)).toAddSubgroup

def inertiaInvariantTorsion (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero M) where
  carrier := {x | x ∈ jZeroTorsion M m ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x}
  zero_mem' := ⟨AddSubgroup.zero_mem _, fun σ _ => smul_zero σ⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨AddSubgroup.add_mem _ hx hy, fun σ hσ => by rw [smul_add, hx' σ hσ, hy' σ hσ]⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨AddSubgroup.neg_mem _ hx, fun σ hσ => by rw [smul_neg, hx' σ hσ]⟩

end JZeroNeronAux

structure JZeroNeronData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : Type 1 where

  toric : ℕ → AddSubgroup (JZero (N * q))

  fin : ℕ → AddSubgroup (JZero (N * q))

  finPart : ℕ → AddSubgroup (JZero (N * q))
  toric_le_fin : ∀ m, toric m ≤ fin m
  fin_le_finPart : ∀ m, fin m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion (N * q) m

  toric_inf : ∀ m m' : ℕ, m ∣ m' → toric m = toric m' ⊓ jZeroTorsion (N * q) m
  fin_inf : ∀ m m' : ℕ, m ∣ m' → fin m = fin m' ⊓ jZeroTorsion (N * q) m
  finPart_inf : ∀ m m' : ℕ, m ∣ m' → finPart m = finPart m' ⊓ jZeroTorsion (N * q) m

  invariants_le_finPart : ∀ m, inertiaInvariantTorsion (N * q) A m ≤ finPart m

  finPart_eq_of_coprime : ∀ m, m.Coprime q → finPart m = inertiaInvariantTorsion (N * q) A m

  toric_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ toric m →
    (letI := heckeModuleBar (N * q); t • x) ∈ toric m
  fin_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ fin m →
    (letI := heckeModuleBar (N * q); t • x) ∈ fin m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ finPart m →
    (letI := heckeModuleBar (N * q); t • x) ∈ finPart m

  toric_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ toric m, σ • x ∈ toric m
  fin_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ fin m, σ • x ∈ fin m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  inertia_unipotent : ∀ (m : ℕ), m.Coprime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion (N * q) m, σ • x - x ∈ toric m

  abq : ∀ m : ℕ, m.Coprime q → (↥(fin m) →+ (JZero N × JZero N))

  abq_ker : ∀ (m : ℕ) (hm : m.Coprime q) (x : ↥(fin m)), abq m hm x = 0 ↔ (x : JZero (N * q)) ∈ toric m

  abq_range : ∀ (m : ℕ) (hm : m.Coprime q),
    (abq m hm).range = (Submodule.torsionBy ℤ (JZero N × JZero N) (m : ℤ)).toAddSubgroup

  abq_compat : ∀ (m m' : ℕ) (hm : m.Coprime q) (hm' : m'.Coprime q) (h : m ∣ m') (x : ↥(fin m))
    (hx : (x : JZero (N * q)) ∈ fin m'), abq m' hm' ⟨x, hx⟩ = abq m hm x

  abq_hecke : ∀ (m : ℕ) (hm : m.Coprime q) (ℓ : Nat.Primes), ¬ (ℓ : ℕ) ∣ N * q → ∀ (x : ↥(fin m)),
    abq m hm ⟨(letI := heckeModuleBar (N * q); heckeGen ℓ • (x : JZero (N * q))),
               fin_hecke m (heckeGen ℓ) x x.2⟩
      = (letI := heckeModuleBar N; (heckeGen ℓ • (abq m hm x).1, heckeGen ℓ • (abq m hm x).2))

  abq_dec : ∀ (m : ℕ) (hm : m.Coprime q) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : ↥(fin m)),
    abq m hm ⟨σ • (x : JZero (N * q)), fin_dec m σ hσ x x.2⟩ = (σ • (abq m hm x).1, σ • (abq m hm x).2)

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero (N * q)) ∈ fin m

  spec_range : ∀ (m : ℕ), 0 < m → (spec m).range = (Submodule.torsionBy ℤ Φ (m : ℤ)).toAddSubgroup

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar (N * q); t • (x : JZero (N * q))), finPart_hecke m t x x.2⟩ = t • spec m x

  spec_inertia : ∀ (m : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : ↥(finPart m)) (hσx : σ • (x : JZero (N * q)) ∈ finPart m), spec m ⟨_, hσx⟩ = spec m x

  spec_compat : ∀ (m m' : ℕ) (h : m ∣ m') (x : ↥(finPart m)) (hx : (x : JZero (N * q)) ∈ finPart m'),
    spec m' ⟨x, hx⟩ = spec m x

  Φ_eisenstein : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

  toric_frob_sq : ∀ (m : ℕ), m.Coprime q → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
    ∀ x ∈ toric m, σ • σ • x = ((q : ℤ) ^ 2) • x

  toric_frob_hecke : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ (m : ℕ), m.Coprime q → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ q →
      ∀ x ∈ toric m, σ • x = (letI := heckeModuleBar (N * q); (((q : ℕ) : HeckeAlg) * heckeGen ⟨q, Fact.out⟩) • x)

  toric_monodromy : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ (m : ℕ), m.Coprime q → ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → heckeTorsion Φ 𝔪 = ⊥ →
      ∀ x ∈ toric m, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
        (letI := heckeModuleBar (N * q); x ∈ toricMonodromyPart (J := JZero (N * q)) q (A.inertiaSubgroupIn ℚ))

  raynaud : q ≠ 2 → ∀ (V : AddSubgroup (JZero (N * q))), V ≤ jZeroTorsion (N * q) q →
    ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
      [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
      (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥V),
      (∀ f g, e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → ((e g : ↥V) : JZero (N * q)) = σ • ((e f : ↥V) : JZero (N * q))) →
      V ≤ finPart q

attribute [instance] JZeroNeronData.instAddCommGroupΦ JZeroNeronData.instFiniteΦ JZeroNeronData.instModuleΦ

def HasJZeroNeronData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronData N q hqN A hA)

end ModularCurve

end


