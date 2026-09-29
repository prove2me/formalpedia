-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronAtPDataCore
-- name    : ModularCurve_JZeroNeronAtPDataCore
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/e086adec-a59f-5fd5-9983-3e260329a1c6
-- title:
--   Core at-q Néron data for J0​(Nq)
-- statement:
--   Fix $N\ge 1$, a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$ (`A.LiesOverPrime q`). The structure `JZeroNeronAtPDataCore` packages, as fields, the data and properties about $J=$ `JZero (N*q)` at the place $A$ that are actually read by the arguments in residue characteristic $q$. The data are three families of subgroups $m\mapsto$ `toric m`, `fin m`, `finPart m` of $J$ with `toric m ≤ fin m ≤ finPart m ≤ jZeroTorsion (N*q) m`, the last being the $m$-torsion $J[m]$; `finPart m` is stable under the action of the Hecke ring `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ acting through `heckeModuleBar`, and under the decomposition subgroup of $A$ over $\mathbb Q$. Inertia acts on `toric m` through the mod-$m$ cyclotomic character: if $\sigma$ lies in the inertia subgroup and $\sigma\zeta=\zeta^c$ for all $\zeta$ with $\zeta^m=1$, then $\sigma\cdot x=c\cdot x$ for $x\in$ `toric m`. There is a finite abelian group $\Phi$ with a `HeckeAlg`-module structure and Hecke-equivariant homomorphisms $\mathrm{spec}_m\colon$ `finPart m` $\to\Phi$ whose kernel is exactly `fin m`; granted the Hecke inputs and commutativity at level $Nq$, $\Phi$ is Eisenstein: $(X_\ell-(\ell+1))\varphi=0$ for all primes $\ell\nmid Nq$ and $\varphi\in\Phi$. A Raynaud prolongation clause says: if $q\ne 2$ and $V\le J[q]$ admits a finite flat cocommutative Hopf algebra $H$ over the subring [`GaloisRep.ratLocalizedAt q`](../def/GaloisRep_Flat.html#L8) of rationals with denominator prime to $q$, together with a bijection from the convolution group of $H$-points in $\overline{\mathbb Q}$ onto $V$ that is additive and Galois-compatible, then $V\le$ `finPart q`. Finally two detection clauses: for $\mathfrak m\subset$ `HeckeAlg` maximal with $q\in\mathfrak m$, an element of `fin q` killed by $\mathfrak m$ and outside `toric q` yields `HasLowerLevelTorsion (primesOf (N*q)) 𝔪 (JZero N)` (a nonzero element of $J_0(N)$ killed by the integers in $\mathfrak m$ and by the $X_\ell-b\in\mathfrak m$ for $\ell\nmid Nq$), and, under the extra hypothesis $X_q\notin\mathfrak m$, that the $\mathfrak m$-torsion of `JZero N` is nonzero. `HasJZeroNeronAtPDataCore N q hqN` asserts such a structure exists for every $A$ above $q$, and `JZeroNeronAtPDataSameIdeal.toCore` extracts this core from the full same-ideal datum, discarding the prime-to-$q$ fields (compatibility of the filtrations under divisibility, the abelian quotient maps, the cardinality pins, the Frobenius and toric-monodromy clauses).
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — valuation subrings with their decomposition and inertia subgroups, `HopfAlgebra`, `Module.Flat`, `Coalgebra.IsCocomm` and the convolution monoid `WithConv` — but has no Jacobian of a modular curve, no Hecke algebra and no Néron-model data; `HeckeAlg` (a polynomial ring on the primes), `JZero` and these carriers are the project's own.
--
--   **Where it is used.** This is the interface through which the level-lowering arguments at the residue characteristic read the Néron model of $J_0(Nq)$ at $q$: the Raynaud prolongation clause, the Eisenstein component group, the multiplicative-type toric part and the two detection clauses together give Mazur's principle and the passage from mod-$q$ eigenforms of level $Nq$ to level $N$, used in the Frey–Serre–Ribet reduction of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronAtPDataCore.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataSameIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : Type 1 where

  toric : ℕ → AddSubgroup (JZero (N * q))

  fin : ℕ → AddSubgroup (JZero (N * q))

  finPart : ℕ → AddSubgroup (JZero (N * q))
  toric_le_fin : ∀ m, toric m ≤ fin m
  fin_le_finPart : ∀ m, fin m ≤ finPart m
  finPart_le_torsion : ∀ m, finPart m ≤ jZeroTorsion (N * q) m
  finPart_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : JZero (N * q)), x ∈ finPart m →
    (letI := heckeModuleBar (N * q); t • x) ∈ finPart m
  finPart_dec : ∀ (m : ℕ), ∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ finPart m, σ • x ∈ finPart m

  inertia_toric : ∀ (m : ℕ), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (c : ℕ),
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) → ∀ x ∈ toric m, σ • x = c • x

  Φ : Type
  [instAddCommGroupΦ : AddCommGroup Φ]
  [instFiniteΦ : Finite Φ]
  [instModuleΦ : Module HeckeAlg Φ]

  spec : ∀ m : ℕ, (↥(finPart m) →+ Φ)

  spec_ker : ∀ (m : ℕ) (x : ↥(finPart m)), spec m x = 0 ↔ (x : JZero (N * q)) ∈ fin m

  spec_hecke : ∀ (m : ℕ) (t : HeckeAlg) (x : ↥(finPart m)),
    spec m ⟨(letI := heckeModuleBar (N * q); t • (x : JZero (N * q))), finPart_hecke m t x x.2⟩ = t • spec m x

  Φ_eisenstein : HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q → ∀ φ : Φ, (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • φ = 0

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

  fin_heckeTorsion_detects_lowerLevel :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; HasLowerLevelTorsion (primesOf (N * q)) 𝔪 (JZero N))

  fin_heckeTorsion_detects_lowerLevel_sameIdeal :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 → heckeGen ⟨q, Fact.out⟩ ∉ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; heckeTorsion (JZero N) 𝔪 ≠ ⊥)

attribute [instance] JZeroNeronAtPDataCore.instAddCommGroupΦ JZeroNeronAtPDataCore.instFiniteΦ
  JZeroNeronAtPDataCore.instModuleΦ

def HasJZeroNeronAtPDataCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataCore N q hqN A hA)

def JZeroNeronAtPDataSameIdeal.toCore {N q : ℕ} [NeZero N] [Fact q.Prime] {hqN : ¬ q ∣ N}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime q}
    (D : JZeroNeronAtPDataSameIdeal N q hqN A hA) : JZeroNeronAtPDataCore N q hqN A hA where
  toric := D.toric
  fin := D.fin
  finPart := D.finPart
  toric_le_fin := D.toric_le_fin
  fin_le_finPart := D.fin_le_finPart
  finPart_le_torsion := D.finPart_le_torsion
  finPart_hecke := D.finPart_hecke
  finPart_dec := D.finPart_dec
  inertia_toric := D.inertia_toric
  Φ := D.Φ
  spec := D.spec
  spec_ker := D.spec_ker
  spec_hecke := D.spec_hecke
  Φ_eisenstein := D.Φ_eisenstein
  raynaud := D.raynaud
  fin_heckeTorsion_detects_lowerLevel := D.fin_heckeTorsion_detects_lowerLevel
  fin_heckeTorsion_detects_lowerLevel_sameIdeal := D.fin_heckeTorsion_detects_lowerLevel_sameIdeal

end ModularCurve

end


