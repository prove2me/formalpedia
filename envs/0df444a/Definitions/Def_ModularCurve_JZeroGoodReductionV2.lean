-- Prove2me | Definitions.Def_ModularCurve_JZeroGoodReductionV2
-- name    : ModularCurve_JZeroGoodReductionV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/557a5cb4-8d83-59b0-bf98-57600396ed2d
-- title:
--   Good-reduction specialisation data for J0​(N) at a place above ℓ
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ (with proof `hℓ`), and a level $N \neq 0$, and assume the project's Hecke algebra `HeckeAlg` acts on both `JZero N` and on $\mathrm{Pic}^0$ of the function field `modularFunctionFieldC (ResidueField A) N` over the residue field of $A$. The structure `JZeroGoodReductionSpecialization` bundles, as data and fields, a specialisation situation in characteristic $\ell$: an additive group homomorphism `sp` from `JZero N` to that $\mathrm{Pic}^0$, an additive endomorphism `F` of the target (the intended geometric Frobenius), and five properties asserted as structure fields — `hsurj`, surjectivity of `sp`; `hecke_comm`, $\mathrm{sp}(T\cdot x) = T\cdot \mathrm{sp}(x)$ for every $T \in$ `HeckeAlg`; `inertia_comm`, $\mathrm{sp}(\sigma\cdot x) = \mathrm{sp}(x)$ for every $\sigma$ in `A.inertiaSubgroupIn ℚ`; `frobenius_comm`, $\mathrm{sp}(\sigma\cdot x) = F(\mathrm{sp}(x))$ for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ satisfying `A.IsFrobeniusAt σ ℓ`; and `injective_torsion`, injectivity of `sp` on $p$-power torsion for every prime $p \neq \ell$ (explicitly: if $p^n\cdot x = 0$ for some $n$ and $\mathrm{sp}(x)=0$ then $x=0$). The primality guard on $p$ matters: without it the case $p = 0$ would force `sp` to be injective outright. A final field `sfr` asserts the project's predicate `SpecialFibreRelation ℓ hℓ F` for this $F$ (the intended Eichler–Shimura relation); that predicate, like `IsSpecialization`, `JZero`, `Pic0`, `modularFunctionFieldC` and `heckeGen`, is defined in the imported project modules. Nothing in the structure refers to a Néron model or to reduction of curves; the geometric content is carried entirely by the assumed fields.
--
--   Three small lemmas follow: `hgen`, that the kernel of `sp` is stable under each Hecke generator `heckeGen q`; `toIsSpecialization`, extracting from the bundle the project's predicate `IsSpecialization p (JZero N) … A ℓ D.sp D.F` for any prime $p \neq \ell$; and `toSpecializationExistsBody`, the conjunction of that predicate with `SpecialFibreRelation`. Two local instances supply decidable equality on the residue field (classically) and the residue-field algebra structure on the modular function field.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (`ValuationSubring`, `AlgebraicClosure ℚ`, residue fields, Galois group actions); the Jacobian `JZero`, the degree-zero Picard group of a function field, the Hecke algebra and the specialisation and special-fibre predicates are all the project's own definitions from the imported modules.
--
--   **Where it is used.** This bundle is the interface through which the characteristic-$\ell$ reduction of $J_0(N)$ enters the argument: a term of this structure is what later modules consume to run the Eichler–Shimura/Frobenius comparison on $\ell$-torsion in the Galois representations attached to $J_0(N)$, on the route towards level lowering and Ribet's theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroGoodReductionV2.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SpecializationWitness
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve IsLocalRing

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]

noncomputable local instance instDecEqResidueFieldF3nrp : DecidableEq (ResidueField A) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 80000 in

noncomputable local instance instAlgebraResidueFieldModularFunctionFieldCF3nrp :
    Algebra (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  inferInstance

variable [Module HeckeAlg (JZero N)]

variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

variable (A) (ℓ) (hℓ) (N) in

structure JZeroGoodReductionSpecialization where

  sp : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  F : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  hsurj : Function.Surjective sp

  hecke_comm : ∀ (T : HeckeAlg) (x : JZero N), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero N, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt σ ℓ →
    ∀ x : JZero N, sp (σ • x) = F (sp x)

  injective_torsion : ∀ (p : ℕ), p.Prime → p ≠ ℓ → ∀ (x : JZero N),
    (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  sfr : SpecialFibreRelation
    (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ F

namespace JZeroGoodReductionSpecialization

theorem hgen (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    (q : Nat.Primes) (a : JZero N) (ha : D.sp a = 0) :
    D.sp (heckeGen q • a) = 0 := by
  rw [D.hecke_comm, ha, smul_zero]

theorem toIsSpecialization (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
      (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      A ℓ D.sp D.F where
  hecke_comm := D.hecke_comm
  inertia_comm := D.inertia_comm
  frobenius_comm := D.frobenius_comm
  injective_torsion := fun x hx hker => D.injective_torsion p hp hpℓ x hx hker

theorem toSpecializationExistsBody (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
        (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) A ℓ D.sp D.F
      ∧ SpecialFibreRelation
          (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ D.F :=
  ⟨D.toIsSpecialization hp hpℓ, D.sfr⟩

end JZeroGoodReductionSpecialization

end ModularCurve

end


