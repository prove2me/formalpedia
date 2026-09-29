-- Prove2me | Definitions.Def_ModularCurve_JZeroGoodReductionV3
-- name    : ModularCurve_JZeroGoodReductionV3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/bdce99fb-611e-59b8-921c-aa88e6bc5a30
-- title:
--   Good-reduction specialization data for J0​(N), prime-to-ℓ variant
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ and $N \neq 0$, and work with $J_0(N) =$ `JZero N`, the degree-zero divisor class group of the modular function field over $\overline{\mathbb{Q}}$, and with $J' =$ `Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)`, the corresponding group for the field obtained by adjoining to the residue field $k =$ `ResidueField A` inside $k((q))$ the two Laurent series `jqModC k` and its $N$-fold $q$-substitute `jqNModC k N`; both carry `HeckeAlg`-module structures, `HeckeAlg` being the polynomial algebra $\mathbb{Z}[T_q : q \text{ prime}]$ with generators `heckeGen q`. The structure `JZeroGoodReductionSpecialization_alt` bundles an additive map $sp : J_0(N) \to J'$ and an additive endomorphism $F$ of $J'$, together with: surjectivity of $sp$; full `HeckeAlg`-equivariance $sp(T\cdot x) = T\cdot sp(x)$; invariance $sp(\sigma \cdot x) = sp(x)$ for $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$; the identity $sp(\sigma \cdot x) = F(sp(x))$ for every $\sigma$ which is a Frobenius at $A$ for $\ell$ (i.e. lies in the decomposition subgroup and acts on $k$ as $x \mapsto x^{\ell}$); injectivity of $sp$ on $p$-power torsion for every natural number $p$ with $\ell \nmid p$; and the field `sfr`, asserting the special-fibre relation $F^2(y) - T_\ell F(y) + \ell y = 0$ for all $y \in J'$.
--
--   The torsion clause here is indexed by all $p$ not divisible by $\ell$ (thus excluding $p = 0$ and multiples of $\ell$), rather than by primes $p \neq \ell$. Accompanying results record that $\ker(sp)$ is stable under each `heckeGen q`, and convert the data, for any $p$ with $\ell \nmid p$, into `IsSpecialization` for that $p$ and into the conjunction of `IsSpecialization` with `SpecialFibreRelation` required by `SpecializationExists`.
--
--   **Relation to Mathlib.** The Jacobian-like group `Pic0`, the Hecke algebra `HeckeAlg` and the specialization predicates are the project's own; the inertia and decomposition subgroups of a valuation subring come from Mathlib's ramification-group material, while `IsFrobeniusAt` is defined in the project as acting by $\ell$-th powers on the residue field.
--
--   **Where it is used.** This carrier packages the reduction of $J_0(N)$ at a place where the modular curve has good reduction, in the form required by the Eichler–Shimura congruence relation input to level lowering: the quadratic relation satisfied by Frobenius on the special fibre, transported to prime-to-$\ell$ torsion of $J_0(N)$ by an inertia-invariant, Hecke-equivariant specialization map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroGoodReductionV3.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SpecializationWitness
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JZeroGoodReductionV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve IsLocalRing

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp

attribute [local instance] ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp
variable [Module HeckeAlg (JZero N)]

variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

variable (A) (ℓ) (hℓ) (N) in

structure JZeroGoodReductionSpecialization_alt where

  sp : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  F : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  hsurj : Function.Surjective sp

  hecke_comm : ∀ (T : HeckeAlg) (x : JZero N), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero N, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt σ ℓ →
    ∀ x : JZero N, sp (σ • x) = F (sp x)

  injective_torsion : ∀ (p : ℕ), ¬ ℓ ∣ p → ∀ (x : JZero N),
    (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  sfr : SpecialFibreRelation
    (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ F

namespace JZeroGoodReductionSpecialization_alt

theorem hgen (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    (q : Nat.Primes) (a : JZero N) (ha : D.sp a = 0) :
    D.sp (heckeGen q • a) = 0 := by
  rw [D.hecke_comm, ha, smul_zero]

theorem toIsSpecialization (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
      (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      A ℓ D.sp D.F where
  hecke_comm := D.hecke_comm
  inertia_comm := D.inertia_comm
  frobenius_comm := D.frobenius_comm
  injective_torsion := fun x hx hker => D.injective_torsion p hℓp x hx hker

theorem toSpecializationExistsBody (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
        (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) A ℓ D.sp D.F
      ∧ SpecialFibreRelation
          (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ D.F :=
  ⟨D.toIsSpecialization hℓp, D.sfr⟩

end JZeroGoodReductionSpecialization_alt

end ModularCurve

end


