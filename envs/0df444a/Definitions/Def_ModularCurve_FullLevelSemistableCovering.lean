-- Prove2me | Definitions.Def_ModularCurve_FullLevelSemistableCovering
-- name    : ModularCurve_FullLevelSemistableCovering
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/18819ac0-1e02-58ed-b528-cb00a1f3d6dd
-- title:
--   Semistable coverings of full-level modular function fields
-- statement:
--   Fix a prime $q$, an integer $M'\ge 1$, a valuation subring $A$ of $\overline{\mathbb Q}$ with residue field $\kappa$, and a finite set $SS$ of places of the level-$M'$ modular function field $\mathrm{modularFunctionFieldC}\,\kappa\,M'$ over $\kappa$. The ambient field is `fieldBar q M'`, the intermediate field of $\overline{\mathbb Q}((q))$ attached to level $\Gamma_H(q^2M')$ with $H$ the kernel of reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. First, `lineInfty` is the point $[1:0]$ of the projective line over $\mathbb Z/q$. The structure `SemistableCovering` packages the following data: for each $\ell\in\mathbb P^1(\mathbb Z/q)$ a field $F^{Ig}_\ell$ over $\kappa$ with a `ComponentChart` $C^{Ig}_\ell$ of `fieldBar q M'` along $A$ reducing to it; for each $s\in SS$ a field $F^{ss}_s$ over $\kappa$ with a chart $C^{ss}_s$; and for each pair $(\ell,s)$ two `Annulus` data $\mathrm{An}_{\ell,s}$, $\mathrm{An}'_{\ell,s}$ with equal domains and equal moduli, the common modulus nonzero in $\overline{\mathbb Q}$, and with parameters whose product is the image of that modulus; the first is attached (in the sense of `Annulus.IsAttached`: the reduction of the parameter has order one at the node, with the stated unit principle) to $C^{Ig}_\ell$ at a node $x_{\ell,s}$, the second to $C^{ss}_s$ at a node $x'_{\ell,s}$. The clauses require each node of $C^{Ig}_\ell$ to be $x_{\ell,s}$ for exactly one $s$ and each node of $C^{ss}_s$ to be $x'_{\ell,s}$ for exactly one $\ell$; that every place of `fieldBar q M'` over $\overline{\mathbb Q}$ lies in the domain of exactly one Igusa chart, or exactly one supersingular chart, or exactly one annulus, and in no other of these domains; that some place in the domain of $C^{Ig}_{[1:0]}$ has valuation subring the $q$-adic one $\mathrm{qIntegersBar}$; and that each reduced field has principal divisors and only rational places. The predicate `EquivClauses` asks that for every primitive $q$-th root of unity index $\zeta$ and every $\gamma\in\Gamma_0(M')$ there is a permutation $\sigma$ of $\mathbb P^1(\mathbb Z/q)$ such that pullback along `levelAutBar q M' ζ γ` carries the valuation subring and domain of $C^{Ig}_\ell$ to those of $C^{Ig}_{\sigma\ell}$, fixes those of each $C^{ss}_s$, and carries the domain of $\mathrm{An}_{\ell,s}$ to that of $\mathrm{An}_{\sigma\ell,s}$, with equal moduli; `equivClauses_iff` restates this definition verbatim.
--
--   **Relation to Mathlib.** Mathlib has no notion of semistable covering of a curve by component charts and annuli; these are the project's own structures, phrased entirely in terms of Mathlib's `ValuationSubring`, `IntermediateField` and `LaurentSeries`.
--
--   **Where it is used.** This is the carrier for the semistable reduction at $q$ of the modular curve of level $\Gamma(q)\cap\Gamma_0(M')$, read through its function field: the Igusa components indexed by $\mathbb P^1(\mathbb F_q)$ and the components over the supersingular points meet in a complete bipartite pattern of nodes, each node being described by a pair of annuli with reciprocal parameters. It is the full-level counterpart of the specialization data used for $X_0(Mq)$, and feeds the component-group and Hecke-equivariance arguments in the level-lowering part of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelSemistableCovering.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicCurve_SemistableChartsComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

def lineInfty : CuspidalType.ProjLine q :=
  Projectivization.mk (ZMod q) ![1, 0] (by
    intro h
    have h0 := congr_fun h 0
    simp at h0)

set_option synthInstance.maxHeartbeats 400000 in

structure SemistableCovering
    (SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) : Type 1 where

  FIg : CuspidalType.ProjLine q → Type
  [instFieldIg : ∀ ℓ, Field (FIg ℓ)]
  [instAlgebraIg : ∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]

  FSS : ↥SS → Type
  [instFieldSS : ∀ s, Field (FSS s)]
  [instAlgebraSS : ∀ s, Algebra (ResidueField A) (FSS s)]

  CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)

  CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s)

  An : CuspidalType.ProjLine q → ↥SS → Annulus A (fieldBar q M')

  An' : CuspidalType.ProjLine q → ↥SS → Annulus A (fieldBar q M')

  xs : ∀ ℓ : CuspidalType.ProjLine q, ↥SS → Place (ResidueField A) (FIg ℓ)

  xt : CuspidalType.ProjLine q → ∀ s : ↥SS, Place (ResidueField A) (FSS s)

  dom_eq : ∀ ℓ s, (An' ℓ s).dom = (An ℓ s).dom

  modulus_eq : ∀ ℓ s, (An' ℓ s).modulus = (An ℓ s).modulus

  modulus_ne_zero : ∀ ℓ s, ((An ℓ s).modulus : AlgebraicClosure ℚ) ≠ 0

  param_mul : ∀ ℓ s, (An' ℓ s).param * (An ℓ s).param =
    algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((An ℓ s).modulus : AlgebraicClosure ℚ)

  isAttached : ∀ ℓ s, (An ℓ s).IsAttached (CIg ℓ) (xs ℓ s) ∧ (An' ℓ s).IsAttached (CSS s) (xt ℓ s)

  existsUnique_xs_eq : ∀ ℓ, ∀ x ∈ (CIg ℓ).nodes, ∃! s, xs ℓ s = x

  existsUnique_xt_eq : ∀ s, ∀ x ∈ (CSS s).nodes, ∃! ℓ, xt ℓ s = x

  partition : ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
    (∃ ℓ, P ∈ (CIg ℓ).dom ∧ (∀ ℓ', P ∈ (CIg ℓ').dom → ℓ' = ℓ) ∧ (∀ s, P ∉ (CSS s).dom) ∧ ∀ ℓ' s, P ∉ (An ℓ' s).dom) ∨
    (∃ s, P ∈ (CSS s).dom ∧ (∀ s', P ∈ (CSS s').dom → s' = s) ∧ (∀ ℓ, P ∉ (CIg ℓ).dom) ∧ ∀ ℓ s', P ∉ (An ℓ s').dom) ∨
    (∃ ℓ s, P ∈ (An ℓ s).dom ∧ (∀ ℓ' s', P ∈ (An ℓ' s').dom → ℓ' = ℓ ∧ s' = s) ∧
      (∀ ℓ', P ∉ (CIg ℓ').dom) ∧ ∀ s', P ∉ (CSS s').dom)

  cusp_mem : ∃ P ∈ (CIg (lineInfty q)).dom,
    P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')

  hasPrincipalDivisors_Ig : ∀ ℓ, HasPrincipalDivisors (ResidueField A) (FIg ℓ)
  hasPrincipalDivisors_SS : ∀ s, HasPrincipalDivisors (ResidueField A) (FSS s)

  isRational_Ig : ∀ ℓ (x : Place (ResidueField A) (FIg ℓ)), x.IsRational
  isRational_SS : ∀ s (x : Place (ResidueField A) (FSS s)), x.IsRational

attribute [instance] SemistableCovering.instFieldIg SemistableCovering.instAlgebraIg
  SemistableCovering.instFieldSS SemistableCovering.instAlgebraSS

example {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A SS) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) :=
  𝒞.partition P

example {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A SS) (ℓ : CuspidalType.ProjLine q) (s : ↥SS) :
    (𝒞.An ℓ s).IsAttached (𝒞.CIg ℓ) (𝒞.xs ℓ s) :=
  (𝒞.isAttached ℓ s).1

namespace SemistableCovering

variable {q M' A}
variable {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

def EquivClauses (𝒞 : SemistableCovering q M' A SS) : Prop :=
  ∀ (ζ : Idx q) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
      (∀ ℓ, ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CIg (σ ℓ)).integers ∧
        ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CIg (σ ℓ)).dom) ∧
      (∀ s, ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CSS s).integers ∧
        ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CSS s).dom) ∧
      (∀ ℓ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.An (σ ℓ) s).dom ∧
        (𝒞.An ℓ s).modulus = (𝒞.An (σ ℓ) s).modulus)

theorem equivClauses_iff (𝒞 : SemistableCovering q M' A SS) :
    𝒞.EquivClauses ↔
      ∀ (ζ : Idx q) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
          (∀ ℓ, ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CIg (σ ℓ)).integers ∧
            ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CIg (σ ℓ)).dom) ∧
          (∀ s, ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CSS s).integers ∧
            ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CSS s).dom) ∧
          (∀ ℓ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.An (σ ℓ) s).dom ∧
            (𝒞.An ℓ s).modulus = (𝒞.An (σ ℓ) s).modulus) :=
  Iff.rfl

end SemistableCovering

end ModularCurve.FullLevel

end


