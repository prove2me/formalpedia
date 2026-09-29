-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
-- name    : ModularCurve_JZeroNeronPrimaryTorsionFlag
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/486909f9-318e-583c-913e-4c8788c3ccc3
-- title:
--   Jordan–Hölder flags for Eisenstein primary-torsion fppf sheaves
-- statement:
--   Fix primes $p,q$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit in $A$, a record $C$ of type `JZeroNeronPrimaryTorsionCore p q A hA` (fppf abelian sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$, flat finite-type $\mathbb Z$-Hopf algebras $H_m$ representing their sections through the convolution monoid `WithConv`, and a bijection `genericPoints` from the convolution group of $\mathbb Z$-algebra maps $H_m \to \overline{\mathbb Q}$ onto `eisensteinPrimaryTorsionBar p q m`, the intersection of the kernel of $q^m$ on $J_0(p)$ with the union over $k$ of the $(\mathfrak m^k)$-torsion for $\mathfrak m$ the Eisenstein maximal ideal $\mathrm{eisensteinEval}_p^{-1}(q)$ of the Hecke algebra), and a level $m$. The structure `JZeroNeronPrimaryTorsionFlag` packages: a length $n$; commutative rings $G_i$ ($i \in \mathrm{Fin}(n+1)$) that are flat finite-type $\mathbb Z$-Hopf algebras, surjections $\pi_i : H_m \to G_i$ and surjections $G_{i+1} \to G_i$ commuting with the $\pi_i$; sheaves $F_i$ with monomorphisms $\iota_i : F_i \to \mathcal J_m$ and maps $F_i \to F_{i+1}$ whose composite with $\iota_{i+1}$ is $\iota_i$; per-$i$ additive identifications of the sections of $F_i$ over an fppf object $U$ with the convolution group of $\mathbb Z$-algebra maps $G_i \to \Gamma(U,\top)$, compatible with the core's identification via $\pi_i$; the requirement that $G_0$ admit at most one $\mathbb Z$-algebra map to $\overline{\mathbb Q}$ and that $\iota_{\mathrm{last}}$ be an isomorphism.
--
--   On generic fibres it carries subgroups $M_i \le J_0(p)$, each contained in `eisensteinPrimaryTorsionBar p q m`, monotone, with $M_0 = \bot$, $M_n$ the whole of that group, stable under $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and pinned as the image under `genericPoints` of the classes $g \circ \pi_i$. Each layer $i < n$ carries a label `kind i` (`const` or `mult`): in the `const` case $\sigma x - x \in M_i$ for $x \in M_{i+1}$; in the `mult` case $\sigma x - n_\sigma x \in M_i$ whenever $\sigma$ raises all $q$-th roots of unity to the power $n_\sigma$. Finally, for each layer and each prime $\ell \ne p$ there is a finite flat Hopf algebra $L_{i,\ell}$ of rank $q$ over the subring of $\mathbb Q$ of rationals with denominator coprime to $\ell$, a bijection of its convolution group of $\overline{\mathbb Q}$-points with $M_{i+1}/M_i$, and an algebra isomorphism with $\prod_{j<q} \mathbb Z_{(\ell)}$ in the `const` case, respectively with $\mathbb Z_{(\ell)}[X]/(X^q-1)$ in the `mult` case. The label `kind` carries no content beyond these four clauses, and the flag is a datum attached to the chosen presentation $C$, not an invariant of $J_0(p)$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Jordan–Hölder flag of finite flat group schemes or of fppf torsion sheaves; this is the project's own structure. It is expressed with Mathlib's `HopfAlgebra`, the convolution monoid `WithConv` on algebra maps out of a bialgebra, and sheaves on a Grothendieck topology, while the fppf site of $\operatorname{Spec}\mathbb Z$, the Hecke algebra and the Eisenstein maximal ideal are project notions.
--
--   **Where it is used.** The flag is the device for dévissage along $0 \to F_i \to F_{i+1} \to F_{i+1}/F_i \to 0$: the layers are of multiplicative or constant type of order $q$, so their fppf cohomology over $\operatorname{Spec}\mathbb Z$ is computable, and the resulting bounds on $H^1(\operatorname{Spec}\mathbb Z, \mathcal J_m)$ feed the Eisenstein-ideal analysis of the $q$-primary torsion of $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronPrimaryTorsionFlag.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite GaloisRep

set_option maxHeartbeats 1200000 in

structure JZeroNeronPrimaryTorsionFlag (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ) where
  n : ℕ

  G : Fin (n + 1) → Type
  [instCommRing_G : ∀ i, CommRing (G i)]
  [instHopfAlgebra_G : ∀ i, HopfAlgebra ℤ (G i)]
  [instFiniteType_G : ∀ i, Algebra.FiniteType ℤ (G i)]
  [instFlat_G : ∀ i, Module.Flat ℤ (G i)]
  π : ∀ i, C.H m →ₐ[ℤ] G i
  π_surj : ∀ i, Function.Surjective (π i)
  quot : ∀ i : Fin n, G i.succ →ₐ[ℤ] G i.castSucc
  quot_surj : ∀ i, Function.Surjective (quot i)
  quot_π : ∀ i : Fin n, (quot i).comp (π i.succ) = π i.castSucc

  F : Fin (n + 1) → Sheaf (smallFppfTopology specInt) Ab.{1}
  ι : ∀ i, F i ⟶ C.𝒥 m
  ι_mono : ∀ i, Mono (ι i)
  incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ
  incl_ι : ∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc

  F_sectionsEquiv : ∀ (i : Fin (n + 1)) (U : specInt.Fppf),
    (F i).1.obj (op U) ≃+ Additive (WithConv (G i →ₐ[ℤ] Γ(U.left, ⊤)))

  F_sectionsCompat : ∀ (i : Fin (n + 1)) (U : specInt.Fppf) (s : (F i).1.obj (op U)) (h : C.H m),
    WithConv.ofConv (Additive.toMul (C.sectionsEquiv m U ((ι i).1.app (op U) s))) h
      = WithConv.ofConv (Additive.toMul (F_sectionsEquiv i U s)) (π i h)

  G_zero_subsingleton : Subsingleton (G 0 →ₐ[ℤ] AlgebraicClosure ℚ)
  isIso_ι_last : IsIso (ι (Fin.last n))

  genericStep : Fin (n + 1) → AddSubgroup (JZero p)
  genericStep_le_tors : ∀ i, genericStep i ≤ eisensteinPrimaryTorsionBar p q m
  genericStep_mono : Monotone genericStep
  genericStep_bot : genericStep 0 = ⊥
  genericStep_top : genericStep (Fin.last n) = eisensteinPrimaryTorsionBar p q m
  genericStep_galois : ∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : JZero p), x ∈ genericStep i → σ • x ∈ genericStep i

  genericStep_pin : ∀ (i : Fin (n + 1)) (x : JZero p), x ∈ genericStep i ↔
    ∃ g : G i →ₐ[ℤ] AlgebraicClosure ℚ,
      (C.genericPoints m (WithConv.toConv (g.comp (π i))) : JZero p) = x

  kind : Fin n → JZeroFlagLayerKind

  layerAction_const : ∀ (i : Fin n), kind i = .const →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      x ∈ genericStep i.succ → σ • x - x ∈ genericStep i.castSucc

  layerAction_mult : ∀ (i : Fin n), kind i = .mult →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (x : JZero p), x ∈ genericStep i.succ → σ • x - nσ • x ∈ genericStep i.castSucc
  Lff : ∀ (_ : Fin n) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → Type
  [instCommRing_Lff : ∀ i ℓ hℓ hℓp, CommRing (Lff i ℓ hℓ hℓp)]
  [instHopfAlgebra_Lff : ∀ i ℓ hℓ hℓp, HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  [instFinite_Lff : ∀ i ℓ hℓ hℓp, Module.Finite (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  [instFlat_Lff : ∀ i ℓ hℓ hℓp, Module.Flat (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp)]
  Lff_rank : ∀ i ℓ hℓ hℓp, Module.finrank (GaloisRep.ratLocalizedAt ℓ) (Lff i ℓ hℓ hℓp) = q

  Lff_points : ∀ (i : Fin n) ℓ hℓ hℓp,
    WithConv (Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)
      ≃ (genericStep i.succ ⧸ (genericStep i.castSucc).addSubgroupOf (genericStep i.succ))

  layerIsoConst : ∀ (i : Fin n), kind i = .const → ∀ ℓ hℓ hℓp,
    Nonempty (Lff i ℓ hℓ hℓp ≃ₐ[GaloisRep.ratLocalizedAt ℓ] (Fin q → GaloisRep.ratLocalizedAt ℓ))

  layerIsoMult : ∀ (i : Fin n), kind i = .mult → ∀ ℓ hℓ hℓp,
    Nonempty (Lff i ℓ hℓ hℓp ≃ₐ[GaloisRep.ratLocalizedAt ℓ]
      (Polynomial (GaloisRep.ratLocalizedAt ℓ)
        ⧸ Ideal.span {(Polynomial.X : Polynomial (GaloisRep.ratLocalizedAt ℓ)) ^ q - 1}))

attribute [instance] JZeroNeronPrimaryTorsionFlag.instCommRing_G JZeroNeronPrimaryTorsionFlag.instHopfAlgebra_G
  JZeroNeronPrimaryTorsionFlag.instFiniteType_G JZeroNeronPrimaryTorsionFlag.instFlat_G
  JZeroNeronPrimaryTorsionFlag.instCommRing_Lff JZeroNeronPrimaryTorsionFlag.instHopfAlgebra_Lff
  JZeroNeronPrimaryTorsionFlag.instFinite_Lff JZeroNeronPrimaryTorsionFlag.instFlat_Lff

end ModularCurve


