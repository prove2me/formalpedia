-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
-- name    : ModularCurve_JZeroNeronTorsionFlag
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/95e7055c-366c-5199-909a-0f94867d5caf
-- title:
--   Layered flags of the fppf Eisenstein torsion sheaf
-- statement:
--   Two declarations. `JZeroFlagLayerKind` is a two-element inductive type with constructors `const` and `mult`, used as a tag for the two admissible shapes of a layer. `JZeroNeronTorsionFlag p q A hA S m`, for primes $p,q$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, a torsion-sheaf datum $S$ of type `JZeroNeronTorsionSheaf p q A hA`, and $m\in\mathbb N$, is a structure carrying a filtration of the sheaf $S.\mathcal J\,m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with all the identifications of its layers as data. Its fields are: a length $n$; commutative rings $G_i$, $i\in\{0,\dots,n\}$, each a Hopf algebra over $\mathbb Z$, of finite type and flat as a $\mathbb Z$-module, presented as quotients $\pi_i$ of $S.H\,m$ by surjective $\mathbb Z$-algebra maps, with surjective transition maps $G_{i+1}\to G_i$ compatible with the $\pi_i$; sheaves $F_i$ of abelian groups with monomorphisms $\iota_i\colon F_i\to S.\mathcal J\,m$ and maps $F_i\to F_{i+1}$ whose composites with $\iota_{i+1}$ are the $\iota_i$; per-step representability isomorphisms identifying, for every fppf object $U$ over $\operatorname{Spec}\mathbb Z$, the sections $F_i(U)$ with the convolution group of $\mathbb Z$-algebra maps $G_i\to\Gamma(U,\mathcal O)$, compatibly with $S$'s own identification along $\pi_i$; the requirements that $G_0$ have at most one $\overline{\mathbb Q}$-point and that $\iota_{\mathrm{last}}$ be an isomorphism. On the generic fibre the flag carries a monotone chain `genericStep` of Galois-stable subgroups of `JZero p`, from $\bot$ to `eisensteinTorsionBar p q m` (the $(\mathfrak m_{p,q})^m$-torsion of $J_0(p)$ for the Hecke action), each term pinned to be exactly the set of points of $S.\mathtt{genericPoints}\,m$ arising from $\overline{\mathbb Q}$-points of $G_i$ composed with $\pi_i$. A tag `kind` on each layer is pinned to Galois behaviour: in the `const` case $\sigma\cdot x-x$ lies in the lower step for $x$ in the upper one; in the `mult` case $\sigma\cdot x-n_\sigma\cdot x$ does, whenever $\sigma$ raises $q$-th roots of unity to the power $n_\sigma$. Finally, for each layer $i$ and each prime $\ell\neq p$ there is a Hopf algebra $L_{i,\ell}$ over the subring $\mathbb Z_{(\ell)}\subset\mathbb Q$ of rationals with denominator coprime to $\ell$, finite and flat of rank $q$, with a bijection (a bare bijection, no additivity or equivariance being demanded) between its convolution set of $\overline{\mathbb Q}$-points and the quotient `genericStep i.succ / genericStep i.castSucc`, and an algebra isomorphism to $\mathbb Z_{(\ell)}^{q}$ in the `const` case and to $\mathbb Z_{(\ell)}[X]/(X^q-1)$ in the `mult` case; so each layer is the constant group scheme of order $q$ or $\mu_q$ over $\mathbb Z_{(\ell)}$, and each generic step has index $q$ in the next.
--
--   **Relation to Mathlib.** The Hopf-algebra and convolution apparatus (`HopfAlgebra`, `WithConv`, flatness and finiteness of modules) is Mathlib's; the fppf torsion-sheaf datum for $J_0(p)$ and the notion of a layered flag of it, with prescribed constant or multiplicative layers, are the project's own.
--
--   **Where it is used.** The structure supplies the geometric dévissage used in the analysis of the $\mathfrak m$-power Eisenstein torsion of $J_0(p)$: the filtration produces, on the generic fibre, a chain of Galois-stable subgroups with layers of order $q$ of constant or multiplicative type, which is what the fppf counting arguments for Mazur's study of the Eisenstein ideal consume. That analysis yields the irreducibility input for the mod-$p$ representation of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronTorsionFlag.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite GaloisRep

inductive JZeroFlagLayerKind
  | const
  | mult
  deriving DecidableEq

set_option maxHeartbeats 1200000 in

structure JZeroNeronTorsionFlag (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronTorsionSheaf p q A hA) (m : ℕ) where
  n : ℕ

  G : Fin (n + 1) → Type
  [instCommRing_G : ∀ i, CommRing (G i)]
  [instHopfAlgebra_G : ∀ i, HopfAlgebra ℤ (G i)]
  [instFiniteType_G : ∀ i, Algebra.FiniteType ℤ (G i)]
  [instFlat_G : ∀ i, Module.Flat ℤ (G i)]
  π : ∀ i, S.H m →ₐ[ℤ] G i
  π_surj : ∀ i, Function.Surjective (π i)
  quot : ∀ i : Fin n, G i.succ →ₐ[ℤ] G i.castSucc
  quot_surj : ∀ i, Function.Surjective (quot i)
  quot_π : ∀ i : Fin n, (quot i).comp (π i.succ) = π i.castSucc

  F : Fin (n + 1) → Sheaf (smallFppfTopology specInt) Ab.{1}
  ι : ∀ i, F i ⟶ S.𝒥 m
  ι_mono : ∀ i, Mono (ι i)
  incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ
  incl_ι : ∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc

  F_sectionsEquiv : ∀ (i : Fin (n + 1)) (U : specInt.Fppf),
    (F i).1.obj (op U) ≃+ Additive (WithConv (G i →ₐ[ℤ] Γ(U.left, ⊤)))

  F_sectionsCompat : ∀ (i : Fin (n + 1)) (U : specInt.Fppf) (s : (F i).1.obj (op U)) (h : S.H m),
    WithConv.ofConv (Additive.toMul (S.sectionsEquiv m U ((ι i).1.app (op U) s))) h
      = WithConv.ofConv (Additive.toMul (F_sectionsEquiv i U s)) (π i h)

  G_zero_subsingleton : Subsingleton (G 0 →ₐ[ℤ] AlgebraicClosure ℚ)
  isIso_ι_last : IsIso (ι (Fin.last n))

  genericStep : Fin (n + 1) → AddSubgroup (JZero p)
  genericStep_le_tors : ∀ i, genericStep i ≤ eisensteinTorsionBar p q m
  genericStep_mono : Monotone genericStep
  genericStep_bot : genericStep 0 = ⊥
  genericStep_top : genericStep (Fin.last n) = eisensteinTorsionBar p q m
  genericStep_galois : ∀ (i : Fin (n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : JZero p), x ∈ genericStep i → σ • x ∈ genericStep i

  genericStep_pin : ∀ (i : Fin (n + 1)) (x : JZero p), x ∈ genericStep i ↔
    ∃ g : G i →ₐ[ℤ] AlgebraicClosure ℚ,
      (S.genericPoints m (WithConv.toConv (g.comp (π i))) : JZero p) = x

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

attribute [instance] JZeroNeronTorsionFlag.instCommRing_G JZeroNeronTorsionFlag.instHopfAlgebra_G
  JZeroNeronTorsionFlag.instFiniteType_G JZeroNeronTorsionFlag.instFlat_G
  JZeroNeronTorsionFlag.instCommRing_Lff JZeroNeronTorsionFlag.instHopfAlgebra_Lff
  JZeroNeronTorsionFlag.instFinite_Lff JZeroNeronTorsionFlag.instFlat_Lff

end ModularCurve


