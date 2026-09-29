-- Prove2me | Definitions.Def_CerednikDrinfeld_QMModuliWitnessD
-- name    : CerednikDrinfeld_QMModuliWitnessD
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c8828f39-436c-54e3-b242-c21234171dc7
-- title:
--   Moduli witness for a Shimura curve over ℤ[1/D]
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $R_0\subseteq\mathbb{H}[\mathbb{Q},a,b]$, a real embedding $\iota$ of the quaternion algebra into $2\times 2$ real matrices, a family $\mathcal S$ of sets of ideles, and a `ShimuraCurveModel R₀ ι 𝒮` $M$ (a bundle of function fields $F/\mathbb{Q}$, $\bar F/\bar{\mathbb{Q}}$, $F_{\mathbb C}/\mathbb C$ with Galois action, uniformisation and Hecke correspondences). For a further submodule $\Lambda$ and naturals $N,q,q',D$, the structure `ShimuraCurveModel.ModuliWitnessD M Λ N q q' D` packages a coarse moduli interpretation of $M$ over $\mathbb{Z}[1/D]$, realised as $\mathrm{Spec}$ of `Localization.Away (D : ℤ)`. Its fields are: an integral scheme $X$ with a smooth proper morphism $\pi_X$ to the base; a geometric point $\bar s:\mathrm{Spec}\,\bar{\mathbb{Q}}\to\mathrm{Spec}\,\mathbb{Z}[1/D]$ whose composite with $\mathrm{Spec}$ of $\mathbb{Z}\to\mathbb{Z}[1/D]$ is the canonical $\mathbb{Z}$-structure of $\bar{\mathbb{Q}}$; a rule `pt` assigning to each commutative ring $S$, each $s:\mathrm{Spec}\,S\to\mathrm{Spec}\,\mathbb{Z}[1/D]$ and each `FakeEllipticCurve Λ N S` (an abelian scheme over $S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action satisfying the prescribed additivity, multiplicativity and tangent-trace laws, together with a finite flat level-$N$ subscheme of rank $N^2$) a point of $X$ over $s$; a ring isomorphism $e_F$ from $M.F$ onto the function field of $X$; and an equivalence `pts` between places of $M.\bar F$ over $\bar{\mathbb{Q}}$ and points of $X$ over $\bar s$. The remaining fields are the laws these data satisfy: `pt` is constant on isomorphism classes and compatible with pullback along ring maps; over algebraically closed fields it is surjective onto points and injective up to isomorphism; `pts` is equivariant for the Galois action $M.\mathrm{gal}$ and for $\mathrm{Spec}$ of field automorphisms; a place $P$ bounds $x\in M.F$ exactly when $e_F x$ lies in the image of the stalk at the image point of `pts P`; and for primes $\ell\nmid N$ the support of $M.\mathrm{corrBar}\,\ell$ applied to the divisor $P$ consists of those $Q$ whose fake elliptic curves are $\ell$-Hecke neighbours. The predicate `IsModuliModelD` asserts that such a witness exists. This repeats `ModuliWitness`/`IsModuliModel` with the base $\mathbb{Z}[1/(Nqq')]$ replaced by $\mathbb{Z}[1/D]$; the parameters $q,q'$ now only index the structure, and no divisibility relation between $Nqq'$ and $D$ is part of it.
--
--   **Relation to Mathlib.** Mathlib has no Shimura curves, quaternionic ("fake elliptic curve") moduli problems or Hecke correspondences on them; these notions are the project's own, formulated over Mathlib's schemes, its smooth and proper morphism classes, its function field of a scheme, and finite adele rings.
--
--   **Where it is used.** The witness is the moduli-theoretic input for the Čerednik–Drinfel'd description of a Shimura curve and of the Hecke action on its Jacobian, which feeds the torsion data used in the level-lowering step of the Frey–Serre–Ribet argument. Stating the witness over $\mathbb{Z}[1/D]$ rather than $\mathbb{Z}[1/(Nqq')]$ allows further primes, e.g. $2$, to be inverted in the base without re-establishing the rest of the structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMModuliWitnessD.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}

structure ShimuraCurveModel.ModuliWitnessD {R₀ : Submodule ℤ ℍ[ℚ, a, b]}
    {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) : Type 1 where

  X : Scheme.{0}

  [isIntegral : IsIntegral X]

  πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))

  smooth : Smooth πX

  proper : IsProper πX

  sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))

  sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

  pt : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
    FakeEllipticCurve Λ N S → SchemeHomOver s πX

  eF : M.F ≃+* ↥(X.functionField)

  pts : Place (AlgebraicClosure ℚ) M.Fbar ≃ SchemeHomOver sbar πX

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
    FakeEllipticCurve.Iso E E' → pt S s E = pt S s E'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
    FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1

  pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
    ∃ E : FakeEllipticCurve Λ N k, pt k s E = P

  pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
    (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E'

  pts_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) M.Fbar),
    (pts (M.gal σ • P)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts P).1

  pts_stalk : ∀ (P : Place (AlgebraicClosure ℚ) M.Fbar) (x : M.F),
    M.toBar x ∈ P.toValuationSubring ↔
      eF x ∈ (algebraMap ↥(X.presheaf.stalk ((pts P).1.base default)) ↥(X.functionField)).range

  hecke : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ∀ (P Q : Place (AlgebraicClosure ℚ) M.Fbar),
    Q ∈ (M.corrBar ℓ hℓ (Finsupp.single P 1)).support ↔
      ∃ E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
        pt _ sbar E = pts P ∧ pt _ sbar E' = pts Q ∧ FakeEllipticCurve.HeckeNeighbour ℓ E E'

def ShimuraCurveModel.IsModuliModelD {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) : Prop :=
  Nonempty (M.ModuliWitnessD Λ N q q' D)

end CerednikDrinfeld

end


