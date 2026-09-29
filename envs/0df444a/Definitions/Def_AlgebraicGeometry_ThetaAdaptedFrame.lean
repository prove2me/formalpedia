-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
-- name    : AlgebraicGeometry_ThetaAdaptedFrame
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d4388ae2-05a3-5799-9fa2-bbb063a57aff
-- title:
--   Theta-adapted frames; étale-local theta type for polarised abelian schemes
-- statement:
--   Fix $g, N, n$, moduli $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with each $\delta_i \neq 0$, and write $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. The first definition, `FramedPolarisedAbelianScheme.IsThetaAdapted`, takes a bijection $e : \mathrm{Fin}(N+1) \simeq H(\delta)$ and a framed polarised abelian scheme $X$ over a commutative ring $S$ — so $X$ carries $f : A \to \operatorname{Spec} S$ with relative group law, the $2g$ torsion points of level $n$, an invertible sheaf $X.\mathrm{pol}$ of geometric fibre degree $N+1$, and a frame consisting of $N+1$ global sections of $X.\mathrm{pol}$ forming a basis over $S$ and defining a closed immersion into projective $N$-space. It asserts the existence of a `Polarisation.SchrodingerFrame` for $f$, the group law and $X.\mathrm{pol}$, taken with test morphism the identity of $\operatorname{Spec} S$ and moduli $\delta$, whose basis sections agree with the frame after re-indexing by $e$: for every $i$, the frame section $\sigma_{e(i)}$ of the Schrödinger frame equals the pullback of the $i$-th framing section along the first projection $A \times_S \operatorname{Spec} S \to A$. A Schrödinger frame is itself a structure: sections $\sigma_h$ indexed by $H(\delta)$ whose $S$-linear combinations exhaust the global sections bijectively, together with theta points $\mathrm{lift}(h)$ and $\mathrm{dualLift}(\chi)$ (each a point of $A$ with an isomorphism between the pullback of the sheaf along translation by that point and the sheaf itself), and, as fields of the structure, the equations $U_{\mathrm{lift}(h)}\sigma_{h'} = \sigma_{h+h'}$ and $U_{\mathrm{dualLift}(\chi)}\sigma_h = \chi(h)\,\sigma_h$ for additive characters $\chi$ of $H(\delta)$ valued in $S$.
--
--   The second definition, `PolarisedAbelianScheme.ThetaTypeLocally δ`, is a predicate of the shape $\forall S, \ \text{PolarisedAbelianScheme}\ g\,(N+1)\,n\,S \to \mathrm{Prop}$, hence usable as the property parameter of the project's `Satisfying` and fine-moduli notions. It holds for $u$ over $S$ when: for every commutative $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1 - \zeta^j$ a unit for $0 < j < N+1$, there is an $R$-algebra $R'$ that is faithfully flat as an $R$-module and étale over $R$, a framed polarised abelian scheme $X'$ over $R'$ and a bijection $e : \mathrm{Fin}(N+1) \simeq H(\delta)$, such that $X'$ underlies the base change of $u$ along $S \to R \to R'$ in the sense of `PolarisedAbelianScheme.IsPullback` and $X'$ is theta-adapted for $\delta$ and $e$. The element $\zeta$ occurs only in the hypothesis: its existence over $R$ is the condition under which a theta-adapted framing over an étale faithfully flat cover is demanded.
--
--   **Relation to Mathlib.** Mathlib has no abelian schemes, polarisations or theta structures; these are the project's own notions, built on Mathlib's sheaves of modules on schemes (via the project's `Scheme.Modules` and `Scheme.Modules.pullbackLocalSection`), `Module.FaithfullyFlat` and `Algebra.Etale`.
--
--   **Where it is used.** These predicates formulate the moduli problem on the theta-structure route: `ThetaTypeLocally δ` is the property, attachable to the project's `Satisfying` and fine-moduli definitions, of admitting a theta-adapted framing étale-locally, and it is implied by the symmetric, principally rooted objects of type $\delta$ recorded as `RootedSymmetricOfType`. The resulting moduli schemes are what the quaternionic (Čerednik–Drinfeld) part of the argument cuts its own locus out of.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaAdaptedFrame.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace FramedPolarisedAbelianScheme

variable {g N n : ℕ}

def IsThetaAdapted (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type u} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) : Prop :=
  ∃ F : Polarisation.SchrodingerFrame X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) δ,
    ∀ i : Fin (N + 1),
      F.σ (e i) =
        (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
          Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
            (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))

end FramedPolarisedAbelianScheme

namespace PolarisedAbelianScheme

variable {g N n : ℕ}

def ThetaTypeLocally (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] :
    ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g (N + 1) n S → Prop :=
  fun S _ u =>
    ∀ (R : Type u) [CommRing R] [Algebra S R] (ζ : R),
      ζ ^ (N + 1) = 1 → (∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) →
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
        Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
        ∃ (X' : FramedPolarisedAbelianScheme g N n R') (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i))),
          PolarisedAbelianScheme.IsPullback ((algebraMap R R').comp (algebraMap S R)) u X'.toPolarisedAbelianScheme ∧
          X'.IsThetaAdapted δ e

end PolarisedAbelianScheme

end AlgebraicGeometry

end


