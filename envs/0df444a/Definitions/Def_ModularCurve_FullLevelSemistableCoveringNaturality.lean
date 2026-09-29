-- Prove2me | Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
-- name    : ModularCurve_FullLevelSemistableCoveringNaturality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a94b06d2-70bc-58c4-89b4-2a13760fe5ee
-- title:
--   Naturality clauses for full-level semistable coverings
-- statement:
--   Fix a prime $q$, a level $M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with residue field $\kappa_A$, and a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa_A\,M'$. For a semistable covering $\mathcal{C}$ of `fieldBar q M'` over $A$ — a structure consisting of component charts $\mathcal{C}.\mathrm{CIg}\,\ell$ indexed by $\ell$ in the projectivisation of $(\mathbb{Z}/q)^2$ with reduced fields $\mathcal{C}.\mathrm{FIg}\,\ell$, component charts $\mathcal{C}.\mathrm{CSS}\,s$ with reduced fields $\mathcal{C}.\mathrm{FSS}\,s$ for $s\in W$, annuli $\mathcal{C}.\mathrm{An}$, $\mathcal{C}.\mathrm{An}'$ joining them, and the attachment, partition and rationality axioms — the predicate `NaturalityClauses` is the conjunction of four assertions.
--
--   First: for every $\tau$ in the inertia subgroup of $A$ over $\mathbb{Q}$, with $g$ the semilinear automorphism of `fieldBar q M'` that applies $\tau$ to the Laurent coefficients of $q$-expansions (semilinear over $\tau$ on constants), and for every $s\in W$: the valuation subring $(\mathcal{C}.\mathrm{CSS}\,s).\mathrm{integers}$ and the domain $(\mathcal{C}.\mathrm{CSS}\,s).\mathrm{dom}$ are $g$-stable, and there is a $\kappa_A$-algebra automorphism $\varphi$ of $\mathcal{C}.\mathrm{FSS}\,s$ with `InducesOnChart`, i.e. reduction intertwines $g$ with $\varphi$, and $\mathrm{placeMap}(g\cdot P)=\varphi\cdot\mathrm{placeMap}(P)$ for $P$ in the domain. Second: the same conclusions, for each index $\zeta$ and each $\gamma\in\Gamma_0(M')\subseteq\mathrm{SL}_2(\mathbb{Z})$, with $g$ the semilinear automorphism attached to the level automorphism `levelAutBar q M' ζ γ⁻¹`. Third: for such $\gamma$ whose reduction `redQ q γ` is of unipotent cuspidal type, the domain of the Igusa chart at $\ell=[1:0]$ is stable, the induced map on its reduced field is the identity, and $\mathrm{placeMap}$ is invariant there. Fourth: there is one index $\zeta_0$ such that for all $\gamma\in\Gamma_0(M')$ and all $\ell$, the pullback of $\mathcal{C}.\mathrm{CIg}\,\ell$ along that level automorphism has the same integers and domain as $\mathcal{C}.\mathrm{CIg}((\mathrm{redQ}\,q\,\gamma)^{-1}\cdot\ell)$, and likewise the pulled-back annulus domains match those of $(\mathrm{redQ}\,q\,\gamma)^{-1}\cdot\ell$.
--
--   Thus the predicate records, for a chosen presentation of the semistable reduction by charts and annuli, that the charts are permuted by the level automorphisms according to the action on the projective line and that inertia and the level automorphisms act through automorphisms of the reduced function fields compatibly with the specialisation of places.
--
--   **Relation to Mathlib.** Mathlib has no notion of component charts, annuli or semistable coverings of a function field over a valuation subring; these, and the predicate `InducesOnChart` relating a semilinear automorphism of the big field to a ring automorphism of a reduced field, are the project's own.
--
--   **Where it is used.** The clauses are asserted of the semistable covering of the full-level modular function field produced elsewhere in the development, and they supply the equivariance needed to compute the action of inertia and of the $\Gamma_0(M')$-level automorphisms on the components and the component group of the reduction, hence on the specialisation of the Jacobian that enters the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelSemistableCoveringNaturality.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing DrinfeldCurve CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def NaturalityClauses (𝒞 : SemistableCovering q M' A W) : Prop :=

  (∀ τ ∈ A.inertiaSubgroupIn ℚ,
    let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
    ∀ s, (∀ f : fieldBar q M', f ∈ (𝒞.CSS s).integers ↔ g • f ∈ (𝒞.CSS s).integers) ∧
      (∀ P, P ∈ (𝒞.CSS s).dom ↔ g • P ∈ (𝒞.CSS s).dom) ∧
      ∃ φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s, InducesOnChart (𝒞.CSS s) g φ.toRingEquiv ∧
        ∀ P ∈ (𝒞.CSS s).dom, (𝒞.CSS s).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (𝒞.CSS s).placeMap P) ∧

  (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ s,
    let g := SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)
    ∃ φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s, InducesOnChart (𝒞.CSS s) g φ.toRingEquiv ∧
      ∀ P ∈ (𝒞.CSS s).dom, (𝒞.CSS s).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (𝒞.CSS s).placeMap P) ∧

  (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
    let g := SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)
    (∀ P, P ∈ (𝒞.CIg (lineInfty q)).dom ↔ g • P ∈ (𝒞.CIg (lineInfty q)).dom) ∧
    InducesOnChart (𝒞.CIg (lineInfty q)) g (RingEquiv.refl _) ∧
    (∀ P ∈ (𝒞.CIg (lineInfty q)).dom, (𝒞.CIg (lineInfty q)).placeMap (g • P) = (𝒞.CIg (lineInfty q)).placeMap P)) ∧

  (∃ ζ₀ : Idx q, ∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ ℓ,
    ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ₀ γ⁻¹)).integers = (𝒞.CIg ((redQ q γ)⁻¹ • ℓ)).integers ∧
    ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ₀ γ⁻¹)).dom = (𝒞.CIg ((redQ q γ)⁻¹ • ℓ)).dom ∧
    ∀ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ₀ γ⁻¹)).dom = (𝒞.An ((redQ q γ)⁻¹ • ℓ) s).dom)

end SemistableCovering

end ModularCurve.FullLevel

end


