-- Prove2me | Definitions.Def_GroupCohomology_GlobalBridge
-- name    : GroupCohomology_GlobalBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/abdeb000-860c-530a-99b0-173b6eba3d1d
-- title:
--   Degree-two global bridge predicate for level-constant cohomology
-- statement:
--   Fix a finite set $S$ of rational primes, a group $D$ together with a homomorphism $\pi\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to D$, two morphisms $f\colon R\to P$ and $g\colon P\to B$ of $\mathbb Z[D]$-representations, a further $\mathbb Z[D]$-representation $X$, a $\mathbb Z$-linear Galois representation $A$, an additive map $\iota\colon X\to A$, a prime $p$, a $\mathbb Z/p$-linear Galois representation $M$, and a biadditive pairing $\kappa\colon B\times M\to A$. For an additive map
--   $$\Lambda\colon H^1\bigl(D,\operatorname{Hom}_{\mathbb Z}(R,X)\bigr)\longrightarrow \mathrm{continuousH2S}\,S\,M,$$
--   the target being the quotient of the $S$-level-constant $2$-cocycles on $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ with values in $M$ by the coboundaries of $S$-level-constant $1$-cochains, the predicate `IsGlobalBridge₂` asserts the following for all data: whenever $a$ is a $1$-cocycle of $D$ with values in the internal hom $\operatorname{Hom}_{\mathbb Z}(R,X)$ (with its conjugation $D$-action), $\psi\colon D\to \operatorname{Hom}_{\mathbb Z}(P,A)$ is a family of additive maps with $\psi_d\circ f=\iota\circ a(d)$ for all $d$, the values $\psi_d(x)$ are all fixed by $\mathrm{Gal}(\overline{\mathbb Q}/F)$ for some intermediate field $F$ that is finite over $\mathbb Q$ and whose fixing subgroup contains the inertia group of every valuation subring of $\overline{\mathbb Q}$ lying over a prime outside $S$, and $m\colon \mathrm{Gal}\times\mathrm{Gal}\to M$ satisfies
--   $$\kappa\bigl(g(x),m(\gamma_1,\gamma_2)\bigr)=\bigl(d_{12}(\psi\circ\pi)\bigr)(\gamma_1,\gamma_2)(x)\qquad(x\in P),$$
--   where $d_{12}$ is the cochain differential for the conjugation action on $\operatorname{Hom}_{\mathbb Z}(P,A)$, and $m$ is moreover an $S$-level-constant $2$-cocycle, then $\Lambda$ sends the class of $a$ to the class of $m$.
--
--   Thus the predicate pins down $\Lambda$ on the cochain level against any such pair of compatible presentations; it asserts no existence of the lifts $\psi$ or of the cochain $m$, and is vacuous on classes admitting no such reading.
--
--   **Relation to Mathlib.** The ambient group cohomology (`cocycles₁`, `H1`, `H1π`, the differential `d₁₂`), the internal hom in `Rep` and restriction along a group homomorphism are Mathlib's; the level-constant (‘continuous’) cocycles and the quotient `continuousH2S`, the unramifiedness predicate on intermediate fields of $\overline{\mathbb Q}/\mathbb Q$, and the bridge predicate itself belong to the project.
--
--   **Where it is used.** The predicate supplies, as a hypothesis on a given map $\Lambda$, the cochain-level compatibility between a degree-one class over a finite Galois level and a degree-two level-constant class over the whole Galois group; it is the degree-two counterpart of the corresponding local bridge condition and is used in the modules treating global duality and the $H^2$ terms entering the Selmer-group estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_GlobalBridge.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

variable (S : Finset Nat.Primes)
  {D : Type} [Group D] (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D)
  {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep ℤ D} {A : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (ι : X →+ A)
  {p : ℕ} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (κ : B →+ M →+ A)

def IsGlobalBridge₂ (Λ : H1 ((ihom R).obj X) →+ continuousH2S S M) : Prop :=
  ∀ (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (_ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (_ : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup →
        ∀ (d : D) (x : P), A.ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (_ : ∀ (g₁ g₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : P), κ (g.hom x) (m (g₁, g₂)) =
      LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (g₁, g₂)) x)
    (hm : m ∈ levelCocyclesS₂ S M),
    Λ ((H1π ((ihom R).obj X)).hom a) = continuousH2Sπ S M ⟨m, hm⟩

end groupCohomology

end


