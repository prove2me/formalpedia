-- Prove2me | Definitions.Def_GroupCohomology_LocalInvariant
-- name    : GroupCohomology_LocalInvariant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/fc35bdbb-2e0b-59e9-8a7f-6373770d189e
-- title:
--   Local invariant functional on continuous H2 of Fp​(χp​)
-- statement:
--   Fix a prime $p$, an element $\zeta$ of $\overline{\mathbb{Q}}$ and a prime $q$, and write $G_q = \overline{\mathbb{Q}}_q \simeq_{\mathbb{Q}_q} \overline{\mathbb{Q}}_q$ for the local Galois group, `primeLocalToGlobal q` for its map to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting along the fixed embedding [`padicEmbedding q`](../def/GaloisRep_CompletionBridge.html#L17), and $M =$ `ofChar ((cycloChar p).comp (primeLocalToGlobal q))` for the one-dimensional $\mathbb{Z}/p$-representation of $G_q$ on which $G_q$ acts through the mod $p$ cyclotomic character. The carrier is the project's `continuousH2`: level-constant inhomogeneous $2$-cocycles (those invariant under right translation of both arguments by elements whose global image fixes some finite extension of $\mathbb{Q}$) modulo coboundaries of level-constant $1$-cochains.
--
--   `IsLocalInv p ζ q f` is a predicate on a $\mathbb{Z}/p$-linear functional $f$ on this space. It asserts: for every unit $u$ of $\overline{\mathbb{Q}}_q$ whose underlying element is the image of $\zeta$; every $\mathbb{Q}_q$-automorphism $\varphi$ of $L = \mathbb{Q}_q\big(\{x : x^{q^p-1}=1\}\big)$ which generates the whole automorphism group, has finite order, and satisfies $\varphi(x) = x^q$ on the $(q^p-1)$-st roots of unity; every unit $\pi$ of $L$ whose underlying element is $q$; with $L$ assumed normal over $\mathbb{Q}_q$; and every level-constant $2$-cocycle $z$ with values in $\mathbb{Z}/p$ — if the cochain $g \mapsto u^{(z\,g).\mathrm{val}}$, written additively in $\overline{\mathbb{Q}}_q^\times$, differs from the inflation along `unitsInflate₂` of the carry cochain `carryFun φ … π` (value $\pi$ when the sum of the discrete logarithms of the two arguments to base $\varphi$ is at least $\mathrm{ord}(\varphi)$, and $0$ otherwise) by a level coboundary in the representation of $G_q$ on the units of $\overline{\mathbb{Q}}_q$, then $f$ of the class of $z$ equals $1$.
--
--   `localInv p ζ q` is the functional so characterised when such an $f$ exists and is unique, and $0$ otherwise; the definition itself asserts neither existence nor uniqueness.
--
--   **Relation to Mathlib.** Mathlib has no invariant map of local class field theory; this is the project's own formulation, and it is not an isomorphism but a linear functional pinned down by a normalisation condition on a chosen cocycle presentation, built on the project's level-constant $H^2$, units inflation and cyclic carry cochain.
--
--   **Where it is used.** The functional is the normalised local invariant at $q$ on the $\mathbb{F}_p(\chi_p)$-valued continuous $H^2$, normalised so that the class of the unramified degree-$p$ carry cocycle with uniformiser $q$ takes the value $1$; the same global $\zeta$ is used at every place. It serves to state the sum-of-local-invariants reciprocity law and the local orthogonality conditions used in the Selmer-group estimates of the extension-class argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LocalInvariant.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
noncomputable section
open CategoryTheory ExtCitation groupCohomology

namespace groupCohomology

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

def IsLocalInv
    (f : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p) : Prop :=
  ∀ (u : (PadicAlgCl q)ˣ), (u : PadicAlgCl q) = padicEmbedding q ζ →
  ∀ (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ),
    (∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ)) →
  ∀ (π : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ), ((π : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = ((q : ℕ) : PadicAlgCl q) →
  ∀ (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))),
    ((fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
      - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
          (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul π))
      ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) →
    f (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩) = 1

open Classical in

def localInv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p :=
  if h : ∃ f, IsLocalInv p ζ q f ∧ ∀ f', IsLocalInv p ζ q f' → f' = f then Classical.choose h else 0

end groupCohomology

end


