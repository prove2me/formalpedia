-- Prove2me | Definitions.Def_ExtCitation_AdmissibleExtension_v2
-- name    : ExtCitation_AdmissibleExtension_v2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/50a46b41-ff2a-5f3b-9147-6194c68e6b58
-- title:
--   Continuous admissible extensions of μp​ by Z/p
-- statement:
--   Throughout, $p$ is a prime, $V$ is a $\mathbb{Z}/p$-vector space carrying a distributive multiplicative action of $G_{\mathbb{Q}} = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (realised as `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`) commuting with scalars, and $C \subseteq V$ is a $\mathbb{Z}/p$-submodule. The structure `IsAdmissibleExtensionCts p V C` extends the project's `IsAdmissibleExtension p V C` by a single extra field `open_kernel`, asserting that the pointwise stabiliser $\{\sigma \in G_{\mathbb{Q}} \mid \sigma \cdot v = v \text{ for all } v \in V\}$ is open for the Krull topology; equivalently, the action factors through a finite Galois quotient. The inherited fields say: $C$ is $G_{\mathbb{Q}}$-stable, $G_{\mathbb{Q}}$ acts trivially on $C$ (so the stability field is subsumed), for every $\sigma$ and every $x \in V$ one has $\sigma\cdot x - \bar\chi(\sigma)\,x \in C$, where $\bar\chi(\sigma) \in \mathbb{Z}/p$ is the value of the mod $p$ cyclotomic character (`cycloExp`, built from Mathlib's `modularCyclotomicCharacter`) — i.e. $V/C \cong \mu_p$, stated as a congruence rather than an isomorphism; $\#C = p$ and $\#V = p^2$; for every prime $\ell \neq p$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, every element of the image of the inertia subgroup of $A$ over $\mathbb{Q}$ acts trivially on all of $V$ (unramified outside $p$); and for every such $A$ lying over $p$ there is a submodule $C'$ stable under the decomposition subgroup of $A$ with $C \oplus C' = V$ (locally split at $p$).
--
--   `ExtVanishingCts p` asserts that for every such $V$ and $C$ satisfying `IsAdmissibleExtensionCts`, the conclusion `SplitsGlobally C` holds: there is a $G_{\mathbb{Q}}$-stable complement $C'$ to $C$ in $V$. `ExtVanishingCtsAll` quantifies this over all primes $p \ge 3$. Finally `extVanishingCts_of_extVanishing` records the immediate implication `ExtVanishing p → ExtVanishingCts p`, obtained by forgetting the openness field; the continuous version is thus the weaker hypothesis, and every consequence of the non-continuous one remains available.
--
--   **Relation to Mathlib.** Mathlib has no notion of admissible extension of $\mu_p$ by $\mathbb{Z}/p$, nor of the corresponding $\mathrm{Ext}$-vanishing statement; these are the project's own. The topology on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ used in `open_kernel` is Mathlib's Krull topology instance, and the mod $p$ cyclotomic character underlying `cycloExp` is Mathlib's `modularCyclotomicCharacter`.
--
--   **Where it is used.** These predicates package, in a form citable inside the formalisation, the vanishing of $\mathrm{Ext}^1_{\mathrm{Spec}\,\mathbb{Z}}(\mu_p, \mathbb{Z}/p)$: a two-dimensional mod $p$ Galois module with a trivial sub, cyclotomic quotient, unramified outside $p$ and split at $p$, must split globally. It is used in the step ruling out reducibility of the mod $p$ representation attached to the $p$-torsion of a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_AdmissibleExtension_v2.lean

import Mathlib
import Definitions.Def_ExtCitation_AdmissibleExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]
variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtensionCts (C : Submodule (ZMod p) V) : Prop
    extends IsAdmissibleExtension p V C where

  open_kernel : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | ∀ v : V, σ • v = v}

def ExtVanishingCts : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtensionCts p V C → SplitsGlobally C

def ExtVanishingCtsAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishingCts p ⟨hp⟩

variable {p V} in

theorem extVanishingCts_of_extVanishing (h : ExtVanishing p) : ExtVanishingCts p :=
  fun V _ _ _ _ C hadm => h V C hadm.toIsAdmissibleExtension

end ExtCitation


