-- Prove2me | Definitions.Def_ModularCurve_AtPPackage
-- name    : ModularCurve_AtPPackage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/4cc90560-1355-5d8d-bba3-e91adb147b74
-- title:
--   Predicates for the at-p filtration, Eisenstein annihilation, support descent
-- statement:
--   Three predicates are introduced, all phrased over the project's Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ whose generator `heckeGen ℓ` stands for $T_\ell$.
--
--   First, for a group $G$ acting distributively on a module $J$ over a commutative ring $R$, a subgroup $I \le G$, a character $\chi : G \to R^\times$ and an $R$-submodule $W \le J$, `IsAtPFiltration` is the conjunction of four clauses: $W \neq J$; $W$ is stable under every element of $G$ (`ToricStable`); $\sigma \cdot x = \chi(\sigma)\, x$ for all $\sigma \in I$ and $x \in W$ (`MultiplicativeType`); and $\sigma \cdot x - x \in W$ for all $\sigma \in I$ and all $x \in J$ (`InertiaUnipotentTowards`). It differs from `IsInertiaFiltration` exactly in replacing "inertia fixes $W$ pointwise" by "inertia acts on $W$ through $\chi$"; $\chi$ is an arbitrary parameter, not pinned to the mod $p$ cyclotomic character, and no commutation between the $G$- and $R$-actions is assumed.
--
--   Second, for a finite set $S$ of primes and a `HeckeAlg`-module $\Phi$, `EisensteinAnnihilates` says that $X_\ell - (\ell+1)$ annihilates every element of $\Phi$, for every prime $\ell \notin S$.
--
--   Third, `AtPSupportDescends` takes $N_0 \neq 0$, a finite set $S$, an unspecified predicate `fin` on ideals of `HeckeAlg`, and a `HeckeAlg`-module $W^{\mathrm{et}}$, and asserts: for every maximal ideal $\mathfrak{m}$ of `HeckeAlg` which is non-Eisenstein in the explicit sense that $X_\ell - (\ell+1) \notin \mathfrak{m}$ for some prime $\ell \notin S$, which satisfies `fin`, and whose torsion submodule $\{x \in W^{\mathrm{et}} : \mathfrak{m}x = 0\}$ is non-zero, one has `IsEigenformIdeal N₀ 𝔪`: $\mathfrak{m}$ is the kernel of the evaluation $X_\ell \mapsto \varphi(a_\ell(f))$ for some normalised eigenform $f$ of weight $2$ on $\Gamma_0(N_0)$, a subring $\mathcal{O} \subseteq \mathbb{C}$ containing its prime-indexed $q$-coefficients, and a homomorphism $\varphi$ from $\mathcal{O}$ to a finite field.
--
--   **Relation to Mathlib.** Mathlib has no abstract Hecke algebra, component group or integral-model filtration notions; `HeckeAlg` is simply a free commutative polynomial $\mathbb{Z}$-algebra on the primes, and the predicates here are the project's own. The $\mathfrak{m}$-torsion used in `AtPSupportDescends` is Mathlib's `Submodule.torsionBySet`, and `CuspForm`, `CongruenceSubgroup.Gamma0` and the $q$-expansion coefficients underlying `IsEigenformIdeal` come from Mathlib.
--
--   **Where it is used.** These predicates axiomatise the semistable-reduction input at the prime $p$ equal to the residue characteristic: the multiplicative-type filtration on the $p$-torsion of the relevant Jacobian quotient, the vanishing of Eisenstein elements on the component group, and the conclusion that non-Eisenstein maximal ideals supported on the étale quotient come from weight-$2$ eigenforms of the lowered level. They are the hypotheses consumed by the level-lowering step that passes from the mod $p$ representation attached to the Frey curve to a form of level $N_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AtPPackage.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_DeligneRapoport
import Definitions.Def_ModularCurve_EigenformIdeal
import Definitions.Def_ModularCurve_MultiplicativeType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section FiltrationPredicates

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def IsAtPFiltration (I : Subgroup G) (χ : G →* Rˣ) (W : Submodule R J) : Prop :=
  W ≠ ⊤ ∧ ToricStable G W ∧ MultiplicativeType I χ W ∧ InertiaUnipotentTowards I W

end FiltrationPredicates

section EisensteinComponentGroup

variable (S : Finset Nat.Primes) (Φ : Type*) [AddCommGroup Φ] [Module HeckeAlg Φ]

def EisensteinAnnihilates : Prop :=
  ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ x : Φ,
    (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0

end EisensteinComponentGroup

section SupportDescends

variable (N₀ : ℕ) [NeZero N₀]

def AtPSupportDescends (S : Finset Nat.Primes) (fin : Ideal HeckeAlg → Prop)
    (Wet : Type*) [AddCommGroup Wet] [Module HeckeAlg Wet] : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal →
    (∃ ℓ : Nat.Primes, ℓ ∉ S ∧ heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) →
    fin 𝔪 →
    heckeTorsion Wet 𝔪 ≠ ⊥ →
    IsEigenformIdeal N₀ 𝔪

end SupportDescends

end ModularCurve

end


