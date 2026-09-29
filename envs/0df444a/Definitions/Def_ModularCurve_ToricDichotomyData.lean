-- Prove2me | Definitions.Def_ModularCurve_ToricDichotomyData
-- name    : ModularCurve_ToricDichotomyData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/0fc442e8-58be-5409-845e-ea1fd0e17b0c
-- title:
--   Guarded toric dichotomy data for Hecke modules
-- statement:
--   Throughout, $G$ is a group, $J$ an abelian group carrying a module structure over the project's Hecke ring `HeckeAlg` (a polynomial ring with generators `heckeGen ℓ` indexed by the primes, integer constants being written `C`) and a distributive $G$-action, $J_0$ a second `HeckeAlg`-module, $S$ a finite set of primes, $I \le G$, $\varphi \in G$ and $q$ a prime; the two actions on $J$ are not assumed to commute. The first definition, `IsToricDichotomyQGuarded q S I 𝒯 J₀`, is a predicate on a `HeckeAlg`-submodule $\mathcal T \subseteq J$: for every maximal ideal $\mathfrak m \subset$ `HeckeAlg` that is not eventually Eisenstein (i.e. for which no cofinite set of primes $\ell$ has $T_\ell - (\ell+1) \in \mathfrak m$) and whose residue field receives $q$ as a unit, and for every $x$ in the project's $\mathfrak m$-torsion `heckeTorsion J 𝔪` fixed by all $\sigma \in I$, either $x \in \mathcal T$, or `HasLowerLevelTorsion S 𝔪 J₀` holds, i.e. there is a nonzero $y \in J_0$ killed by every natural number lying in $\mathfrak m$ and by every $T_\ell - b$ ($\ell \notin S$, $b \in \mathbb Z$) that lies in $\mathfrak m$. Note that the second alternative is a statement about $J_0$ alone, independent of $x$ and of $\mathfrak m$-freeness of $x$.
--
--   The second definition, `ExistsToricDichotomyDataQGuarded J q S I φ J₀`, asserts the existence of a `HeckeAlg`-submodule $\mathcal T \subseteq J$ satisfying three conditions: `ToricFrobeniusSq`, that $\varphi$ acts on $\mathcal T$ with $\varphi^2 x = q^2 x$; the guarded dichotomy above towards $J_0$; and `ToricFrobeniusHecke`, that $\varphi x = (q\,T_q)\,x$ for $x \in \mathcal T$. The remaining declarations are accessors: `toric` extracts a witness submodule via choice, and `toricFrobeniusSq`, `toricDichotomy`, `toricFrobeniusHecke` record its three defining properties.
--
--   **Relation to Mathlib.** Mathlib has no notion of Hecke-module toric part, Eisenstein maximal ideal or level-raising dichotomy; these are the project's own definitions, stated for an arbitrary module over the project's ring `HeckeAlg` with a compatible group action.
--
--   **Where it is used.** These predicates package what is needed from the Deligne–Rapoport description of the special fibre of $J_0(Nq)$ at $q$ in the form used by Mazur's principle: in the intended application $J$ is the Jacobian of $X_0(Nq)$ over $\overline{\mathbb Q}$, $J_0$ that of $X_0(N)$, $I$ an inertia group at a place above $q$ and $\varphi$ a corresponding Frobenius, and the dichotomy says that an unramified non-Eisenstein $\mathfrak m$-torsion point is toric unless $\mathfrak m$-torsion already exists at level $N$. They are consumed by the Mazur-principle core and by the Frey-package descent apparatus used for level lowering at a prime $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ToricDichotomyData.lean

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Dichotomy

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]

def IsToricDichotomyQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (J₀ : Type*) [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → x ∈ 𝒯 ∨ HasLowerLevelTorsion S 𝔪 J₀

end Dichotomy

section Bundle

def ExistsToricDichotomyDataQGuarded {G : Type*} [Group G]
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
    (q : Nat.Primes) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (J₀ : Type*) [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J,
    ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧ IsToricDichotomyQGuarded (q : ℕ) S I 𝒯 J₀ ∧
    ToricFrobeniusHecke q φ 𝒯

namespace ExistsToricDichotomyDataQGuarded

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

def toric (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    ToricFrobeniusSq (q : ℕ) φ h.toric :=
  h.choose_spec.1

theorem toricDichotomy (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    IsToricDichotomyQGuarded (q : ℕ) S I h.toric J₀ :=
  h.choose_spec.2.1

theorem toricFrobeniusHecke (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    ToricFrobeniusHecke q φ h.toric :=
  h.choose_spec.2.2

end ExistsToricDichotomyDataQGuarded

end Bundle

end ModularCurve

end


