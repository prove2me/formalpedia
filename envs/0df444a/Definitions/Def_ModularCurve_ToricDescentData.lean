-- Prove2me | Definitions.Def_ModularCurve_ToricDescentData
-- name    : ModularCurve_ToricDescentData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/5f964431-3f5b-5863-b10d-2d22241b3334
-- title:
--   Toric descent data and degeneracy pushforwards at level Nq
-- statement:
--   The first half works in a generic setting: a group $G$, a module $J$ over the project's Hecke algebra `HeckeAlg` (with generators `heckeGen ℓ`, one for each rational prime) carrying a compatible $G$-action, a second `HeckeAlg`-module $J_0$, and two additive maps $\delta_0,\delta_1 : J \to J_0$ indexed by `Fin 2`. `IsAbelianPartDataQGuarded q S I 𝒯 δ` is a structure on a `HeckeAlg`-submodule $\mathcal T \subseteq J$ with three fields: $\delta_i$ kills $\mathcal T$ for $i=0,1$; for every prime $\ell \notin S$ one has $\delta_i(T_\ell x) = T_\ell \delta_i(x)$ for all $x$; and, for every maximal ideal $\mathfrak m \subset$ `HeckeAlg` which is not eventually Eisenstein (i.e. there is no finite set $S'$ with $T_\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S'$) and in whose residue ring the class of $q$ is a unit, every element of the $\mathfrak m$-torsion `heckeTorsion J 𝔪` that is fixed by all $\sigma \in I$ and killed by both $\delta_i$ already lies in $\mathcal T$. This is the project's unguarded `IsAbelianPartData` with the extra unit guard on $q$ in the third clause, whence the forgetful map `IsAbelianPartData.qGuarded`. `ToricFrobeniusHecke q φ 𝒯` says $\varphi\cdot x = (q\,T_q)\cdot x$ for $x \in \mathcal T$. Three existential bundles package a submodule $\mathcal T$ with `ToricFrobeniusSq q φ 𝒯` (i.e. $\varphi^2 x = q^2 x$ on $\mathcal T$) together with the unguarded data, the guarded data, or the guarded data plus the Frobenius–Hecke clause; each comes with choice-based extractors `.toric` and accessors, and the implications unguarded $\Rightarrow$ guarded and full $\Rightarrow$ guarded.
--
--   The second half fixes the two degeneracy maps at level $Nq$. `DegeneracyPushforwardInputs N q` asserts the conjunction, phrased as an existential over the data, of: integrality of the two algebra maps `heckeAlphaBar` (the inclusion of the base-changed full modular function field of level $N$ into that of level $Nq$) and `heckeBetaBar` (the substitution $q$-expansion map), module-finiteness along each, and the pushforward norm formula along each. `degeneracyPushforwardPair N q : Fin 2 → (JZero (N*q) →+ JZero N)` is a total term, defined by a case split: on those inputs it is the pair of divisor-class pushforwards `Pic0.pushforwardAlongHom` along `heckeAlphaBar` and `heckeBetaBar`, and $0$ otherwise; the accompanying lemmas identify it at any given witnesses and record the junk value.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebra acting on modular Jacobians and no notion of toric or abelian part of a degenerate fibre; these are the project's own. The divisor-theoretic input (places, divisors, $\mathrm{Pic}^0$ of a function field presented as a subfield of a Laurent series field, and pushforward along an integral algebra map) is likewise built in the project on top of Mathlib's valuation subrings and Dedekind-domain machinery.
--
--   **Where it is used.** These predicates are the vocabulary in which the geometric input to Mazur's principle at the auxiliary prime $q$ is stated: Frobenius acting as $q T_q$ (and so with square $q^2$) on the toric part of $J_0(Nq)$ in characteristic $q$, and the identification of non-Eisenstein inertia-invariant torsion killed by both degeneracy pushforwards $\alpha_*,\beta_*\colon J_0(Nq) \to J_0(N)$ as toric. They feed the level-lowering step for the mod $p$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ToricDescentData.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_DeligneRapoport
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Generic

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

structure IsAbelianPartDataQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (δ : Fin 2 → J →+ J₀) : Prop where

  toric_le_ker : ∀ i : Fin 2, ∀ x ∈ 𝒯, δ i x = 0

  goodPrime_equivariant : ∀ i : Fin 2, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    ∀ x : J, δ i (heckeGen ℓ • x) = heckeGen ℓ • δ i x

  component_eisenstein : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → (∀ i : Fin 2, δ i x = 0) → x ∈ 𝒯

theorem IsAbelianPartData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G}
    {𝒯 : Submodule HeckeAlg J} {δ : Fin 2 → J →+ J₀} (h : IsAbelianPartData S I 𝒯 δ) :
    IsAbelianPartDataQGuarded q S I 𝒯 δ where
  toric_le_ker := h.toric_le_ker
  goodPrime_equivariant := h.goodPrime_equivariant
  component_eisenstein := fun 𝔪 hmax heis _ => h.component_eisenstein 𝔪 hmax heis

def ExistsToricData (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartData S I 𝒯 δ

namespace ExistsToricData

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricData q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricData q S I φ δ) : ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartData (h : ExistsToricData q S I φ δ) : IsAbelianPartData S I h.toric δ :=
  h.choose_spec.2

end ExistsToricData

def ExistsToricDataQGuarded (q : ℕ) (S : Finset Nat.Primes) (I : Subgroup G) (φ : G)
    (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J, ToricFrobeniusSq q φ 𝒯 ∧ IsAbelianPartDataQGuarded q S I 𝒯 δ

theorem ExistsToricData.qGuarded {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
    {δ : Fin 2 → J →+ J₀} (h : ExistsToricData q S I φ δ) :
    ExistsToricDataQGuarded q S I φ δ := by
  obtain ⟨𝒯, hfrob, hab⟩ := h
  exact ⟨𝒯, hfrob, hab.qGuarded⟩

namespace ExistsToricDataQGuarded

variable {q : ℕ} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G} {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricDataQGuarded q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricDataQGuarded q S I φ δ) :
    ToricFrobeniusSq q φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartDataQGuarded (h : ExistsToricDataQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded q S I h.toric δ :=
  h.choose_spec.2

end ExistsToricDataQGuarded

def ToricFrobeniusHecke (q : Nat.Primes) (φ : G) (𝒯 : Submodule HeckeAlg J) : Prop :=
  ∀ x ∈ 𝒯, φ • x = (((q : ℕ) : HeckeAlg) * heckeGen q) • x

def ExistsToricDataFullQGuarded (q : Nat.Primes) (S : Finset Nat.Primes) (I : Subgroup G)
    (φ : G) (δ : Fin 2 → J →+ J₀) : Prop :=
  ∃ 𝒯 : Submodule HeckeAlg J,
    ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧ IsAbelianPartDataQGuarded (q : ℕ) S I 𝒯 δ ∧
    ToricFrobeniusHecke q φ 𝒯

namespace ExistsToricDataFullQGuarded

variable {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {δ : Fin 2 → J →+ J₀}

def toric (h : ExistsToricDataFullQGuarded q S I φ δ) : Submodule HeckeAlg J :=
  h.choose

theorem toricFrobeniusSq (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusSq (q : ℕ) φ h.toric :=
  h.choose_spec.1

theorem isAbelianPartDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    IsAbelianPartDataQGuarded (q : ℕ) S I h.toric δ :=
  h.choose_spec.2.1

theorem toricFrobeniusHecke (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ToricFrobeniusHecke q φ h.toric :=
  h.choose_spec.2.2

theorem toExistsToricDataQGuarded (h : ExistsToricDataFullQGuarded q S I φ δ) :
    ExistsToricDataQGuarded (q : ℕ) S I φ δ :=
  ⟨h.toric, h.toricFrobeniusSq, h.isAbelianPartDataQGuarded⟩

end ExistsToricDataFullQGuarded

end Generic

section Degeneracy

variable (N q : ℕ) [NeZero N] [NeZero q]

def DegeneracyPushforwardInputs : Prop :=
  ∃ (_ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q)),
    NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα ∧
      NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ

open Classical in

def degeneracyPushforwardPair : Fin 2 → (JZero (N * q) →+ JZero N) :=
  if h : DegeneracyPushforwardInputs N q then
    ![Pic0.pushforwardAlongHom (heckeAlphaBar (AlgebraicClosure ℚ) N q) h.1 h.2.2.1 h.2.2.2.2.1,
      Pic0.pushforwardAlongHom (heckeBetaBar (AlgebraicClosure ℚ) N q) h.2.1 h.2.2.2.1 h.2.2.2.2.2]
  else 0

variable {N q}

theorem degeneracyPushforwardInputs_intro
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ) :
    DegeneracyPushforwardInputs N q :=
  ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩

theorem degeneracyPushforwardPair_eq
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ) :
    degeneracyPushforwardPair N q =
      ![Pic0.pushforwardAlongHom (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hfinα hNα,
        Pic0.pushforwardAlongHom (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hfinβ hNβ] := by
  rw [degeneracyPushforwardPair, dif_pos (degeneracyPushforwardInputs_intro hα hβ hfinα hNα hfinβ hNβ)]

theorem degeneracyPushforwardPair_of_not (h : ¬ DegeneracyPushforwardInputs N q) :
    degeneracyPushforwardPair N q = 0 := by
  rw [degeneracyPushforwardPair, dif_neg h]

end Degeneracy

end ModularCurve

end


