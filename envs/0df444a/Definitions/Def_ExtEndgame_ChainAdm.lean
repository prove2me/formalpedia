-- Prove2me | Definitions.Def_ExtEndgame_ChainAdm
-- name    : ExtEndgame_ChainAdm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4e61572e-95c5-58b5-8235-958515543c7b
-- title:
--   Admissible-carrier Selmer realisation of cyclotomic extension classes
-- statement:
--   Throughout, $p$ is a prime, $V$ runs over $\mathbb{Z}/p$-modules (in the lowest universe) carrying an action of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ commuting with the scalars, and $C \subseteq V$ is a $\mathbb{Z}/p$-submodule satisfying `IsAdmissibleExtension p V C`: $C$ is Galois-stable and pointwise fixed, $\sigma\cdot x - \overline{\mathrm{cycloExp}\,\sigma}\cdot x \in C$ for all $\sigma$ and all $x \in V$ (so $V/C$ is the mod-$p$ cyclotomic character), $|C| = p$, $|V| = p^2$, inertia at every prime $\ell \neq p$ acts trivially on $V$, and at every valuation subring over $p$ the decomposition group preserves some complement of $C$. The cochain attached to $v_0 \in V$ is $\mathrm{extClassFun}(\chi, v_0)(\sigma) = \chi(\sigma)^{-1}\bigl(\sigma\cdot v_0 - \chi(\sigma)v_0\bigr)$ with $\chi =$ `cycloChar p` the mod-$p$ cyclotomic character.
--
--   `ExtClassesAreCoboundaries p` asserts that for every such admissible pair and every $v_0 \notin C$ there is $b \in C$ with $\mathrm{extClassFun}(\chi, v_0)(\sigma) = \chi(\sigma)^{-1}b - b$ for all $\sigma$, i.e. the class is a coboundary valued in $C$. `ExtSelmerRealization` and `ExtSelmerRealizationAdm` place this conclusion behind a Selmer class: for an abstract group $\Gamma'$, finitely many local groups $\Gamma'_v$ with maps $\mathrm{loc}'_v$, a character $\psi : \Gamma' \to (\mathbb{Z}/p)^\times$ with associated one-dimensional representation `ofChar ψ`, a set $P$ of places and local subspaces $U_v \subseteq H^1(\Gamma'_v, \psi)$, they assert that for every admissible pair and $v_0 \notin C$ there is an element $x$ of the Selmer group for the conditions $\mathrm{extConditions}$ ($0$ at places of $P$, $U_v$ elsewhere) — intersected with a submodule $\mathrm{adm}$ in the second version — such that $x = 0$ implies the coboundary conclusion. Thus each predicate is implied by non-vanishing of the relevant Selmer group, and conversely yields the coboundary statement once that group vanishes. `extSelmerRealizationAdm_top_iff` identifies the two when $\mathrm{adm} = \top$.
--
--   `ExtChainAdmResidual` bundles as fields the hypotheses of the vanishing argument for a datum $(\mathrm{loc}', \psi, M', \mathrm{pairing}, P, U, \mathrm{adm}, \mathrm{adm}', \rho, f)$: the admissible realisation predicate; a Greenberg–Wiles inequality datum `IsGreenbergWilesLeDatumAdm` for the conditions $\mathrm{extConditions}$ and the carriers $\mathrm{adm}, \mathrm{adm}'$; the local bound $\sum_v \dim \mathrm{extConditions}_v \le \sum_v \dim H^0(\Gamma'_v, \psi)$; vanishing of $H^0$ for both $\psi$ and $M'$; that $f$ maps every element of the dual admissible Selmer group (for the $\mathrm{pairing}$-orthogonal conditions) to an $\omega^{p-2}$-eigenvector for $\rho$, meaning $\rho(d)a = d^{\,p-2}a$; injectivity of $f$ on that group; and that the Stickelberger endomorphism $\sum_{0 < c,\ 2c < p} \rho(\bar c)^{-1}$ annihilates $A$.
--
--   **Relation to Mathlib.** Mathlib supplies the cyclotomic character (`modularCyclotomicCharacter`) and group cohomology of representations; the Selmer groups with local conditions, their admissible-carrier variants, the Greenberg–Wiles inequality data, the admissible-extension predicate and the Stickelberger vocabulary are the project's own.
--
--   **Where it is used.** These predicates form the interface of the argument that an admissible extension of the mod-$p$ cyclotomic character by the trivial character, unramified outside $p$ and locally split at $p$, has vanishing class: the class is realised in a Selmer group, whose vanishing is forced by a Greenberg–Wiles inequality together with Stickelberger annihilation on an $\omega^{p-2}$-eigenspace. The concrete arithmetic instantiation, with the $p$-torsion of the class group of $\mathbb{Q}(\zeta_p)$ as the module $A$, is made elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtEndgame_ChainAdm.lean

import Mathlib
import Definitions.Def_GroupCohomology_SelmerAdm
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_Stickelberger_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation

def ExtClassesAreCoboundaries (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        extClassFun (cycloChar p) v₀ σ
          = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b

def ExtSelmerRealization (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)))) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ x ∈ selmer loc' (ofChar (k := ZMod p) ψ)
          (extConditions loc' (ofChar (k := ZMod p) ψ) P U),
        (x = 0 →
          ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            extClassFun (cycloChar p) v₀ σ
              = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b)

def ExtSelmerRealizationAdm (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ))))
    (adm : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ψ))) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ x ∈ selmerAdm loc' (ofChar (k := ZMod p) ψ)
          (extConditions loc' (ofChar (k := ZMod p) ψ) P U) adm,
        (x = 0 →
          ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            extClassFun (cycloChar p) v₀ σ
              = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b)

theorem extSelmerRealizationAdm_top_iff (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)))) :
    ExtSelmerRealizationAdm p loc' ψ P U ⊤ ↔ ExtSelmerRealization p loc' ψ P U := by
  unfold ExtSelmerRealizationAdm ExtSelmerRealization
  simp_rw [selmerAdm_top]

structure ExtChainAdmResidual (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (M' : Rep (ZMod p) Γ')
    (pairing : ∀ v, H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)) →ₗ[ZMod p]
      H1 (Rep.res (loc' v) M') →ₗ[ZMod p] (ZMod p))
    (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ))))
    (adm : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ψ)))
    (adm' : Submodule (ZMod p) (H1 M'))
    {A : Type} [AddCommGroup A] [Module (ZMod p) A]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A)
    (f : H1 M' →ₗ[ZMod p] A) : Prop where

  hrealAdm : ExtSelmerRealizationAdm p loc' ψ P U adm

  hGWAdm : IsGreenbergWilesLeDatumAdm loc' (ofChar (k := ZMod p) ψ) M' pairing
    (extConditions loc' (ofChar (k := ZMod p) ψ) P U) adm adm'

  hsum : ∑ v, finrank (ZMod p) (extConditions loc' (ofChar (k := ZMod p) ψ) P U v)
    ≤ ∑ v, finrank (ZMod p) (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)).ρ.invariants

  hM : finrank (ZMod p) (ofChar (k := ZMod p) ψ).ρ.invariants = 0

  hM' : finrank (ZMod p) M'.ρ.invariants = 0

  heig : ∀ x ∈ selmerAdm loc' M' (dualConditions loc' (ofChar (k := ZMod p) ψ) M' pairing
      (extConditions loc' (ofChar (k := ZMod p) ψ) P U)) adm',
    Stickelberger.IsOmegaEigenvector ρ (p - 2) (f x)

  hinj : ∀ x ∈ selmerAdm loc' M' (dualConditions loc' (ofChar (k := ZMod p) ψ) M' pairing
      (extConditions loc' (ofChar (k := ZMod p) ψ) P U)) adm',
    f x = 0 → x = 0

  hann : Stickelberger.StickelbergerAnnihilates ρ

end ExtCitation


