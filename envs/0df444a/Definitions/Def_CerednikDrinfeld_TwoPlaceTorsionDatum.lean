-- Prove2me | Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
-- name    : CerednikDrinfeld_TwoPlaceTorsionDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/5a18c7a3-342a-5213-a507-e44c5a4a861f
-- title:
--   Two-place torsion data, local laws, good reduction outside M
-- statement:
--   Four notions are introduced over the standing data: a natural number $p$, finite index sets $E_i \rightrightarrows V_i$ with degeneracy data $D_i$ (two maps $E_i \to V_i$ and a width function) and formal Hecke data $H_i$, and valuation subrings $A_1,A_2$ of $\overline{\mathbb{Q}}$.
--
--   `LocalLaws Dm r` is a Prop-valued structure collecting the laws expected of a one-place datum `Dm` (a finite abelian group $T$ killed by $p$ with commuting actions of `HeckeAlg` $=\mathbb{Z}[X_\ell:\ell\text{ prime}]$ and of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, a subgroup `toric`, an isomorphism `toricEquiv` of it with $\mathrm{Hom}_{\mathbb{Z}}(Z,\mathbb{Z}/p)$ for $Z=$ `ribbonKernel D`, and a homomorphism `sp` from the inertia invariants at $A$ to $\Psi=Z^{*}/\mathrm{im}(\text{ribbonGram})$) at a place of residue characteristic $r$: `toric` is stable under every element of `HeckeAlg`; `toricEquiv` turns the action of the generator $X_\ell$ into precomposition with `heckeKernelMap H ℓ`; `toric` lies in the inertia invariants; $\ker(\mathrm{sp})=$ `toric`; the image of `sp` is exactly $\Psi[p]$; `sp` carries $X_\ell$ to the map induced on $\Psi$ by $\varphi \mapsto \varphi \circ$ `heckeKernelMap H ℓ`, stated both as a compatibility with chosen dual lifts and, for an arbitrary ring homomorphism `heckeΨ` realising that formula on generators, as full equivariance; and, for every Frobenius $\varphi$ at $A$ over $r$, the identities $\varphi = r\,X_r$ on `toric` and $\varphi \equiv X_r$ modulo `toric` on all of $T$.
--
--   `GoodReductionOutside Dm M` asserts, for every prime $\ell \nmid M$ and every valuation subring $B$ lying over $\ell$: inertia at $B$ acts trivially on $T$, and every Frobenius $\sigma$ at $B$ satisfies $\sigma^{2}-X_\ell\sigma+\ell=0$ on $T$.
--
--   `TwoPlaceTorsionDatum` packages a single such $T$, with its `HeckeAlg`-action, Galois action factoring through a finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$, and two independent toric subgroups, identifications and specialisation maps, one for $(D_1,A_1)$ and one for $(D_2,A_2)$. The projections `fst`, `snd` return the one-place data at $A_1$ over $(D_1,H_1)$ and at $A_2$ over $(D_2,H_2)$, sharing $T$ and both actions; `fst_D`, `snd_D`, `fst_T`, `snd_T`, `fst_toric`, `snd_toric` record this. Finally `Laws 𝒥 M r₁ r₂` bundles `GoodReductionOutside M` for `𝒥.fst` (its clauses involve only the shared $T$, Hecke and Galois actions) together with `LocalLaws r₁` for `𝒥.fst` and `LocalLaws r₂` for `𝒥.snd`.
--
--   **Relation to Mathlib.** Mathlib has no notion of degeneracy or ribbon data, of toric parts and component groups of such data, nor of torsion data of this shape; these are the project's own. The ambient Hecke algebra is the polynomial ring `MvPolynomial Nat.Primes ℤ`, and the Galois-side notions (valuation subrings, inertia subgroups, Frobenius conditions) come from Mathlib or from the project's ramification definitions.
--
--   **Where it is used.** This is the axiomatised shape of the $p$-torsion of the Jacobian of a Shimura curve attached to an Eichler order in an indefinite rational quaternion algebra of discriminant $qq'$, read simultaneously at a place over $q$ and at a place over $q'$, both of purely toric (Čerednik–Drinfeld) reduction, with character groups identified with the doubly-new sublattices of the corresponding supersingular degeneracy graphs. The laws recorded here are what the level-lowering argument consumes when it transfers a mod $p$ eigensystem between curves of different level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_TwoPlaceTorsionDatum.lean

import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

structure LocalLaws (Dm : JPrimeTorsionDatum p E V A) (r : ℕ) [Fact r.Prime] : Prop where

  toric_hecke : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric

  toricEquiv_hecke : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric)
      (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ

  toric_le_invariants : Dm.toric ≤ Dm.invariants

  sp_eq_zero_iff : ∀ t : ↥Dm.invariants, Dm.sp t = 0 ↔ (t : Dm.T) ∈ Dm.toric

  mem_range_sp_iff : ∀ ψ : ribbonComponentGroup Dm.D, ψ ∈ Dm.sp.range ↔ p • ψ = 0

  sp_hecke : ∀ (ℓ : Nat.Primes) (t : ↥Dm.invariants)
      (hℓt : Dm.hecke (heckeGen ℓ) (t : Dm.T) ∈ Dm.invariants)
      (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
      Dm.sp t = ribbonComponentGroupProj Dm.D φ →
        Dm.sp ⟨Dm.hecke (heckeGen ℓ) (t : Dm.T), hℓt⟩ =
          ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ)

  sp_hecke_ringHom : ∀ (heckeΨ : HeckeAlg →+* Module.End ℤ (ribbonComponentGroup Dm.D)),
      (∀ (ℓ : Nat.Primes) (φ : Module.Dual ℤ ↥(ribbonKernel Dm.D)),
          heckeΨ (heckeGen ℓ) (ribbonComponentGroupProj Dm.D φ) =
            ribbonComponentGroupProj Dm.D (φ ∘ₗ heckeKernelMap Dm.H ℓ)) →
        ∀ (x : HeckeAlg) (t : ↥Dm.invariants) (ht : Dm.hecke x (t : Dm.T) ∈ Dm.invariants),
          Dm.sp ⟨Dm.hecke x (t : Dm.T), ht⟩ = heckeΨ x (Dm.sp t)

  frobenius_toric : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ t : Dm.T, t ∈ Dm.toric → Dm.gal φ t = Dm.hecke ((r : HeckeAlg) * heckeGen ⟨r, Fact.out⟩) t

  frobenius_quot : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
      ∀ t : Dm.T, Dm.gal φ t - Dm.hecke (heckeGen ⟨r, Fact.out⟩) t ∈ Dm.toric

structure GoodReductionOutside (Dm : JPrimeTorsionDatum p E V A) (M : ℕ) : Prop where

  unramified : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ ∈ B.inertiaSubgroupIn ℚ, Dm.gal σ = 1

  eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt σ ℓ →
          ∀ t : Dm.T, Dm.gal σ (Dm.gal σ t) - Dm.hecke (heckeGen ⟨ℓ, hℓ⟩) (Dm.gal σ t) + ℓ • t = 0

end JPrimeTorsionDatum

structure TwoPlaceTorsionDatum (p : ℕ) {E₁ V₁ E₂ V₂ : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    (D₁ : DegeneracyData E₁ V₁) (H₁ : HeckeData D₁) (D₂ : DegeneracyData E₂ V₂) (H₂ : HeckeData D₂)
    (A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)) : Type 1 where

  T : Type
  [instAddCommGroup : AddCommGroup T]
  [instFinite : Finite T]

  pTorsion : ∀ t : T, p • t = 0

  hecke : HeckeAlg →+* Module.End ℤ T

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T

  comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
    gal σ (hecke x t) = hecke x (gal σ t)

  finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ = 1

  toric₁ : AddSubgroup T

  toricEquiv₁ : ↥toric₁ ≃+ (↥(ribbonKernel D₁) →ₗ[ℤ] ZMod p)

  sp₁ : ↥(⨅ σ ∈ A₁.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D₁

  toric₂ : AddSubgroup T

  toricEquiv₂ : ↥toric₂ ≃+ (↥(ribbonKernel D₂) →ₗ[ℤ] ZMod p)

  sp₂ : ↥(⨅ σ ∈ A₂.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D₂

attribute [instance] TwoPlaceTorsionDatum.instAddCommGroup TwoPlaceTorsionDatum.instFinite

namespace TwoPlaceTorsionDatum

variable {p : ℕ} {E₁ V₁ E₂ V₂ : Type}
  [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
  {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂}
  {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}

def fst (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : JPrimeTorsionDatum p E₁ V₁ A₁ where
  D := D₁
  H := H₁
  T := 𝒥.T
  pTorsion := 𝒥.pTorsion
  hecke := 𝒥.hecke
  gal := 𝒥.gal
  comm := 𝒥.comm
  finiteLevel := 𝒥.finiteLevel
  toric := 𝒥.toric₁
  toricEquiv := 𝒥.toricEquiv₁
  sp := 𝒥.sp₁

def snd (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : JPrimeTorsionDatum p E₂ V₂ A₂ where
  D := D₂
  H := H₂
  T := 𝒥.T
  pTorsion := 𝒥.pTorsion
  hecke := 𝒥.hecke
  gal := 𝒥.gal
  comm := 𝒥.comm
  finiteLevel := 𝒥.finiteLevel
  toric := 𝒥.toric₂
  toricEquiv := 𝒥.toricEquiv₂
  sp := 𝒥.sp₂

@[simp] theorem fst_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.D = D₁ := rfl
@[simp] theorem snd_D (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.D = D₂ := rfl
@[simp] theorem fst_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.T = 𝒥.T := rfl
@[simp] theorem snd_T (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.T = 𝒥.T := rfl
@[simp] theorem fst_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.fst.toric = 𝒥.toric₁ := rfl
@[simp] theorem snd_toric (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) : 𝒥.snd.toric = 𝒥.toric₂ := rfl

structure Laws (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂) (M r₁ r₂ : ℕ)
    [Fact r₁.Prime] [Fact r₂.Prime] : Prop where

  goodReduction : 𝒥.fst.GoodReductionOutside M

  fst : 𝒥.fst.LocalLaws r₁

  snd : 𝒥.snd.LocalLaws r₂

end TwoPlaceTorsionDatum

end CerednikDrinfeld


