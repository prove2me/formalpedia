-- Prove2me | Definitions.Def_EllipticCurve_FrobeniusTrace
-- name    : EllipticCurve_FrobeniusTrace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a1ca1b69-152b-5d32-9250-96e0c0aac230
-- title:
--   Mod-n Galois trace on torsion; Frobenius at a place
-- statement:
--   Two unrelated pieces of vocabulary are set up here, both used for stating trace-of-Frobenius congruences.
--
--   The first concerns the mod-$n$ representation attached to a Weierstrass curve. Fix commutative rings $R$, $S$ and a field $K$ with compatible algebra structures ($R\to S\to K$ a scalar tower), an affine Weierstrass curve $W'$ over $R$, and $n : \mathbb{N}$. The carrier is the $\mathbb{Z}$-torsion submodule `Submodule.torsionBy ℤ (W'⁄K).Point n`, i.e. the subgroup of $n$-torsion points of the base-changed curve $(W'⁄K)$ over $K$, viewed as a $\mathbb{Z}/n$-module. The group $K \simeq_{\text{alg}[S]} K$ of $S$-algebra automorphisms of $K$ acts on it coordinatewise (this action and the $\mathbb{Z}/n$-module structure come from the project's Galois-representation definitions); an instance records that the two actions commute. Then `galoisRepModuleEnd S W' n` is the monoid homomorphism $\sigma \mapsto (x \mapsto \sigma \cdot x)$ into $\mathrm{End}_{\mathbb{Z}/n}$ of that torsion module, and `galoisTrace S W' n σ` is defined to be `LinearMap.trace (ZMod n)` of this endomorphism, an element of $\mathbb{Z}/n$. Note that the trace is taken on the torsion module as it stands, with no freeness or finiteness hypothesis; it therefore agrees with the classical $\operatorname{tr}\bar\rho_{E,n}(\sigma)$ exactly when that module is finite free over $\mathbb{Z}/n$ (Mathlib's `LinearMap.trace` is $0$ in degenerate cases). Two `rfl` lemmas unfold the action and the definition of the trace.
--
--   The second is a predicate on places. For a field extension $L/K$ and a valuation subring $A \subseteq L$, [`ValuationSubring.IsFrobeniusAt A σ q`](../def/EllipticCurve_FrobeniusTrace.html#L51) says that $\sigma \in L \simeq_{\text{alg}[K]} L$ lies in the decomposition subgroup of $A$ over $K$ and that the induced automorphism of the residue field of $A$ is the $q$-power map $x \mapsto x^{q}$. The two accessor lemmas extract the membership and the identity $\sigma \cdot x = x^{q}$ on residues. No surjectivity or uniqueness of such $\sigma$ is asserted: this is a property an element may or may not have.
--
--   **Relation to Mathlib.** Built on Mathlib's `Submodule.torsionBy`, `DistribMulAction.toModuleEnd`, `LinearMap.trace`, `ValuationSubring.decompositionSubgroup` and `IsLocalRing.ResidueField`; the notion of a Frobenius element at a valuation subring, and the trace of the mod-$n$ Galois action on torsion points, are packaged here rather than in Mathlib.
--
--   **Where it is used.** These definitions give the language in which the project states congruences of the form $\operatorname{tr}\bar\rho_{E,n}(\mathrm{Frob}_\ell) \equiv a_\ell(E) \pmod n$ for an elliptic curve at a prime $\ell$ of good reduction, with $\mathrm{Frob}_\ell$ taken to be any element satisfying `IsFrobeniusAt` for a place above $\ell$. Such congruences are what link mod-$\ell$ representations of Frey curves to Hecke eigenvalues of modular forms in the level-lowering and modularity steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EllipticCurve_FrobeniusTrace.lean

import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Valuation.RamificationGroup
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

variable (S) in

def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp] lemma galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K)
    (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd S W' n σ x = σ • x :=
  rfl

variable (S) in

def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n :=
  LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) (galoisRepModuleEnd S W' n σ)

lemma galoisTrace_def (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd S W' n σ) :=
  rfl

end WeierstrassCurve.Affine.Point

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

lemma IsFrobeniusAt.mem_decompositionSubgroup {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.choose

lemma IsFrobeniusAt.smul_residue_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) (x : IsLocalRing.ResidueField A) :
    (⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • x = x ^ q :=
  h.choose_spec x

end ValuationSubring

end


