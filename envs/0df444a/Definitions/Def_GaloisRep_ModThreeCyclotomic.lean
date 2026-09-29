-- Prove2me | Definitions.Def_GaloisRep_ModThreeCyclotomic
-- name    : GaloisRep_ModThreeCyclotomic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a6565c84-e57c-55bf-9894-ce302ab43f26
-- title:
--   The mod-3 cyclotomic character on the absolute Galois group of ℚ
-- statement:
--   This module packages the mod-$3$ cyclotomic character as a homomorphism on $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Concretely, [`WeierstrassCurve.modThreeCyclotomicChar`](../def/GaloisRep_ModThreeCyclotomic.html#L10) is the monoid homomorphism
--   $$(\,\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}\,) \longrightarrow (\mathbb{Z}/3)^{\times}$$
--   sending a $\mathbb{Q}$-algebra automorphism $\sigma$ of `AlgebraicClosure ℚ` to the value at the underlying ring isomorphism $\sigma$ of Mathlib's `modularCyclotomicCharacter` for $n = 3$; that is, to the unique unit $\chi(\sigma) \in (\mathbb{Z}/3)^{\times}$ with $\sigma(\zeta) = \zeta^{\chi(\sigma)}$ for every cube root of unity $\zeta$. The side condition required by `modularCyclotomicCharacter`, namely that the group of cube roots of unity in $\overline{\mathbb{Q}}$ has exactly three elements, is discharged by [`IsAlgClosed.card_rootsOfUnity_eq`](../def/ExtCitation_AdmissibleExtension.html#L7), which gives, for any algebraically closed field of characteristic zero and any nonzero $n$, that the group $\mu_n$ of $n$-th roots of unity has exactly $n$ elements. Since `modularCyclotomicCharacter` is stated for ring isomorphisms while the Galois action in this development is by $\mathbb{Q}$-algebra equivalences, the map is constructed with `MonoidHom.mk'`: only multiplicativity is checked, using multiplicativity of the cyclotomic character together with the fact that the coercion from algebra equivalences to ring equivalences preserves composition. The accompanying lemma `modThreeCyclotomicChar_apply` records that the value of the homomorphism at $\sigma$ is by definition the cyclotomic-character value at the coerced ring isomorphism.
--
--   **Relation to Mathlib.** Mathlib provides `modularCyclotomicCharacter` for a field $K$ together with the hypothesis that $\mu_n(K)$ has exactly $n$ elements, as a homomorphism on ring automorphisms; this module only specialises it to $K = \overline{\mathbb{Q}}$ and $n = 3$ and transports it along the coercion from $\mathbb{Q}$-algebra automorphisms to ring automorphisms.
--
--   **Where it is used.** The character serves as the target of the determinant comparison for mod-$3$ Galois representations: the project's `galoisRepDet` and `GaloisRepDetEqCyclotomic` assert that the determinant of the $n$-torsion representation of a curve agrees with the mod-$n$ cyclotomic character, which for $n=3$ is this map, and it is the nontrivial possibility in the classification of the determinant characters occurring in the Langlands–Tunnell input to the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_ModThreeCyclotomic.lean

import Mathlib
import Definitions.Def_FreyPackage_DetCyclotomic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine.Point

noncomputable def modThreeCyclotomicChar :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod 3)ˣ :=
  MonoidHom.mk'
    (fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (fun a b => by rw [← map_mul]; congr 1)

@[simp] lemma modThreeCyclotomicChar_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    modThreeCyclotomicChar σ = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :=
  rfl

end WeierstrassCurve


