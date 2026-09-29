-- Prove2me | Definitions.Def_ModularCurve_EisensteinIdeal
-- name    : ModularCurve_EisensteinIdeal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f7fc8612-6d3d-5764-8f77-2790ba29fc0e
-- title:
--   Eisenstein eigensystem evaluation, Eisenstein maximal ideal, Eisenstein congruence
-- statement:
--   The ambient Hecke algebra is the project's abstract model $\mathbb{T} =$ `HeckeAlg`, the polynomial ring $\mathbb{Z}[X_\ell]$ on one generator `heckeGen ℓ` for each prime $\ell$, and the Eisenstein system at level $N$ is the family `eisensteinSystem N` sending a prime $\ell$ to $1$ when $\ell \mid N$ and to $1 + \ell$ otherwise. Four things are defined on top of this. First, `eisensteinEval N` is the $\mathbb{Z}$-algebra homomorphism $\mathbb{T} \to \mathbb{Z}$ obtained by evaluating at this family, so that the generator attached to $\ell$ is sent to $1$ for $\ell \mid N$ and to $1+\ell$ for $\ell \nmid N$. Second, `eisensteinMaximalIdeal N p`, for natural numbers $N$ and $p$, is the ideal of $\mathbb{T}$ defined as the preimage under `eisensteinEval N` of the principal ideal $(p) \subseteq \mathbb{Z}$; equivalently, by the membership lemma, $t$ lies in it exactly when $p \mid$ `eisensteinEval N t`, and in particular the image of $p$ in $\mathbb{T}$ lies in it. No primality assumption on $p$ is imposed and no maximality is asserted here: the name records the intended use, while the definition is the comap just described. Third, `IsEisensteinCongruent m N a` is a predicate on a family of integers $a$ indexed by the primes: for every prime $\ell$ whose underlying natural number is different from $N$, one has $a_\ell \equiv \ell + 1$ in $\mathbb{Z}/m\mathbb{Z}$. Note that the excluded primes are those equal to $N$, not those dividing $N$, and that this is a congruence condition on a system of integer eigenvalues, not a statement about ideals. Fourth, `modSystem m a` is the reduction $\ell \mapsto a_\ell \bmod m$ of such a family to a family of elements of $\mathbb{Z}/m\mathbb{Z}$. Two further lemmas record the value of `eisensteinEval N` on a generator and the defining value of `modSystem`.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebra or Eisenstein ideal; both the model $\mathbb{T} =$ `MvPolynomial Nat.Primes ℤ` and the notions here are the project's own, built from Mathlib's multivariate polynomial evaluation and `Ideal.comap`.
--
--   **Where it is used.** Together with the Eisenstein ideal `eisensteinIdeal N` (the kernel of the same evaluation), these definitions supply the maximal ideal and the congruence condition at which the project's Eichler–Shimura and multiplicity-one data for Hecke modules are formulated, for instance in the statements about nonvanishing of $\mathfrak{m}$-torsion and about eigenform ideals containing the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EisensteinIdeal.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def eisensteinEval (N : ℕ) : HeckeAlg →ₐ[ℤ] ℤ :=
  MvPolynomial.aeval (eisensteinSystem N)

@[simp] lemma eisensteinEval_heckeGen (N : ℕ) (ℓ : Nat.Primes) :
    eisensteinEval N (heckeGen ℓ) = eisensteinSystem N ℓ := by
  simp [eisensteinEval, heckeGen]

def eisensteinMaximalIdeal (N p : ℕ) : Ideal HeckeAlg :=
  Ideal.comap (eisensteinEval N) (Ideal.span {(p : ℤ)})

lemma mem_eisensteinMaximalIdeal_iff (N p : ℕ) (t : HeckeAlg) :
    t ∈ eisensteinMaximalIdeal N p ↔ (p : ℤ) ∣ eisensteinEval N t := by
  rw [eisensteinMaximalIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

lemma natCast_mem_eisensteinMaximalIdeal (N p : ℕ) :
    (p : HeckeAlg) ∈ eisensteinMaximalIdeal N p := by
  rw [mem_eisensteinMaximalIdeal_iff, map_natCast]

def IsEisensteinCongruent (m : ℕ) (N : ℕ) (a : Nat.Primes → ℤ) : Prop :=
  ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ N → ((a ℓ : ZMod m)) = ((ℓ : ℕ) : ZMod m) + 1

def modSystem (m : ℕ) (a : Nat.Primes → ℤ) : Nat.Primes → ZMod m :=
  fun ℓ => (a ℓ : ZMod m)

@[simp] lemma modSystem_apply (m : ℕ) (a : Nat.Primes → ℤ) (ℓ : Nat.Primes) :
    modSystem m a ℓ = (a ℓ : ZMod m) := rfl

end ModularCurve


