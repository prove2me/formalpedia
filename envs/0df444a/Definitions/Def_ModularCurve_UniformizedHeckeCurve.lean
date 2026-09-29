-- Prove2me | Definitions.Def_ModularCurve_UniformizedHeckeCurve
-- name    : ModularCurve_UniformizedHeckeCurve
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/06663b1a-659b-5700-b50f-48a4147dc177
-- title:
--   Uniformized Hecke curves over the upper half-plane
-- statement:
--   For a subgroup $\Gamma \le \mathrm{GL}_2(\mathbb{R})$ acting on the upper half-plane $\mathfrak{H}$ and a field $F_c$ that is a $\mathbb{C}$-algebra, [`ModularCurve.UniformizedHeckeCurve Γ Fc`](../def/ModularCurve_UniformizedHeckeCurve.html#L14) is a structure packaging an analytic uniformisation of the places of $F_c$ over $\mathbb{C}$ by points of $\mathfrak{H}$, together with Hecke correspondences. Here a place ([`AlgebraicCurve.Place ℂ Fc`](../def/AlgebraicCurve_DivisorClassGroup.html#L22)) is a valuation subring of $F_c$ containing the image of $\mathbb{C}$, not equal to all of $F_c$ and a principal ideal ring, so a discrete valuation ring with associated order function `ord`; divisors are finitely supported $\mathbb{Z}$-valued functions on places. The data are: a map $\mathrm{pt} : \mathfrak{H} \to \{\text{places}\}$; a realisation $\mathrm{realize} : F_c \to \mathfrak{H} \to \mathbb{C}$; a ramification function $e : \mathfrak{H} \to \mathbb{N}$ with $e(\tau) > 0$; a distinguished element of $F_c$; for each prime $\ell$ a multiset $\Delta_\ell$ of elements of $\mathrm{GL}_2(\mathbb{R})$ and an additive endomorphism $\mathrm{corr}_\ell$ of the divisor group. The axioms, carried as fields, assert: $x$ lies in the valuation subring of $\mathrm{pt}(\tau)$ exactly when $z \mapsto \|\mathrm{realize}\,x\,z\|$ is bounded near $\tau$ along the punctured neighbourhood filter; for $x \neq 0$ the meromorphic order at $\tau$ of the realisation, read as a function of a complex variable through `ofComplex`, equals $e(\tau)\cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$; $\mathrm{pt}(\tau) = \mathrm{pt}(\tau')$ iff $\tau' = \gamma\tau$ for some $\gamma \in \Gamma$; every place whose valuation subring contains the distinguished element is some $\mathrm{pt}(\tau)$; $2e(\tau)$ is the cardinality of the stabiliser of $\tau$ in $\Gamma$; and $\mathrm{corr}_\ell$ sends the divisor $[\mathrm{pt}(\tau)]$ to $\sum_{\delta \in \Delta_\ell} [\mathrm{pt}(\delta\tau)]$.
--
--   Two helpers fix the intended level structure: `gamma0GL N` is the image of $\Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$, and `heckePoints N ℓ` is the multiset consisting of the matrices $\begin{pmatrix}1 & j\\ 0 & \ell\end{pmatrix}$ for $0 \le j < \ell$, together with $\begin{pmatrix}\ell & 0\\ 0 & 1\end{pmatrix}$ when $\ell \nmid N$.
--
--   **Relation to Mathlib.** Mathlib supplies the upper half-plane with its $\mathrm{GL}_2(\mathbb{R})$-action, congruence subgroups and `meromorphicOrderAt`; the notions of place and divisor used here, the Hecke matrices, and the uniformised Hecke curve structure itself are the project's own.
--
--   **Where it is used.** The structure is the interface through which the complex-analytic description of $\Gamma_0(N)\backslash\mathfrak{H}$ is transferred to the algebraic language of places and divisors of the modular function field, so that Hecke correspondences become endomorphisms of the divisor group and orders of vanishing of modular functions become valuations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_UniformizedHeckeCurve.lean

import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

structure UniformizedHeckeCurve (Γ : Subgroup (GL (Fin 2) ℝ)) (Fc : Type) [Field Fc] [Algebra ℂ Fc] where

  pt : ℍ → AlgebraicCurve.Place ℂ Fc

  realize : Fc → ℍ → ℂ

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  mem_pt_iff : ∀ (τ : ℍ) (x : Fc), x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖realize x z‖)

  meromorphicOrderAt_realize : ∀ (τ : ℍ) (x : Fc), x ≠ 0 →
      meromorphicOrderAt (fun z : ℂ => realize x (ofComplex z)) (τ : ℂ) =
        (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

  pt_eq_pt_iff : ∀ τ τ' : ℍ, pt τ = pt τ' ↔ ∃ γ ∈ Γ, γ • τ = τ'

  distinguished : Fc

  exists_pt_eq : ∀ P : AlgebraicCurve.Place ℂ Fc, distinguished ∈ P.toValuationSubring → ∃ τ : ℍ, pt τ = P

  two_mul_ramification : ∀ τ : ℍ, 2 * ramification τ = Nat.card (MulAction.stabilizer Γ τ)

  heckePoints : ∀ ℓ : ℕ, ℓ.Prime → Multiset (GL (Fin 2) ℝ)

  corr : ∀ ℓ : ℕ, ℓ.Prime → (AlgebraicCurve.Divisor ℂ Fc →+ AlgebraicCurve.Divisor ℂ Fc)

  corr_single_pt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (τ : ℍ),
      corr ℓ hℓ (Finsupp.single (pt τ) 1) =
        ((heckePoints ℓ hℓ).map fun δ => Finsupp.single (pt (δ • τ)) 1).sum

section Level

variable (N : ℕ)

def gamma0GL : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

def heckePoints (ℓ : ℕ) (_hℓ : ℓ.Prime) : Multiset (GL (Fin 2) ℝ) :=
  (Finset.range ℓ).val.map (fun j => ModularForm.heckeMatrix ℓ j) +
    (if ℓ ∣ N then 0 else {ModularForm.heckeDiagMatrix ℓ})

end Level

end ModularCurve

end


