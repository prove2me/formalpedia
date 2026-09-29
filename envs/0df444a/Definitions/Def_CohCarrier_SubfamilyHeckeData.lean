-- Prove2me | Definitions.Def_CohCarrier_SubfamilyHeckeData
-- name    : CohCarrier_SubfamilyHeckeData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a964538f-bdd0-5ece-8cfa-a72f4c109d2b
-- title:
--   Hecke data for a subfamily of Hecke operators
-- statement:
--   Throughout, $M$ is a natural number with `NeZero M`, $H \le (\mathbb{Z}/M)^\times$ a subgroup, $S$ a set of natural numbers, $\mathcal{O}$ a commutative ring and $k$ a field with an $\mathcal{O}$-algebra structure. The carrier is `H1 M H 𝒪`, the group of additive homomorphisms from $\Gamma_H(M)$ (the preimage in $\mathrm{SL}_2(\mathbb{Z})$ of $H$ under the lower-triangular reduction character, viewed additively) to $\mathcal{O}$, an $\mathcal{O}$-module. The inductive type `Gen M S` names formal generators: $T_\ell$ for primes $\ell \notin S$ with $\ell \nmid M$, $U_q$ for primes $q \mid M$, and $\langle d\rangle$ for $d \in (\mathbb{Z}/M)^\times$; `opFamily` realises $T_\ell$ and $U_q$ by the same transfer-and-conjugate endomorphism `heckeTL` at the prime in question and $\langle d \rangle$ by conjugation by a chosen element of $\Gamma_0(M)$ over $d$.
--
--   `hdataSub` packages a subfamily of these operators as a `HeckeData`: given any index type $G$, a map $\varphi\colon G \to$ `Gen M S` (not assumed injective), a proof `hcomm` that the endomorphisms `opFamily (φ g)`, $g \in G$, commute pairwise, and a map $\bar\theta\colon G \to k$, the resulting datum has generator type $G$, operator $g \mapsto$ `opFamily (φ g)`, commutativity field `hcomm` (the structure carries this theorem as a field) and residual system $\bar\theta$. `hdataSub_op` records the operator attached to $g$, and `hdataSub_id` that for $G =$ `Gen M S` and $\varphi = \mathrm{id}$ one recovers `hdata`.
--
--   The abbreviation `MLSubAt` is the associated localised module: $H^1$ is a module over $\mathcal{O}[X_g : g \in G]$ via $X_g \mapsto$ `opFamily (φ g)`, and `MLSubAt` is its localisation at the prime complement of $\ker(\mathrm{aeval}\,\bar\theta)$, again an $\mathcal{O}$-module.
--
--   **Relation to Mathlib.** Mathlib supplies the congruence subgroups, the group-theoretic transfer used to build the operators, and `LocalizedModule`; the `HeckeData` structure and the operator family on $\mathrm{Hom}(\Gamma_H(M),\mathcal{O})$ are the project's own.
--
--   **Where it is used.** This gives the localisation of the cohomological carrier at a residual eigensystem prescribed only on a chosen subfamily of Hecke and diamond operators, which is the form needed for the anemic Hecke algebras of the Taylor–Wiles argument, where operators at the auxiliary primes in $S$ are deliberately omitted. Statements proved for the subfamily datum specialise to the full datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_SubfamilyHeckeData.lean

import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CohCarrier

section Sub

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

def hdataSub [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) : HeckeData 𝒪 (H1 M H 𝒪) k where
  Gen := G
  op g := opFamily M H S 𝒪 (φ g)
  comm := hcomm
  θbar := θbar

theorem hdataSub_op [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) (g : G) :
    (hdataSub M H S 𝒪 k φ hcomm θbar).op g = opFamily M H S 𝒪 (φ g) := rfl

theorem hdataSub_id [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) :
    hdataSub M H S 𝒪 k id hcomm θbar = hdata M H S 𝒪 k hcomm θbar := rfl

abbrev MLSubAt [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) : Type :=
  (hdataSub M H S 𝒪 k φ hcomm θbar).ML

example [NeZero M] {G : Type} (φ : G → Gen M S) (hcomm) (θbar : G → k) :
    Module 𝒪 (MLSubAt M H S 𝒪 k φ hcomm θbar) :=
  inferInstance

end Sub

end CohCarrier

end


