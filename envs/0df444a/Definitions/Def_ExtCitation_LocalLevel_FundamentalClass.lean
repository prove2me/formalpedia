-- Prove2me | Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
-- name    : ExtCitation_LocalLevel_FundamentalClass
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a5f6b206-d302-54b2-9c6b-007bf21133bd
-- title:
--   Local fundamental class via unramified over-layers
-- statement:
--   Throughout, $q$ is a prime, $\overline{\mathbb{Q}}_q$ is written `PadicAlgCl q`, and layers are intermediate fields of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ carrying the spectral norm; for a finite layer $K$, `Rw q K` denotes its valuation ring (the elements of norm at most $1$). The predicate `IsBase` on a layer $L$ with a group $G$ acting by $\mathbb{Q}_q$-semiring automorphisms and a layer $K$ asserts two things: $K \le L$, and an element of $L$ lies in $K$ exactly when it is fixed by every $g \in G$; that is, $K = L^{G}$. The structure `IsUnramOverlayerDatum` is a predicate (all fields are propositions) on a finite layer $M \ge L$ with a finite group $H$ acting faithfully on $M$ and compatibly on $M^{\times}$, two normal subgroups $N_L, N_n \le H$, an isomorphism $e : G \cong H/N_L$, an element $\varphi \in H$ and a unit $\pi \in M^{\times}$. Its clauses say: $H$ fixes the image of $\mathbb{Q}_q$ and acts on $M^{\times}$ through its action on $M$; $M^{H} = K$ and $M^{N_L} = L$; the $G$-action on $L$ agrees, under $e$ and the quotient map, with the $H$-action on $M$; $|H/N_n| = |G|$; the image $\bar\varphi$ of $\varphi$ generates $H/N_n$; for every $x \in M^{N_n}$ of norm at most $1$ one has $\|\varphi \cdot x - x^{\,|k_K|}\| < 1$, where $k_K$ is the residue field of `Rw q K`, so $\bar\varphi$ induces the Frobenius on residues; and $\pi$ is $H$-invariant, lies in $K$, has norm $< 1$, and has maximal norm among the elements of $M^{N_n}$ of norm $< 1$, i.e. $\pi$ is a uniformiser there. Thus the datum presents $M^{N_n}/K$ as unramified of degree $|G|$ with Frobenius $\bar\varphi$ and $\pi$ a uniformiser of the base.
--
--   Attached to such a datum, `piInv` records $\pi$, written additively, as an element of the $H/N_n$-representation $(M^{\times})^{N_n}$ obtained from `Rep.ofMulDistribMulAction H (↥M)ˣ` by passing to $N_n$-invariants; `ofMul_pi_mem` is the invariance statement that makes this legitimate, and `piInv_val` identifies the underlying element. Finally, `IsLocalFundamentalClass L G K u`, for a class $u \in H^{2}(G, L^{\times})$, asserts: for every over-layer datum as above and every morphism $\iota$ of $\mathbb{Z}$-representations from $L^{\times}$ pulled back along $H \to H/N_L \xrightarrow{e^{-1}} G$ to $M^{\times}$ whose underlying map is the inclusion $L^{\times} \subseteq M^{\times}$ (checked on images in $\overline{\mathbb{Q}}_q$), and whenever $\bar\varphi$ has finite order and the carry function `carryFun` built from $\bar\varphi$ and `piInv` is a $2$-cocycle, the image of $u$ under the degree-$2$ cohomology map induced by $(H \to G, \iota)$ equals the inflation to $H$ of the class in $H^{2}(H/N_n, (M^{\times})^{N_n})$ of that carry cocycle. Here `carryFun` sends a pair $(g,h)$ to $\pi$ or $1$ according to whether the discrete logarithms of $g$ and $h$ with respect to $\bar\varphi$, taken in $\{0,\dots,n-1\}$, sum to at least $n = \mathrm{ord}(\bar\varphi)$. So the predicate pins down $u$ by requiring its image in every unramified over-layer to be the inflated carry class of a base uniformiser; no existence or uniqueness is asserted here.
--
--   **Relation to Mathlib.** The cohomological apparatus used in the statements — `groupCohomology.H2`, `cocycles₂`, the projection `H2π`, the inflation natural transformation, `Rep.ofMulDistribMulAction` and the passage to invariants `Rep.quotientToInvariants` — is Mathlib's. Mathlib has no notion of a local fundamental class or of class formations; the predicates `IsBase`, `IsUnramOverlayerDatum` and `IsLocalFundamentalClass`, and the carry cocycle `carryFun` they use, are the project's own.
--
--   **Where it is used.** These predicates fix the vocabulary for the local class field theory at a prime $q$ that is cited, rather than reproved, in the project: the normalisation of the invariant map by unramified splitting, in the form of a characterisation of the fundamental class of $L/K$ by inflation of the cyclic carry cocycle of a uniformiser. They underlie the statements about local conditions at auxiliary primes used in the Selmer- and Kummer-theoretic computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_LocalLevel_FundamentalClass.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime]

structure IsBase (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) : Prop where
  le : K ≤ L
  mem_iff : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x

structure IsUnramOverlayerDatum (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] (hLM : L ≤ M)
    (H : Type) [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    (NL Nn : Subgroup H) [NL.Normal] [Nn.Normal] (e : G ≃* H ⧸ NL) (φ : H) (π : (↥M)ˣ) : Prop where
  smul_algebraMap : ∀ (h : H) (x : ℚ_[q]), h • algebraMap ℚ_[q] M x = algebraMap ℚ_[q] M x
  coe_smul_units : ∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M)
  mem_base_iff : ∀ x : M, (x : PadicAlgCl q) ∈ K ↔ ∀ h : H, h • x = x
  mem_layer_iff : ∀ x : M, (x : PadicAlgCl q) ∈ L ↔ ∀ h ∈ NL, h • x = x
  coe_smul_eq : ∀ (g : G) (h : H), (QuotientGroup.mk h : H ⧸ NL) = e g →
    ∀ x : L, ((g • x : L) : PadicAlgCl q) = ((h • (⟨(x : PadicAlgCl q), hLM x.2⟩ : M) : M) : PadicAlgCl q)
  card_quotient : Nat.card (H ⧸ Nn) = Nat.card G
  mem_zpowers : ∀ h : H ⧸ Nn, h ∈ Subgroup.zpowers (QuotientGroup.mk' Nn φ)
  frobenius : ∀ x : M, (∀ h ∈ Nn, h • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
    ‖((φ • x : M) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1
  smul_pi : ∀ h : H, h • π = π
  pi_mem : ((π : M) : PadicAlgCl q) ∈ K
  norm_pi_lt : ‖((π : M) : PadicAlgCl q)‖ < 1
  norm_le_norm_pi : ∀ y : M, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : M) : PadicAlgCl q)‖

namespace IsUnramOverlayerDatum

variable {q}
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G] [MulSemiringAction G L]
    {K : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K]
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}

theorem ofMul_pi_mem (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) :
    (Additive.ofMul π : Rep.ofMulDistribMulAction H (↥M)ˣ) ∈
      Representation.invariants ((Rep.ofMulDistribMulAction H (↥M)ˣ).ρ.comp Nn.subtype) :=
  fun n => congrArg Additive.ofMul (d.smul_pi (n : H))

def piInv (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) : (Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn :=
  ⟨Additive.ofMul π, d.ofMul_pi_mem⟩

theorem piInv_val (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π) :
    (d.piInv.1 : Rep.ofMulDistribMulAction H (↥M)ˣ) = Additive.ofMul π := rfl

end IsUnramOverlayerDatum

def IsLocalFundamentalClass (L : IntermediateField ℚ_[q] (PadicAlgCl q)) (G : Type) [Group G] [MulSemiringAction G L]
    [MulDistribMulAction G (↥L)ˣ] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) : Prop :=
  ∀ (M : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] M] (hLM : L ≤ M)
    (H : Type) [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    (NL Nn : Subgroup H) [NL.Normal] [Nn.Normal] (e : G ≃* H ⧸ NL) (φ : H) (π : (↥M)ˣ)
    (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
    (ι : Rep.res (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction G (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction H (↥M)ˣ),
    (∀ v : (↥L)ˣ, (((Additive.toMul (ι.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q)) →
    ∀ (hfin : IsOfFinOrder (QuotientGroup.mk' Nn φ))
      (hc : carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)),
      (groupCohomology.map (e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) ι 2).hom u =
        ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M)ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥M)ˣ).quotientToInvariants Nn)).hom
            ⟨carryFun (QuotientGroup.mk' Nn φ) d.mem_zpowers hfin d.piInv, hc⟩)

end ExtCitation.LocalLevel


