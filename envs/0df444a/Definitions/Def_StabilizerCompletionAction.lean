-- Prove2me | Definitions.Def_StabilizerCompletionAction
-- name    : StabilizerCompletionAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c7bd0281-655f-51e2-b350-b40c30dcf0a4
-- title:
--   Stabiliser action on the adic completion at an ideal
-- statement:
--   The setting is a commutative ring $A$, a commutative $A$-algebra $B$, a group $G$ acting on $B$ by ring automorphisms in a way commuting with the $A$-action, and an ideal $\mathfrak P \subseteq B$. Taking $G$ to act on ideals of $B$ by the pointwise action, let $S = \mathrm{Stab}_G(\mathfrak P)$ be the stabiliser of $\mathfrak P$. Two preliminary facts are recorded: an element $g \in S$ maps each $x \in \mathfrak P$ into $\mathfrak P$, hence the image $\mathfrak P \cdot$ under the $A$-algebra automorphism $b \mapsto g \cdot b$ of $B$ satisfies $\mathfrak P.\mathrm{map}(g) \le \mathfrak P$; and the inverse of the automorphism attached to $g$ is the automorphism attached to $g^{-1}$.
--
--   From these, `stabAut` attaches to $g \in S$ an $A$-algebra automorphism of the $\mathfrak P$-adic completion $\mathrm{AdicCompletion}\,\mathfrak P\,B$: it is the equivalence obtained from the project's functoriality construction `mapAlgEquiv` applied to the automorphism $b \mapsto g\cdot b$ of $B$, whose two hypotheses $\mathfrak P.\mathrm{map}(g) \le \mathfrak P$ and $\mathfrak P.\mathrm{map}(g^{-1}) \le \mathfrak P$ are exactly the facts just recorded. Its defining property, `evalₐ_stabAut`, is levelwise: if $z \in B$ has class in $B/\mathfrak P^{n}$ equal to the $n$-th component of $x$, then the $n$-th component of $\mathrm{stabAut}(g)(x)$ is the class of $g \cdot z$. The assignment $g \mapsto \mathrm{stabAut}(g)$ is then shown to be a monoid homomorphism `stabilizerToCompletionAut` from $S$ to the group of $A$-algebra automorphisms of $\mathrm{AdicCompletion}\,\mathfrak P\,B$, and `stabilizerMulSemiringAction` is the resulting multiplicative-semiring action of $S$ on the completion, obtained by composing the canonical action of the automorphism group along this homomorphism; it is a named (reducible) definition rather than a global instance. Finally, on canonical images the action is computed: $g$ sends the image of $b \in B$ in the completion to the image of $g \cdot b$.
--
--   **Relation to Mathlib.** Mathlib supplies the adic completion $\mathrm{AdicCompletion}$, the pointwise action of a group on ideals, the automorphism $\mathrm{MulSemiringAction.toAlgEquiv}$ attached to a group element, and the transport of a multiplicative-semiring action along a monoid homomorphism; the functoriality of adic completions in $A$-algebra maps and equivalences used here (`mapₐ`, `mapAlgEquiv`) is the project's own, and so is the induced action of the stabiliser of an ideal on its adic completion.
--
--   **Where it is used.** This is general commutative-algebra infrastructure: the stabiliser of $\mathfrak P$ in $G$ — in the arithmetic case the decomposition group of a prime — acts by $A$-algebra automorphisms on the $\mathfrak P$-adic completion, compatibly with the action on $B$ under the canonical map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_StabilizerCompletionAction.lean

import Definitions.Def_AdicCompletionRingFunctoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u₁ u₂ u₃

open Pointwise

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₂) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable (𝔓 : Ideal B)

theorem smul_mem_of_mem_stabilizer (g : MulAction.stabilizer G 𝔓) {x : B} (hx : x ∈ 𝔓) :
    (g : G) • x ∈ 𝔓 := by
  have h : (g : G) • 𝔓 = 𝔓 := g.2
  have hmem : (g : G) • x ∈ (g : G) • 𝔓 := by
    rw [Ideal.pointwise_smul_def]
    exact Ideal.mem_map_of_mem _ hx
  rwa [h] at hmem

theorem map_toAlgEquiv_le_of_mem_stabilizer (g : MulAction.stabilizer G 𝔓) :
    𝔓.map (MulSemiringAction.toAlgEquiv A B (g : G) : B →ₐ[A] B) ≤ 𝔓 :=
  Ideal.map_le_iff_le_comap.mpr fun _ hx => smul_mem_of_mem_stabilizer B G 𝔓 g hx

theorem toAlgEquiv_symm (g : G) :
    (MulSemiringAction.toAlgEquiv A B g).symm = MulSemiringAction.toAlgEquiv A B g⁻¹ := by
  ext b
  rw [AlgEquiv.symm_apply_eq]
  show b = g • g⁻¹ • b
  rw [smul_inv_smul]

noncomputable def stabAut (g : MulAction.stabilizer G 𝔓) :
    AdicCompletion 𝔓 B ≃ₐ[A] AdicCompletion 𝔓 B :=
  mapAlgEquiv 𝔓 𝔓 (MulSemiringAction.toAlgEquiv A B (g : G))
    (map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g)
    (by rw [toAlgEquiv_symm]
        exact map_toAlgEquiv_le_of_mem_stabilizer A B G 𝔓 g⁻¹)

theorem evalₐ_stabAut (g : MulAction.stabilizer G 𝔓) (n : ℕ) (x : AdicCompletion 𝔓 B)
    (z : B) (hz : Ideal.Quotient.mk (𝔓 ^ n) z = evalₐ 𝔓 n x) :
    evalₐ 𝔓 n (stabAut A B G 𝔓 g x) = Ideal.Quotient.mk (𝔓 ^ n) ((g : G) • z) := by
  rw [stabAut, mapAlgEquiv_apply, evalₐ_mapₐ, ← hz, levelMapₐ_mk]
  rfl

noncomputable def stabilizerToCompletionAut :
    MulAction.stabilizer G 𝔓 →* (AdicCompletion 𝔓 B ≃ₐ[A] AdicCompletion 𝔓 B) where
  toFun := stabAut A B G 𝔓
  map_one' := by
    refine AlgEquiv.ext fun x => ext_evalₐ fun n => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n x)
    rw [evalₐ_stabAut A B G 𝔓 1 n x z hz, AlgEquiv.one_apply, ← hz,
      OneMemClass.coe_one, one_smul]
  map_mul' g₁ g₂ := by
    refine AlgEquiv.ext fun x => ext_evalₐ fun n => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ 𝔓 n x)
    have h₂ : Ideal.Quotient.mk (𝔓 ^ n) ((g₂ : G) • z) =
        evalₐ 𝔓 n (stabAut A B G 𝔓 g₂ x) :=
      (evalₐ_stabAut A B G 𝔓 g₂ n x z hz).symm
    rw [AlgEquiv.mul_apply, evalₐ_stabAut A B G 𝔓 (g₁ * g₂) n x z hz,
      evalₐ_stabAut A B G 𝔓 g₁ n _ ((g₂ : G) • z) h₂, Subgroup.coe_mul, mul_smul]

@[reducible]
noncomputable def stabilizerMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer G 𝔓) (AdicCompletion 𝔓 B) :=
  MulSemiringAction.compHom _ (stabilizerToCompletionAut A B G 𝔓)

@[simp]
theorem stabilizerToCompletionAut_of (g : MulAction.stabilizer G 𝔓) (b : B) :
    stabilizerToCompletionAut A B G 𝔓 g (of 𝔓 B b) = of 𝔓 B ((g : G) • b) := by
  show stabAut A B G 𝔓 g (of 𝔓 B b) = _
  rw [stabAut, mapAlgEquiv_apply, mapₐ_of]
  rfl

end AdicCompletion

set_option pp.universes true in
#check @AdicCompletion.stabilizerMulSemiringAction
set_option pp.universes true in
#check @AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.smul_mem_of_mem_stabilizer
#print axioms AdicCompletion.map_toAlgEquiv_le_of_mem_stabilizer
#print axioms AdicCompletion.toAlgEquiv_symm
#print axioms AdicCompletion.stabAut
#print axioms AdicCompletion.evalₐ_stabAut
#print axioms AdicCompletion.stabilizerToCompletionAut
#print axioms AdicCompletion.stabilizerMulSemiringAction
#print axioms AdicCompletion.stabilizerToCompletionAut_of


