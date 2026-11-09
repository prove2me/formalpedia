-- Prove2me | Definitions.Def_PhyloCSP_AutF
-- name    : PhyloCSP_AutF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:53.300246+00:00
-- url     : https://prove2.me/theorems/ca592175-3c8a-4962-9818-ca7d3380df98
-- title:
--   The automorphism group $\mathrm{Aut}(\mathcal F)$ with the pointwise topology
-- statement:
--   $\mathrm{Aut}(\mathcal F)$ is the group of permutations $g$ of $Z$ preserving the relation $C$ of the concrete Fraïssé limit in both directions, $C(g a;g b,g c)=C(a;b,c)$. It carries the **topology of pointwise convergence**: a basic neighborhood of $g$ consists of the automorphisms agreeing with $g$ on a given finite subset of $Z$.
--
--   With this topology $\mathrm{Aut}(\mathcal F)$ is a topological group (composition and inversion are continuous; proved in the module). It acts on random relations on $Z$, and invariance under this action is the central notion of Sections 7–12.
--
--   **Formalization Note** The topology is induced from the product of discrete topologies on $Z^Z$.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.2, p.18 (PDF p.20); Section 7.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PhyloCSP_fraisseRel

set_option autoImplicit false

namespace PhyloCSP

/-- **The automorphism group `Aut(F)` with the topology of pointwise convergence.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.2, p.18 (PDF p.20): "An automorphism is an
isomorphism from a structure to itself, that is, a permutation of its domain preserving both the
truth and falsity of the relation." Section 7.1, p.19 (PDF p.21): "We give Aut(F) the topology of
pointwise convergence: a basic neighborhood of g consists of the automorphisms agreeing with g on a
specified finite subset of Z."

**Formalization Note.** `F` is the concrete structure `(Z, fraisseRel)` of Definition 7.5. The
topology is induced by `g ↦ (g : Z → Z)` from the product of discrete topologies on `Z`. -/
def AutF : Subgroup (Equiv.Perm Z) where
  carrier := {g | ∀ a b c, fraisseRel (g a) (g b) (g c) = fraisseRel a b c}
  mul_mem' := by
    intro g h hg hh a b c
    simp only [Set.mem_ofPred_eq, Equiv.Perm.coe_mul, Function.comp_apply] at *
    rw [hg, hh]
  one_mem' := by
    intro a b c
    rfl
  inv_mem' := by
    intro g hg a b c
    simp only [Set.mem_ofPred_eq] at *
    have := hg (g⁻¹ a) (g⁻¹ b) (g⁻¹ c)
    simp only [Equiv.apply_symm_apply, Equiv.Perm.inv_def] at this ⊢
    exact this.symm

/-- The topology of pointwise convergence on `Aut(F)`. -/
instance : TopologicalSpace AutF :=
  TopologicalSpace.induced (fun g : AutF => ((g : Equiv.Perm Z) : Z → Z)) inferInstance

/-- "Composition and inversion are continuous in this topology, making Aut(F) a topological group"
(p.19): proved, not assumed. -/
instance : IsTopologicalGroup AutF := by
  have hc : Continuous (fun g : AutF => ((g : Equiv.Perm Z) : Z → Z)) := continuous_induced_dom
  have key : ∀ (z : Z), Continuous (fun g : AutF => (g : Equiv.Perm Z) z) :=
    fun z => (continuous_apply z).comp hc
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · refine continuous_induced_rng.2 (continuous_pi fun z => ?_)
    rw [continuous_discrete_rng]
    intro b
    show IsOpen ((fun p : AutF × AutF => ((p.1 * p.2 : AutF) : Equiv.Perm Z) z) ⁻¹' {b})
    have : (fun p : AutF × AutF => ((p.1 * p.2 : AutF) : Equiv.Perm Z) z) ⁻¹' {b} =
        ⋃ c : Z, (fun p : AutF × AutF => (p.2 : Equiv.Perm Z) z) ⁻¹' {c} ∩
          (fun p : AutF × AutF => (p.1 : Equiv.Perm Z) c) ⁻¹' {b} := by
      ext p; simp [Equiv.Perm.mul_apply]
    rw [this]
    refine isOpen_iUnion fun c => IsOpen.inter ?_ ?_
    · exact (continuous_discrete_rng.1 ((key z).comp continuous_snd)) c
    · exact (continuous_discrete_rng.1 ((key c).comp continuous_fst)) b
  · refine continuous_induced_rng.2 (continuous_pi fun z => ?_)
    rw [continuous_discrete_rng]
    intro b
    show IsOpen ((fun g : AutF => ((g⁻¹ : AutF) : Equiv.Perm Z) z) ⁻¹' {b})
    have : (fun g : AutF => ((g⁻¹ : AutF) : Equiv.Perm Z) z) ⁻¹' {b} =
        (fun g : AutF => (g : Equiv.Perm Z) b) ⁻¹' {z} := by
      ext g; simp only [Set.mem_preimage, Set.mem_singleton_iff, Subgroup.coe_inv, Equiv.Perm.inv_def]
      rw [Equiv.symm_apply_eq, eq_comm]
    rw [this]
    exact continuous_discrete_rng.1 (key b) z

end PhyloCSP


