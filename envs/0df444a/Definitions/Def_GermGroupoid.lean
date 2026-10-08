-- Prove2me | Definitions.Def_GermGroupoid
-- name    : GermGroupoid
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-06T17:06:08.253979+00:00
-- url     : https://prove2.me/theorems/8c4f9e4d-0d76-4923-b830-f48a5978384e
-- title:
--   Groupoids of germs — germs in a pseudogroup, the topological full group, the group of germs at a point
-- statement:
--   Germs of homeomorphisms of a topological space $X$, after Juschenko, Nekrashevych and de la Salle (§1, p. 2, and §3.1, p. 6).
--
--   A groupoid of germs of homeomorphisms of $X$ is given by a pseudogroup $\mathcal H$: a Mathlib `StructureGroupoid X`, a set of homeomorphisms between open subsets of $X$ (`OpenPartialHomeomorph X X`) that contains the identity and is closed under composition, inverses, and gluing of local pieces. Its germs are the germs of its members. The groupoids of germs represented this way are the open ones in the topology of JNdlS §3.1 (“The groupoid of germs has a natural topology defined by the basis of open sets of the form $\{(g, x) : x \in U\}$”), since with the germ of a member at $x$ it contains the germs of that member at the nearby points.
--
--   - `GermMem 𝓗 f x`: the germ of the homeomorphism $f$ of $X$ at $x$ belongs to $\mathcal H$, that is, some member $e$ of $\mathcal H$ is defined at $x$ and agrees with $f$ on a neighbourhood of $x$. JNdlS p. 6: “Let $G$ be a group acting faithfully by homeomorphisms on a topological space $\mathcal X$. A germ of the action is an equivalence class of pairs $(g, x) \in G \times X$, where two germs $(g_1, x_1)$ and $(g_2, x_2)$ are equal if and only if $x_1 = x_2$, and there exists a neighborhood $U$ of $x_1$ such that $g_1|_U = g_2|_U$.”
--   - `fullGroup 𝓗`, the topological full group $[[\mathcal H]]$: the homeomorphisms of $X$ all of whose germs belong to $\mathcal H$, as a subgroup of `X ≃ₜ X`. JNdlS p. 6: “The topological full group of a groupoid of germs $\mathcal G$, denoted $[[\mathcal G]]$ is the set of all homeomorphisms $F : X \to X$ such that all germs of $F$ belong to $\mathcal G$.”
--   - `germKernel G x` and `GermGroup G x`, for a group $G$ of homeomorphisms of $X$ (a subgroup of `X ≃ₜ X`): the elements of the stabilizer of $x$ that act trivially on a neighbourhood of $x$, a normal subgroup of the stabilizer, and the quotient, the group of germs of $G$ at $x$. JNdlS p. 2: “If $G$ is a group acting by homeomorphisms on a topological space $\mathcal X$, then by $[[G]]$ we denote the full topological group of the action, […]. For $x \in \mathcal X$ the group of germs of $G$ at $x$ is the quotient of the stabilizer of $x$ by the subgroup of elements acting trivially on a neighborhood of $x$.” On p. 6 this is the isotropy group $\mathcal G_x$ of the groupoid of germs of $G$.
--
--   Homeomorphisms act on $X$ by evaluation (`HomeomorphAction.applyMulAction`), and a subgroup $G$ acts through it.
-- source:
--   Juschenko, K., Nekrashevych, V. and de la Salle, M., Extensions of amenable groups by recurrent groupoids, Invent. Math. 206 (2016) 837–867, https://doi.org/10.1007/s00222-016-0664-6 (arXiv:1305.2637v2, whose page numbers are used), §1, p. 2, and §3.1, p. 6 (germs, groupoids of germs, the topological full group, the group of germs at a point)

import Definitions.Def_HomeomorphAction
import Mathlib

/-!
# Groupoids of germs and topological full groups

K. Juschenko, V. Nekrashevych and M. de la Salle, *Extensions of amenable groups by recurrent
groupoids*, Invent. Math. 206 (2016) 837–867 (arXiv:1305.2637v2, whose page numbers are used),
§3.1, p. 6; K. Juschenko, N. Matte Bon, N. Monod and M. de la Salle, *Extensive amenability and
an application to interval exchanges*, Ergodic Theory Dynam. Systems 38 (2018) 195–219
(arXiv:1503.04977v1), p. 23.

A groupoid of germs of homeomorphisms of `X` is given by a pseudogroup: a Mathlib
`StructureGroupoid X`, a set of homeomorphisms between open subsets of `X` closed under
composition, inverses and gluing. Its germs are the germs of its members.
-/

namespace GermGroupoid

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- JNdlS §3.1: the germ of the homeomorphism `f` at `x` belongs to the groupoid of germs of the
pseudogroup `𝓗`: near `x`, `f` agrees with a member of `𝓗` whose domain contains `x`. -/
def GermMem (𝓗 : StructureGroupoid X) (f : X ≃ₜ X) (x : X) : Prop :=
  ∃ e ∈ 𝓗, x ∈ e.source ∧ ∀ᶠ y in 𝓝 x, f y = e y

/-- JNdlS §3.1, p. 6: the topological full group `[[𝓗]]`, the homeomorphisms of `X` all of whose
germs belong to `𝓗`. -/
def fullGroup (𝓗 : StructureGroupoid X) : Subgroup (X ≃ₜ X) where
  carrier := {f | ∀ x, GermMem 𝓗 f x}
  one_mem' x := ⟨OpenPartialHomeomorph.refl X, 𝓗.id_mem, by simp,
    Filter.Eventually.of_forall fun _ => rfl⟩
  mul_mem' {f g} hf hg x := by
    obtain ⟨e₂, he₂, hx₂, hg₂⟩ := hg x
    obtain ⟨e₁, he₁, hx₁, hf₁⟩ := hf (g x)
    have hgx : g x = e₂ x := hg₂.self_of_nhds
    refine ⟨e₂.trans e₁, 𝓗.trans he₂ he₁, ?_, ?_⟩
    · simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨hx₂, hgx ▸ hx₁⟩
    · have hcont : Filter.Tendsto g (𝓝 x) (𝓝 (g x)) := g.continuous.tendsto x
      filter_upwards [hg₂, hcont.eventually hf₁] with y hy hfy
      change f (g y) = e₁ (e₂ y)
      rw [hfy, hy]
  inv_mem' {f} hf x := by
    obtain ⟨e, he, hxe, hfe⟩ := hf (f.symm x)
    have hfx : f (f.symm x) = e (f.symm x) := hfe.self_of_nhds
    simp only [Homeomorph.apply_symm_apply] at hfx
    refine ⟨e.symm, 𝓗.symm he, ?_, ?_⟩
    · simp only [OpenPartialHomeomorph.symm_source]
      rw [hfx]
      exact e.map_source hxe
    · have hU : {y | f y = e y} ∩ e.source ∈ 𝓝 (f.symm x) :=
        Filter.inter_mem hfe (e.open_source.mem_nhds hxe)
      have hV : f '' ({y | f y = e y} ∩ e.source) ∈ 𝓝 x := by
        have := f.isOpenMap.image_mem_nhds hU
        simpa using this
      filter_upwards [hV] with z hz
      obtain ⟨y, ⟨hy, hys⟩, rfl⟩ := hz
      show f.symm (f y) = e.symm (f y)
      rw [Homeomorph.symm_apply_apply, show f y = e y from hy, e.left_inv hys]

/-- The elements of `G` fixing `x` that act trivially on a neighbourhood of `x`. -/
def germKernel (G : Subgroup (X ≃ₜ X)) (x : X) : Subgroup (MulAction.stabilizer G x) where
  carrier := {g | ∀ᶠ y in 𝓝 x, ((g : G) : X ≃ₜ X) y = y}
  one_mem' := Filter.Eventually.of_forall fun _ => rfl
  mul_mem' {a b} ha hb := by
    have hb' : Filter.Tendsto ((b : G) : X ≃ₜ X) (𝓝 x) (𝓝 x) := by
      have h := ((b : G) : X ≃ₜ X).continuous.tendsto x
      have hbx : ((b : G) : X ≃ₜ X) x = x := b.2
      rwa [hbx] at h
    filter_upwards [hb, hb'.eventually ha] with y hy hay
    show ((a : G) : X ≃ₜ X) (((b : G) : X ≃ₜ X) y) = y
    rw [hy, show ((a : G) : X ≃ₜ X) y = y by rw [← hy]; exact hay]
  inv_mem' {a} ha := by
    filter_upwards [ha] with y hy
    show ((a : G) : X ≃ₜ X).symm y = y
    conv_lhs => rw [← hy]
    exact ((a : G) : X ≃ₜ X).symm_apply_apply y

instance (G : Subgroup (X ≃ₜ X)) (x : X) : (germKernel G x).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hgx : ((g : G) : X ≃ₜ X) x = x := g.2
  have hg : Filter.Tendsto ((g : G) : X ≃ₜ X).symm (𝓝 x) (𝓝 x) := by
    have h := ((g : G) : X ≃ₜ X).symm.continuous.tendsto x
    have : ((g : G) : X ≃ₜ X).symm x = x :=
      (((g : G) : X ≃ₜ X).symm_apply_eq).2 hgx.symm
    rwa [this] at h
  have hn' : ∀ᶠ y in 𝓝 x, ((n : G) : X ≃ₜ X) y = y := hn
  show ∀ᶠ y in 𝓝 x, ((g * n * g⁻¹ : MulAction.stabilizer G x) : X ≃ₜ X) y = y
  filter_upwards [hg.eventually hn'] with y hy
  change ((g : G) : X ≃ₜ X) (((n : G) : X ≃ₜ X) (((g : G) : X ≃ₜ X).symm y)) = y
  rw [hy, Homeomorph.apply_symm_apply]

/-- JNdlS §1, p. 2, and §3.1, p. 6: the group of germs of `G` at `x` (the isotropy group of the
groupoid of germs of `G` at `x`): the stabilizer of `x` in `G` modulo the elements acting
trivially on a neighbourhood of `x`. -/
abbrev GermGroup (G : Subgroup (X ≃ₜ X)) (x : X) : Type _ :=
  MulAction.stabilizer G x ⧸ germKernel G x

end GermGroupoid


