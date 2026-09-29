-- Prove2me | Definitions.Def_GroupCohomology_Selmer
-- name    : GroupCohomology_Selmer
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/8484e8db-fa88-5be6-9ae5-a059bb1aacd9
-- title:
--   Twisted duals, Selmer submodules, Greenberg–Wiles formula
-- statement:
--   Over a commutative semiring $k$ and a monoid $G$, [`Representation.twist ρ χ`](../def/GroupCohomology_Selmer.html#L15) sends $g$ to $\chi(g)\cdot\rho(g)$ for a character $\chi : G \to k^\times$; twisting by the trivial character returns $\rho$. For $A : \mathrm{Rep}\,k\,G$ with $G$ a group, [`Rep.twist`](../def/GroupCohomology_Selmer.html#L38) and [`Rep.dualTwist`](../def/GroupCohomology_Selmer.html#L41) package $\rho$ and its Mathlib dual twisted by $\chi$, so that the action on $f \in \mathrm{Dual}_k A$ is $g \mapsto \chi(g)\cdot (f \circ \rho(g^{-1}))$; over a field and in finite dimension the twisted dual has the same rank as $A$.
--
--   In the cohomological part, $k$ is a field, $\Gamma$ a group, $\iota$ a finite index type, and $\mathrm{loc}_v : \Gamma_v \to \Gamma$ a family of homomorphisms; $M$ is a $k$-linear representation of $\Gamma$. `locRes` is the map $H^1(\Gamma, M) \to H^1(\Gamma_v, M)$ induced in degree $1$ by $\mathrm{loc}_v$ together with the identity on the restricted representation. Given local conditions $\mathcal{L}_v \subseteq H^1(\Gamma_v, M)$, `selmer` is the intersection over $v$ of the preimages of $\mathcal{L}_v$, i.e. the classes restricting into every $\mathcal{L}_v$; it is monotone in the family $\mathcal{L}$. For a bilinear pairing $B : V \times W \to k$, `orthogonal B L` is the submodule of $w \in W$ with $B(x,w)=0$ for all $x \in L$ (the preimage of the dual annihilator of $L$ under the flip of $B$); it is antitone and sends $\bot$ to $\top$. With a second representation $M'$ and a family of local pairings $H^1(\Gamma_v,M) \times H^1(\Gamma_v,M') \to k$, `dualConditions` is $\mathcal{L}_v^{\perp}$.
--
--   `greenbergWilesEq` is the proposition that
--   $$\dim H^1_{\mathcal{L}}(M) + \dim (M')^{\Gamma} + \sum_v \dim M^{\Gamma_v} = \dim H^1_{\mathcal{L}^{\perp}}(M') + \dim M^{\Gamma} + \sum_v \dim \mathcal{L}_v,$$
--   with all dimensions taken as `finrank` (hence $0$ when infinite). `IsGreenbergWilesDatum` is a structure whose fields are finite-dimensionality of the two Selmer submodules and of each $\mathcal{L}_v$, together with this equation as a field. From such a datum one obtains the inequality $\dim H^1_{\mathcal{L}}(M) \le \dim H^1_{\mathcal{L}^{\perp}}(M') + \dim M^{\Gamma} + \sum_v \dim \mathcal{L}_v$, by discarding the two remaining nonnegative terms of the equation. Finally, `localTermBalanced` is the predicate $\dim \mathcal{L}_v = \dim M^{\Gamma_v}$ for all $v$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Rep`, `Representation.dual`, group cohomology `H1` with its functoriality map, and `Submodule.dualAnnihilator`. The character twist of a representation, the Selmer submodule attached to a family of local conditions, the orthogonal complement with respect to an arbitrary bilinear pairing, and the Greenberg–Wiles equation with its datum structure are the project's own; Mathlib has no Selmer groups in group cohomology.
--
--   **Where it is used.** These are the carrier definitions for the global-duality bookkeeping: Selmer groups cut out by local conditions, their duals under local pairings, and the Euler-characteristic identity comparing a Selmer group with the dual Selmer group. They are used where dimension counts for Selmer groups are needed, in particular in the numerology of Taylor–Wiles patching and in the dual Selmer group bounds feeding the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_Selmer.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm]

lemma twist_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    ρ.twist χ g = (χ g : k) • ρ g := rfl

lemma twist_apply_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (v : V) :
    ρ.twist χ g v = (χ g : k) • ρ g v := rfl

@[simp]
lemma twist_one (ρ : Representation k G V) : ρ.twist 1 = ρ := by
  ext g v
  simp [twist_apply_apply]

end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev twist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.twist χ)

noncomputable abbrev dualTwist (A : Rep k G) (χ : G →* kˣ) : Rep k G :=
  Rep.of (A.ρ.dual.twist χ)

lemma dualTwist_ρ_apply (A : Rep k G) (χ : G →* kˣ) (g : G) (f : Module.Dual k A) :
    (A.dualTwist χ).ρ g f = (χ g : k) • (f ∘ₗ A.ρ g⁻¹) := rfl

lemma finrank_dualTwist (k : Type u) [Field k] {G : Type u} [Group G] (A : Rep k G)
    (χ : G →* kˣ) [FiniteDimensional k A] :
    finrank k (A.dualTwist χ) = finrank k A :=
  Subspace.dual_finrank_eq

end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable abbrev locRes (v : ι) : H1 M ⟶ H1 (Rep.res (loc v) M) :=
  map (loc v) (𝟙 (Rep.res (loc v) M)) 1

noncomputable def selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Submodule k (H1 M) :=
  ⨅ v, (L v).comap (locRes loc M v).hom

omit [Fintype ι] in
lemma mem_selmer_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (x : H1 M) :
    x ∈ selmer loc M L ↔ ∀ v, (locRes loc M v).hom x ∈ L v := by
  simp [selmer, Submodule.mem_iInf]

omit [Fintype ι] in

lemma selmer_mono {L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : ∀ v, L v ≤ L' v) : selmer loc M L ≤ selmer loc M L' :=
  iInf_mono fun v => Submodule.comap_mono (h v)

omit [Fintype ι] in

lemma selmer_bot_le (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmer loc M (fun _ => ⊥) ≤ selmer loc M L :=
  selmer_mono loc M fun _ => bot_le

omit [Fintype ι] in

lemma subsingleton_selmer_of_subsingleton (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    [Subsingleton (H1 M)] : Subsingleton (selmer loc M L) :=
  inferInstance

def orthogonal {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) : Submodule k W :=
  L.dualAnnihilator.comap B.flip

@[simp]
lemma mem_orthogonal_iff {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) (w : W) :
    w ∈ orthogonal B L ↔ ∀ x ∈ L, B x w = 0 := by
  simp only [orthogonal, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  exact forall₂_congr fun x _ => by rw [LinearMap.flip_apply]

@[simp]
lemma orthogonal_bot {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) : orthogonal B (⊥ : Submodule k V) = ⊤ := by
  ext w
  simp only [mem_orthogonal_iff, Submodule.mem_top, iff_true]
  rintro x rfl
  simp

lemma orthogonal_anti {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (B : V →ₗ[k] W →ₗ[k] k) {L L' : Submodule k V} (h : L ≤ L') :
    orthogonal B L' ≤ orthogonal B L :=
  Submodule.comap_mono (Submodule.dualAnnihilator_anti h)

variable (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def dualConditions (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M')) :=
  orthogonal (pairing v) (L v)

def greenbergWilesEq (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    = finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

structure IsGreenbergWilesDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  formula : greenbergWilesEq loc M M' pairing L

theorem finrank_selmer_le_of_isGreenbergWilesDatum
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    finrank k (selmer loc M L)
      ≤ finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + finrank k M.ρ.invariants + ∑ v, finrank k (L v) := by
  have := h.formula
  unfold greenbergWilesEq at this
  omega

def localTermBalanced (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  ∀ v, finrank k (L v) = finrank k (Rep.res (loc v) M).ρ.invariants

end groupCohomology


