-- Prove2me | Definitions.Def_GroupCohomology_SplittingModule
-- name    : GroupCohomology_SplittingModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d127639d-b796-58c0-9c36-e8a34298ab40
-- title:
--   Augmentation ideal and splitting module of a 2-cocycle
-- statement:
--   Throughout, $k$ is a commutative ring and $G$ a group, and representations are objects of `Rep k G` built on the $\mathrm{Finsupp}$ model $G \to_0 k$ of the group algebra. The first group of declarations sets up the augmentation. [`Rep.augε`](../def/GroupCohomology_SplittingModule.html#L18) is the morphism $k[G] \to k$ from the left regular representation to the trivial representation on $k$ determined by sending the basis vector $\delta_g$ to $1$; `augε_hom_apply` identifies it with $f \mapsto \sum_{g} f(g)$. [`Rep.augIdeal k G`](../def/GroupCohomology_SplittingModule.html#L21) is the subrepresentation of $k[G]$ carried by $\ker \varepsilon$ (stability under the action being part of the definition), `mem_augIdeal_iff` restates membership as vanishing of the coefficient sum, and `coe_augIdeal_ρ_apply` records that $\sigma$ acts by translating supports, $f \mapsto f \circ (\sigma^{-1}\cdot)$ in the form `Finsupp.lmapDomain` along $\sigma\cdot$. [`Rep.augIdealι`](../def/GroupCohomology_SplittingModule.html#L27) is the inclusion and [`Rep.augShortComplex k G`](../def/GroupCohomology_SplittingModule.html#L30) is the short complex $I_G \to k[G] \xrightarrow{\varepsilon} k$ in `Rep k G`, with the vanishing of the composite as its field (no exactness is asserted).
--
--   The second group fixes a representation $C$ and an inhomogeneous $2$-cocycle $\varphi \in$ `groupCohomology.cocycles₂ C`. For $\sigma \in G$, [`Rep.cocycleTwist C φ σ`](../def/GroupCohomology_SplittingModule.html#L64) is the $k$-linear map $k[G] \to C$, $f \mapsto \sum_{\tau} f(\tau)\,\varphi(\sigma,\tau)$. Two consequences of the cocycle identity are proved: $\varphi(1,\tau) = \varphi(1,1)$ for all $\tau$, whence the twist by $\sigma = 1$ kills every element of augmentation zero; and, on elements of augmentation zero, $\mathrm{tw}_{\sigma\sigma'}(f) = \sigma\,\mathrm{tw}_{\sigma'}(f) + \mathrm{tw}_{\sigma}(\sigma' f)$. These are exactly what makes [`Rep.splittingRep C φ`](../def/GroupCohomology_SplittingModule.html#L107) a representation of $G$ on $C \times I_G$, namely $\sigma\cdot(c,f) = \bigl(\sigma c + \sum_{\tau} f(\tau)\varphi(\sigma,\tau),\ \sigma f\bigr)$; [`Rep.splittingModule C φ`](../def/GroupCohomology_SplittingModule.html#L124) is the corresponding object of `Rep k G`, with `splittingModule_ρ_apply` recording the formula. Finally [`Rep.splittingModuleι`](../def/GroupCohomology_SplittingModule.html#L129) is $c \mapsto (c,0)$, [`Rep.splittingModuleπ`](../def/GroupCohomology_SplittingModule.html#L134) is $(c,f) \mapsto f$, and [`Rep.splittingShortComplex C φ`](../def/GroupCohomology_SplittingModule.html#L140) is the short complex $C \to C(\varphi) \to I_G$ they form.
--
--   **Relation to Mathlib.** The cocycles are Mathlib's inhomogeneous `groupCohomology.cocycles₂`; the ambient group algebra is the `Finsupp`-based left regular representation [`Rep.leftRegularFinsupp`](../def/Compat_Mathlib430.html#L103) vendored in the project's compatibility module (a copy of an earlier Mathlib definition kept under a new name) rather than Mathlib's `MonoidAlgebra`-based `Rep.leftRegular`. Mathlib has no augmentation ideal in `Rep k G` and no splitting module of a $2$-cocycle; both are the project's own.
--
--   **Where it is used.** The augmentation sequence and the splitting module provide the explicit extension realising a given $2$-cocycle class, used in the dimension-shifting arguments for group cohomology that make a prescribed degree-two class vanish after enlarging the coefficient module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_SplittingModule.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

section Augmentation

variable (k G : Type u) [CommRing k] [Group G]

abbrev augε : Rep.leftRegularFinsupp k G ⟶ Rep.trivial k G k :=
  Rep.leftRegularHomFinsupp (Rep.trivial k G k) (1 : k)

abbrev augIdeal : Rep k G :=
  Rep.of (Representation.subrepresentation (Rep.leftRegularFinsupp k G).ρ
    (LinearMap.ker (augε k G).hom.toLinearMap) fun g x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
      rw [Rep.hom_comm_apply, hx, map_zero])

abbrev augIdealι : augIdeal k G ⟶ Rep.leftRegularFinsupp k G :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

def augShortComplex : ShortComplex (Rep k G) where
  X₁ := augIdeal k G
  X₂ := Rep.leftRegularFinsupp k G
  X₃ := Rep.trivial k G k
  f := augIdealι k G
  g := augε k G
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

@[simp] lemma augShortComplex_X₁ : (augShortComplex k G).X₁ = augIdeal k G := rfl
@[simp] lemma augShortComplex_X₂ : (augShortComplex k G).X₂ = Rep.leftRegularFinsupp k G := rfl
@[simp] lemma augShortComplex_X₃ : (augShortComplex k G).X₃ = Rep.trivial k G k := rfl
@[simp] lemma augShortComplex_f : (augShortComplex k G).f = augIdealι k G := rfl
@[simp] lemma augShortComplex_g : (augShortComplex k G).g = augε k G := rfl

variable {k G}

lemma augε_hom_apply (f : G →₀ k) : (augε k G).hom f = Finsupp.linearCombination k (fun _ : G => (1 : k)) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single g r => rw [Rep.leftRegularHomFinsupp_hom_single, Finsupp.linearCombination_single]; rfl

lemma mem_augIdeal_iff (f : G →₀ k) :
    f ∈ LinearMap.ker (augε k G).hom.toLinearMap ↔ Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 := by
  rw [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply, augε_hom_apply]

lemma coe_augIdeal_ρ_apply (σ : G) (f : augIdeal k G) : ((augIdeal k G).ρ σ f : G →₀ k) = Finsupp.lmapDomain k k (σ * ·) (f : G →₀ k) := rfl

end Augmentation

section Splitting

variable {k G : Type u} [CommRing k] [Group G] (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C)

def cocycleTwist (σ : G) : (G →₀ k) →ₗ[k] C :=
  Finsupp.linearCombination k (fun τ : G => (φ : G × G → C) (σ, τ))

@[simp] lemma cocycleTwist_single (σ τ : G) (r : k) :
    cocycleTwist C φ σ (Finsupp.single τ r) = r • (φ : G × G → C) (σ, τ) := by
  rw [cocycleTwist, Finsupp.linearCombination_single]

lemma cocycleTwist_apply (σ : G) (f : G →₀ k) :
    cocycleTwist C φ σ f = f.sum fun τ r => r • (φ : G × G → C) (σ, τ) :=
  Finsupp.linearCombination_apply _ _

lemma cocycles₂_one_left (τ : G) : (φ : G × G → C) (1, τ) = (φ : G × G → C) (1, 1) := by
  have h := (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2 1 1 τ
  rw [one_mul, one_mul, map_one] at h
  change (φ : G × G → C) (1, τ) + (φ : G × G → C) (1, 1) = (φ : G × G → C) (1, τ) + (φ : G × G → C) (1, τ) at h
  exact (add_left_cancel h).symm

lemma cocycleTwist_one (f : G →₀ k) (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    cocycleTwist C φ 1 f = 0 := by
  rw [cocycleTwist_apply, Finsupp.sum, Finset.sum_congr rfl fun τ _ => by rw [cocycles₂_one_left C φ τ], ← Finset.sum_smul]
  change (f.sum fun _ r => r) • (φ : G × G → C) (1, 1) = 0
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul]

lemma cocycleTwist_mul (σ σ' : G) (f : G →₀ k) (hf : Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0) :
    cocycleTwist C φ (σ * σ') f = C.ρ σ (cocycleTwist C φ σ' f) + cocycleTwist C φ σ (Finsupp.lmapDomain k k (σ' * ·) f) := by
  have hx : ∀ g h l : G, (φ : G × G → C) (g * h, l) + (φ : G × G → C) (g, h) =
      C.ρ g ((φ : G × G → C) (h, l)) + (φ : G × G → C) (g, h * l) :=
    (groupCohomology.mem_cocycles₂_iff (φ : G × G → C)).1 φ.2
  have h2 : cocycleTwist C φ σ (Finsupp.lmapDomain k k (σ' * ·) f) = f.sum fun τ r => r • (φ : G × G → C) (σ, σ' * τ) := by
    rw [cocycleTwist, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    rfl
  rw [h2, cocycleTwist_apply, cocycleTwist_apply]
  simp only [Finsupp.sum]
  rw [map_sum, ← Finset.sum_add_distrib]
  have h3 : ∀ τ, f τ • (φ : G × G → C) (σ * σ', τ) + f τ • (φ : G × G → C) (σ, σ') =
      C.ρ σ (f τ • (φ : G × G → C) (σ', τ)) + f τ • (φ : G × G → C) (σ, σ' * τ) := fun τ => by
    rw [map_smul, ← smul_add, ← smul_add, hx σ σ' τ]
  rw [← Finset.sum_congr rfl fun τ _ => h3 τ, Finset.sum_add_distrib, ← Finset.sum_smul]
  change _ = _ + (f.sum fun _ r => r) • (φ : G × G → C) (σ, σ')
  rw [show (f.sum fun _ r => r) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f by
    simp [Finsupp.linearCombination_apply], hf, zero_smul, add_zero]

def splittingRep : Representation k G (C × augIdeal k G) where
  toFun σ := LinearMap.prod
    (C.ρ σ ∘ₗ LinearMap.fst k C (augIdeal k G) +
      cocycleTwist C φ σ ∘ₗ (LinearMap.ker (augε k G).hom.toLinearMap).subtype ∘ₗ LinearMap.snd k C (augIdeal k G))
    ((augIdeal k G).ρ σ ∘ₗ LinearMap.snd k C (augIdeal k G))
  map_one' := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ 1 v.1 + cocycleTwist C φ 1 (v.2 : G →₀ k) = v.1
      rw [map_one, cocycleTwist_one C φ _ ((mem_augIdeal_iff _).1 v.2.2), add_zero]; rfl)
    (by change (augIdeal k G).ρ 1 v.2 = v.2; rw [map_one]; rfl)
  map_mul' σ σ' := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ (σ * σ') v.1 + cocycleTwist C φ (σ * σ') (v.2 : G →₀ k) =
        C.ρ σ (C.ρ σ' v.1 + cocycleTwist C φ σ' (v.2 : G →₀ k)) + cocycleTwist C φ σ (((augIdeal k G).ρ σ' v.2 : augIdeal k G) : G →₀ k)
      rw [map_mul, map_add, cocycleTwist_mul C φ σ σ' _ ((mem_augIdeal_iff _).1 v.2.2), add_assoc, coe_augIdeal_ρ_apply]; rfl)
    (by change (augIdeal k G).ρ (σ * σ') v.2 = (augIdeal k G).ρ σ ((augIdeal k G).ρ σ' v.2); rw [map_mul]; rfl)

abbrev splittingModule : Rep k G := Rep.of (splittingRep C φ)

lemma splittingModule_ρ_apply (σ : G) (v : C × augIdeal k G) :
    (splittingModule C φ).ρ σ v = (C.ρ σ v.1 + cocycleTwist C φ σ (v.2 : G →₀ k), (augIdeal k G).ρ σ v.2) := rfl

def splittingModuleι : C ⟶ splittingModule C φ :=
  Rep.ofHom ⟨LinearMap.inl k C (augIdeal k G), fun σ => LinearMap.ext fun c => Prod.ext
    (by change C.ρ σ c = C.ρ σ c + cocycleTwist C φ σ ((0 : augIdeal k G) : G →₀ k); rw [ZeroMemClass.coe_zero, map_zero, add_zero])
    (by change (0 : augIdeal k G) = (augIdeal k G).ρ σ 0; rw [map_zero])⟩

def splittingModuleπ : splittingModule C φ ⟶ augIdeal k G :=
  Rep.ofHom ⟨LinearMap.snd k C (augIdeal k G), fun _ => LinearMap.ext fun _ => rfl⟩

@[simp] lemma splittingModuleι_hom_apply (c : C) : (splittingModuleι C φ).hom c = ((c, 0) : C × augIdeal k G) := rfl
@[simp] lemma splittingModuleπ_hom_apply (v : C × augIdeal k G) : (splittingModuleπ C φ).hom v = v.2 := rfl

def splittingShortComplex : ShortComplex (Rep k G) where
  X₁ := C
  X₂ := splittingModule C φ
  X₃ := augIdeal k G
  f := splittingModuleι C φ
  g := splittingModuleπ C φ
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

@[simp] lemma splittingShortComplex_X₁ : (splittingShortComplex C φ).X₁ = C := rfl
@[simp] lemma splittingShortComplex_X₂ : (splittingShortComplex C φ).X₂ = splittingModule C φ := rfl
@[simp] lemma splittingShortComplex_X₃ : (splittingShortComplex C φ).X₃ = augIdeal k G := rfl
@[simp] lemma splittingShortComplex_f : (splittingShortComplex C φ).f = splittingModuleι C φ := rfl
@[simp] lemma splittingShortComplex_g : (splittingShortComplex C φ).g = splittingModuleπ C φ := rfl

end Splitting

end Rep

end


