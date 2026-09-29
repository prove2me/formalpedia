-- Prove2me | Definitions.Def_Mathlib_Algebra_IsDirectLimit
-- name    : Mathlib_Algebra_IsDirectLimit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/8eba4001-63d6-5fce-bd73-26caad936aec
-- title:
--   A predicate characterising direct limits of directed systems
-- statement:
--   Throughout, $\iota$ is a preorder, $M : \iota \to \mathrm{Type}$ carries transition maps $f_{ij} : M_i \to M_j$ for $i \le j$ forming a `DirectedSystem`, and $g_i : M_i \to P$ is a family of maps into a fixed type $P$. The class [`IsDirectLimit f g`](../def/Mathlib_Algebra_IsDirectLimit.html#L8) is a proposition with three fields, asserting that the cone $(g_i)$ exhibits $P$ as the direct limit: `surj`, every $p \in P$ is of the form $g_i(m_i)$ for some index $i$ and some $m_i \in M_i$; `inj`, if $g_i(m_i) = g_j(m_j)$ then there is a $k$ with $i \le k$, $j \le k$ and $f_{ik}(m_i) = f_{jk}(m_j)$; and `compatibility`, $g_j(f_{ij}(x)) = g_i(x)$ for all $i \le j$ and $x \in M_i$. So this is a predicate on a chosen family of structure maps into a given object, not a construction of a limit; no algebraic structure is assumed at this stage, the maps being bare functions.
--
--   The helper declarations extract, for $p \in P$, an index `preimage_index` and an element `preimage` of the module at that index whose image under the corresponding $g$ is $p$ (`image_preimage`), using choice. Given two cones $g_1$ into $P_1$ and $g_2$ into $P_2$, with $P_1$ a direct limit, [`IsDirectLimit.lift`](../def/Mathlib_Algebra_IsDirectLimit.html#L40) sends $p \in P_1$ to $g_2$ applied to a chosen preimage of $p$; `lift_of` shows that when $g_2$ is compatible with the transition maps this is independent of the choice, i.e. the lift composed with $g_{1,i}$ is $g_{2,i}$. When both cones are direct limits, [`IsDirectLimit.Equiv`](../def/Mathlib_Algebra_IsDirectLimit.html#L50) is the resulting bijection $P_1 \simeq P_2$, with the two lemmas computing it and its inverse on elements of the form $g_i(x)$.
--
--   The `Module` namespace repeats this for $R$-modules: with $\iota$ directed, $f_{ij}$ and $g_i$ $R$-linear, `Module.lift` upgrades the lift to an $R$-linear map $P_1 \to P_2$ (additivity and $R$-homogeneity being checked by pushing representatives into a common index), `Module.lift_of` records its values on $g_{1,i}(x)$, `Module.lift_unique` states that an arbitrary linear $F : P_1 \to P_2$ agrees pointwise with the lift of the cone $F \circ g_{1,i}$, and `Module.linearEquiv` promotes `Equiv` to an $R$-linear isomorphism between any two direct limits of the same system, again with formulae for it and its inverse on $g_i(x)$.
--
--   **Relation to Mathlib.** Mathlib provides the concrete construction `Module.DirectLimit` together with its structure maps `Module.DirectLimit.of`, but no predicate recognising an arbitrary object as a direct limit; the class here supplies one, and an instance verifies that Mathlib's construction with its canonical maps satisfies it (for a nonempty index preorder), so that results proved for Mathlib's model transfer via `Module.linearEquiv`.
--
--   **Where it is used.** This module is imported widely across the development, where objects built by other means (unions of increasing families, colimits of level structures, and similar) are recognised as direct limits of directed systems and maps out of them are constructed from compatible families, without having to identify them with Mathlib's quotient model.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Algebra/IsDirectLimit.lean` — © 2025 Madison Crim; authors: Madison Crim). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

@[mk_iff] class IsDirectLimit [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

theorem compatibility' {i j hij} (x : M i) : g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

theorem is_injective {i j} {mi : M i} {mj : M j} (h : g i mi = g j mj) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

include f in
theorem is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj f

noncomputable def preimage_index (p : P) : ι := (is_surjective f g p).choose

noncomputable def preimage (p : P) : M (preimage_index f g p) :=
  (is_surjective f g p).choose_spec.choose

theorem image_preimage (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

noncomputable def lift [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimage_index f g₁ p) (preimage f g₁ p)

@[simp]
theorem lift_of [IsDirectLimit f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (lift f g₁ g₂) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

noncomputable def Equiv [h₁ : IsDirectLimit f g₁] [h₂ : IsDirectLimit f g₂] :
    P₁ ≃ P₂ where
  toFun := lift f g₁ g₂
  invFun := lift f g₂ g₁
  left_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₁.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]
  right_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₂.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]

@[simp]
lemma Equiv_apply (i : ι) (x : M i) [IsDirectLimit f g₁] [IsDirectLimit f g₂] :
  Equiv f g₁ g₂ (g₁ i x) = g₂ i x := by
  simp [Equiv, Equiv.coe_fn_mk, compatibility', implies_true, lift_of]

@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) [IsDirectLimit f g₁]
  [IsDirectLimit f g₂] : (Equiv f g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp [Equiv, compatibility', implies_true, lift_of]

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit (f · · ·) (Module.DirectLimit.of R ι M f ·) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of, Quotient.eq] at h
    exact h
  compatibility i j hij x := Module.DirectLimit.of_f

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]

omit [IsDirected ι (· ≤ ·)] in
theorem compatibility_module {i j hij} (x : M i) : g₁ j (f i j hij x) = g₁ i x :=
  compatibility' (f · · ·) (g₁ · ·) x

noncomputable def lift
    (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
  toFun := IsDirectLimit.lift (f · · ·) (g₁ · ·) (g₂ · · )
  map_add' x y := by
    obtain ⟨k, hxk, hyk⟩ :=
      IsDirected.directed (r := (· ≤ ·)) (preimage_index (f · · ·) (g₁ · ·) x)
      (preimage_index (f · · ·) (g₁ · ·) y)
    obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·))
      (preimage_index (f · · ·) (g₁ · ·) (x+y)) k
    have sum_eq : g₁ k' (f (preimage_index (f · · ·) (g₁ · ·) x) k' (le_trans hxk hkk')
      (preimage (f · · ·) (g₁ · ·) x) + f (preimage_index (f · · ·) (g₁ · ·) y) k'
      (le_trans hyk hkk') (preimage (f · · ·) (g₁ · ·) y)) =
        g₁ (preimage_index (f · · ·) (g₁ · ·) (x+y)) (preimage (f · · ·) (g₁ · ·) (x+y)) := by
      simp only [LinearMap.map_add, image_preimage]
      repeat rw [compatibility' (f · · ·) (g₁ · ·),
        image_preimage (f := (f · · ·)) (g := (g₁ · ·))]
    obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := is_injective (f · · ·) (g₁ · ·) sum_eq
    simpa [Hg, IsDirectLimit.lift] using congr_arg (g₂ k'') h'''.symm
  map_smul' r x := by
    have smul_eq : g₁ (preimage_index (f · · ·) (g₁ · ·) (r • x)) (preimage (f · · ·) (g₁ · ·)
      (r • x)) = g₁ (preimage_index (f · · ·) (g₁ · ·) x) (r • preimage (f · · ·) (g₁ · ·) x) := by
      simp only [image_preimage, map_smul]
    obtain ⟨k, hixk, hirxk, h_smul⟩ := is_injective (f · · ·) (g₁ · ·) smul_eq
    simpa [Hg, IsDirectLimit.lift] using congr_arg (g₂ k) h_smul

@[simp]
theorem lift_of (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (Module.lift f g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift, IsDirectLimit.lift_of]
  exact IsDirectLimit.lift_of (f · · ·) (g₁ · ·) (g₂ · ·) Hg x

theorem lift_unique (F : P₁ →ₗ[R] P₂) (x) : F x = (Module.lift f g₁ (fun i ↦ F.comp <| g₁ i)
    (fun i j hij x ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact LinearMap.congr_arg (IsDirectLimit.compatibility (f := (f · · ·))
      (g := (g₁ · ·)) i j hij x))) x := by
  simp only [lift, IsDirectLimit.lift,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, image_preimage]

variable [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

noncomputable def linearEquiv : P₁ ≃ₗ[R] P₂ :=
  { IsDirectLimit.Equiv (f · · ·) (g₁ · ·) (g₂ · ·) with
    map_add' := (lift f g₁ g₂ h₂.compatibility).map_add'
    map_smul' := (lift f g₁ g₂ h₂.compatibility).map_smul'}

@[simp]
lemma linearEquiv_apply (i : ι) (x : M i) :
  linearEquiv f g₁ g₂ (g₁ i x) = g₂ i x :=
  IsDirectLimit.Equiv_apply (f · · ·) (g₁ · ·) (g₂ · ·) i x

@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) :
  (linearEquiv f g₁ g₂).symm (g₂ i x) = g₁ i x :=
  IsDirectLimit.linearEquiv_symm_apply (f · · ·) (g₁ · ·) (g₂ · ·) i x

end Module

end IsDirectLimit


