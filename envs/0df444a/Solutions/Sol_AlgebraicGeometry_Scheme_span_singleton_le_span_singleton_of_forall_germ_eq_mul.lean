-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.span_singleton_le_span_singleton_of_forall_germ_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c70bb146-1ee7-5484-9bcc-bed750b9d1c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace LocPrinc

open TopologicalSpace

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.affineOpens) (g : ∀ i, Γ(X, U i))

noncomputable abbrev res {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

omit U g in
theorem res_res {V W Y : X.Opens} (h : V ≤ W) (h' : W ≤ Y) (s : Γ(X, Y)) : res h (res h' s) = res (h.trans h') s := by
  change (X.presheaf.map (homOfLE h').op ≫ X.presheaf.map (homOfLE h).op) s = _
  rw [← X.presheaf.map_comp]
  rfl

omit U g in
theorem res_self {V : X.Opens} (s : Γ(X, V)) : res (le_refl V) s = s := by
  change (X.presheaf.map (homOfLE (le_refl V)).op) s = s
  have : (homOfLE (le_refl V)).op = 𝟙 _ := rfl
  rw [this, X.presheaf.map_id]
  rfl

theorem res_mem_span {V W : X.Opens} (h : V ≤ W) {Y : X.Opens} (hW : W ≤ Y) (t : Γ(X, Y)) (s : Γ(X, W))
    (hs : s ∈ Ideal.span {res hW t}) : res h s ∈ Ideal.span {res (h.trans hW) t} := by
  rw [Ideal.mem_span_singleton'] at hs ⊢
  obtain ⟨a, rfl⟩ := hs
  exact ⟨res h a, by rw [map_mul, res_res]⟩

def LocMem (W : X.Opens) (s : Γ(X, W)) (x : X) : Prop :=
  ∃ (V : X.affineOpens) (i : ι) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U i),
    res hVW s ∈ Ideal.span {res hVU (g i)}

variable (hU : ⨆ i, (U i : X.Opens) = ⊤)
  (hg : ∀ (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i), res h (g i) ∈ nonZeroDivisors Γ(X, W))
  (hcomp : ∀ (i j : ι) (W : X.affineOpens) (hi : (W : X.Opens) ≤ U i) (hj : (W : X.Opens) ≤ U j),
    Ideal.span {res hi (g i)} = Ideal.span {res hj (g j)})

include hU in
omit g in

theorem exists_affine_nhd (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ (V : X.affineOpens) (i : ι), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ W ∧ (V : X.Opens) ≤ U i := by
  have hx' : x ∈ (⨆ i, (U i : X.Opens)) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ W ⊓ (U i : X.Opens) from ⟨hx, hi⟩) (W ⊓ U i).2
  exact ⟨⟨V, hV⟩, i, hxV, fun y hy => (hVle hy).1, fun y hy => (hVle hy).2⟩

include hcomp in

theorem LocMem.restrict {W : X.Opens} {s : Γ(X, W)} {x : X} (h : LocMem U g W s x)
    (V' : X.affineOpens) (j : ι) (hxV' : x ∈ (V' : X.Opens)) (hV'W : (V' : X.Opens) ≤ W) (hV'U : (V' : X.Opens) ≤ U j)
    (hsmall : ∀ (V : X.affineOpens), x ∈ (V : X.Opens) → ∃ (V'' : X.affineOpens), x ∈ (V'' : X.Opens) ∧ (V'' : X.Opens) ≤ V ∧ (V'' : X.Opens) ≤ V') :
    ∃ (V'' : X.affineOpens) (_ : x ∈ (V'' : X.Opens)) (hle : (V'' : X.Opens) ≤ V'),
      res (hle.trans hV'W) s ∈ Ideal.span {res (hle.trans hV'U) (g j)} := by
  obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := h
  obtain ⟨V'', hxV'', h1, h2⟩ := hsmall V hxV
  refine ⟨V'', hxV'', h2, ?_⟩
  have hmem' := res_mem_span h1 hVU (g i) _ hmem
  rw [res_res] at hmem'
  rw [← hcomp i j V'' (h1.trans hVU) (h2.trans hV'U)]
  exact hmem'

include hg in

theorem mul_res_g_injective (i : ι) (O : X.Opens) (hO : O ≤ U i) (c₁ c₂ : Γ(X, O))
    (h : c₁ * res hO (g i) = c₂ * res hO (g i)) : c₁ = c₂ := by

  let J := {V : X.affineOpens // (V : X.Opens) ≤ O}
  have hcov : O ≤ ⨆ j : J, (j.1 : X.Opens) := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVO⟩, hxV⟩
  apply X.sheaf.eq_of_locally_eq' (fun j : J => (j.1 : X.Opens)) O (fun j => homOfLE j.2) hcov
  intro j
  change res j.2 c₁ = res j.2 c₂
  have hj := congrArg (res j.2) h
  rw [map_mul, map_mul, res_res] at hj
  have hnzd := hg i j.1 (j.2.trans hO)
  exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp hj

include hg hcomp in

theorem mem_span_of_locMem (W₀ : X.Opens) (s : Γ(X, W₀)) (i : ι) (V : X.affineOpens)
    (hVW : (V : X.Opens) ≤ W₀) (hVU : (V : X.Opens) ≤ U i)
    (hloc : ∀ x ∈ (V : X.Opens), LocMem U g W₀ s x) :
    res hVW s ∈ Ideal.span {res hVU (g i)} := by
  classical

  let J := {V' : X.affineOpens // ∃ (h : (V' : X.Opens) ≤ V), res (h.trans hVW) s ∈ Ideal.span {res (h.trans hVU) (g i)}}
  have hJle : ∀ j : J, (j.1 : X.Opens) ≤ V := fun j => j.2.1
  have hcov : (V : X.Opens) ≤ ⨆ j : J, (j.1 : X.Opens) := by
    intro x hx
    obtain ⟨V'', hxV'', hle, hmem⟩ := (hloc x hx).restrict U g hcomp V i hx hVW hVU (fun V₁ hx₁ => by
      obtain ⟨_, ⟨V₂, hV₂, rfl⟩, hxV₂, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V₁ : X.Opens) ⊓ V from ⟨hx₁, hx⟩) ((V₁ : X.Opens) ⊓ V).2
      exact ⟨⟨V₂, hV₂⟩, hxV₂, fun y hy => (hle hy).1, fun y hy => (hle hy).2⟩)
    exact Opens.mem_iSup.mpr ⟨⟨V'', hle, hmem⟩, hxV''⟩

  have hq : ∀ j : J, ∃ c : Γ(X, j.1), c * res ((hJle j).trans hVU) (g i) = res ((hJle j).trans hVW) s := by
    intro j
    obtain ⟨h, hmem⟩ := j.2
    rw [Ideal.mem_span_singleton'] at hmem
    exact hmem
  choose c hc using hq
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun j : J => (j.1 : X.Opens)) c := by
    intro j k
    apply mul_res_g_injective U g hg i ((j.1 : X.Opens) ⊓ k.1) (inf_le_left.trans ((hJle j).trans hVU))
    have ej := congrArg (res (inf_le_left : (j.1 : X.Opens) ⊓ k.1 ≤ j.1)) (hc j)
    have ek := congrArg (res (inf_le_right : (j.1 : X.Opens) ⊓ k.1 ≤ k.1)) (hc k)
    rw [map_mul, res_res, res_res] at ej ek
    exact ej.trans ek.symm
  obtain ⟨cV', hcV', -⟩ := X.sheaf.existsUnique_gluing' (fun j : J => (j.1 : X.Opens)) V (fun j => homOfLE (hJle j)) hcov c hcompat
  let cV : Γ(X, (V : X.Opens)) := cV'
  have hcV : ∀ j, res (hJle j) cV = c j := hcV'
  rw [Ideal.mem_span_singleton']
  refine ⟨cV, ?_⟩
  apply X.sheaf.eq_of_locally_eq' (fun j : J => (j.1 : X.Opens)) V (fun j => homOfLE (hJle j)) hcov
  intro j
  change res (hJle j) (cV * res hVU (g i)) = res (hJle j) (res hVW s)
  rw [map_mul, res_res, res_res]
  rw [hcV j]
  exact hc j

omit g in

theorem exists_affine_le_inf (V₁ V₂ : X.affineOpens) (x : X) (h₁ : x ∈ (V₁ : X.Opens)) (h₂ : x ∈ (V₂ : X.Opens)) :
    ∃ (V : X.affineOpens), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ V₁ ∧ (V : X.Opens) ≤ V₂ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (V₁ : X.Opens) ⊓ V₂ from ⟨h₁, h₂⟩) ((V₁ : X.Opens) ⊓ V₂).2
  exact ⟨⟨V, hV⟩, hxV, fun y hy => (hle hy).1, fun y hy => (hle hy).2⟩

def glueIdeal (W : X.Opens) : Ideal Γ(X, W) where
  carrier := {s | ∀ x ∈ W, LocMem U g W s x}
  zero_mem' := by
    intro x hx
    obtain ⟨V, i, hxV, hVW, hVU⟩ := exists_affine_nhd U hU W x hx
    exact ⟨V, i, hxV, hVW, hVU, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := ha x hx
    obtain ⟨V'', hxV'', hle, hmemb⟩ := (hb x hx).restrict U g hcomp V i hxV hVW hVU
      (fun V₁ hx₁ => exists_affine_le_inf V₁ V x hx₁ hxV)
    refine ⟨V'', i, hxV'', hle.trans hVW, hle.trans hVU, ?_⟩
    rw [map_add]
    refine add_mem ?_ hmemb
    have := res_mem_span hle hVU (g i) _ hmem
    rwa [res_res] at this
  smul_mem' := by
    intro c s hs x hx
    obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := hs x hx
    exact ⟨V, i, hxV, hVW, hVU, by rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hmem⟩

theorem mem_glueIdeal {W : X.Opens} {s : Γ(X, W)} : s ∈ glueIdeal U g hU hcomp W ↔ ∀ x ∈ W, LocMem U g W s x := Iff.rfl

include hg in

theorem glueIdeal_eq_span (i : ι) (W : X.affineOpens) (h : (W : X.Opens) ≤ U i) :
    glueIdeal U g hU hcomp W = Ideal.span {res h (g i)} := by
  apply le_antisymm
  · intro s hs
    have := mem_span_of_locMem U g hg hcomp (W : X.Opens) s i W le_rfl h hs
    rwa [res_self] at this
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    intro x hx
    exact ⟨W, i, hx, le_rfl, h, by rw [res_self]; exact Ideal.subset_span rfl⟩

theorem res_mem_glueIdeal {W W' : X.Opens} (hW : W' ≤ W) {s : Γ(X, W)} (hs : s ∈ glueIdeal U g hU hcomp W) :
    res hW s ∈ glueIdeal U g hU hcomp W' := by
  intro x hx
  obtain ⟨V, i, hxV, hVW, hVU, hmem⟩ := hs x (hW hx)

  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (V : X.Opens) ⊓ W' from ⟨hxV, hx⟩) ((V : X.Opens) ⊓ W').2
  have h1 : (V' : Set X) ≤ (V : X.Opens) := fun y hy => (hle hy).1
  have h2 : (V' : Set X) ≤ (W' : X.Opens) := fun y hy => (hle hy).2
  refine ⟨⟨V', hV'⟩, i, hxV', h2, fun y hy => hVU (h1 hy), ?_⟩
  have := res_mem_span (V := V') h1 hVU (g i) _ hmem
  rw [res_res] at this
  rw [res_res]
  exact this

include hg in

theorem map_glueIdeal_basicOpen (W : X.affineOpens) (f : Γ(X, (W : X.Opens))) :
    Ideal.map (res (X.basicOpen_le f)) (glueIdeal U g hU hcomp W) = glueIdeal U g hU hcomp (X.affineBasicOpen f) := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact res_mem_glueIdeal U g hU hcomp (X.basicOpen_le f) hs
  · intro s hs
    letI := W.2.isLocalization_basicOpen f
    obtain ⟨⟨a₀, ⟨_, m, rfl⟩⟩, ha₀⟩ := IsLocalization.surj (Submonoid.powers f) s
    simp only at ha₀

    have key : ∀ x ∈ (W : X.Opens), ∃ (V : X.affineOpens) (i : ι) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W)
        (hVU : (V : X.Opens) ≤ U i), ∃ N : ℕ, res hVW (f ^ N * a₀) ∈ Ideal.span {res hVU (g i)} := by
      intro x hx
      obtain ⟨V, i, hxV, hVW, hVU⟩ := exists_affine_nhd U hU W x hx
      refine ⟨V, i, hxV, hVW, hVU, ?_⟩
      let fV : Γ(X, (V : X.Opens)) := res hVW f
      have hV'V : (X.affineBasicOpen fV : X.Opens) ≤ V := X.basicOpen_le fV
      have hV'D : (X.affineBasicOpen fV : X.Opens) ≤ X.affineBasicOpen f := by
        change X.basicOpen fV ≤ X.basicOpen f
        rw [Scheme.basicOpen_res]
        exact inf_le_right

      have hsV' := mem_span_of_locMem U g hg hcomp (X.affineBasicOpen f) s i (X.affineBasicOpen fV) hV'D (hV'V.trans hVU)
        (fun y hy => hs y (hV'D hy))

      have ha₀V' : res hV'V (res hVW a₀) ∈ Ideal.span {res (hV'V.trans hVU) (g i)} := by
        have e : res hV'D s * res hV'D (res (X.basicOpen_le f) (f ^ m)) = res hV'D (res (X.basicOpen_le f) a₀) := by
          rw [← map_mul]; exact congrArg (res hV'D) ha₀
        erw [res_res, res_res] at e
        rw [res_res, show res (hV'V.trans hVW) a₀ = res (hV'D.trans (X.basicOpen_le f)) a₀ from rfl, ← e]
        exact Ideal.mul_mem_right _ _ hsV'

      letI := V.2.isLocalization_basicOpen fV
      have hmap : res hV'V (res hVW a₀) ∈ Ideal.map (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen fV)) (Ideal.span {res hVU (g i)}) := by
        rw [Ideal.map_span, Set.image_singleton,
          show (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen fV)) (res hVU (g i)) = res (hV'V.trans hVU) (g i) from res_res _ _ _]
        exact ha₀V'
      obtain ⟨⟨⟨b, hb⟩, ⟨_, k, rfl⟩⟩, hbk0⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers fV) Γ(X, X.basicOpen fV)).mp hmap
      have hbk : algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen fV) (res hVW a₀ * fV ^ k) =
          algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen fV) b := by
        rw [map_mul]; exact hbk0
      obtain ⟨⟨_, k', rfl⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers fV) Γ(X, X.basicOpen fV)).mp hbk
      change fV ^ k' * (res hVW a₀ * fV ^ k) = fV ^ k' * b at hk'
      refine ⟨k' + k, ?_⟩
      have : res hVW (f ^ (k' + k) * a₀) = fV ^ k' * (res hVW a₀ * fV ^ k) := by
        rw [map_mul, map_pow]; ring
      rw [this, hk']
      exact Ideal.mul_mem_left _ _ hb
    choose V i hxV hVW hVU N hN using key

    obtain ⟨t, ht⟩ := W.2.isCompact.elim_finite_subcover (fun x : (W : X.Opens) => ((V x.1 x.2 : X.Opens) : Set X))
      (fun x => (V x.1 x.2 : X.Opens).2) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x hx⟩)
    let Nmax : ℕ := t.sup (fun x => N x.1 x.2)
    have hmemW : f ^ Nmax * a₀ ∈ glueIdeal U g hU hcomp W := by
      intro y hy
      obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ ((V x.1 x.2 : X.Opens) : Set X) := by
        simpa only [Set.mem_iUnion, exists_prop] using ht hy
      refine ⟨V x.1 x.2, i x.1 x.2, hyx, hVW x.1 x.2, hVU x.1 x.2, ?_⟩
      have hle : N x.1 x.2 ≤ Nmax := Finset.le_sup (f := fun x => N x.1 x.2) hxt
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have : f ^ Nmax * a₀ = f ^ d * (f ^ N x.1 x.2 * a₀) := by rw [hd]; ring
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hN x.1 x.2)

    have hs' : s * algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f) (f ^ (m + Nmax)) =
        algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f) (f ^ Nmax * a₀) := by
      rw [pow_add, map_mul, ← mul_assoc, ha₀, map_mul]; ring
    obtain ⟨u, hu⟩ := IsLocalization.map_units Γ(X, X.basicOpen f) (⟨f ^ (m + Nmax), _, rfl⟩ : Submonoid.powers f)
    have hu' : (↑u : Γ(X, X.basicOpen f)) = algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f) (f ^ (m + Nmax)) := hu
    have : s = algebraMap Γ(X, (W : X.Opens)) Γ(X, X.basicOpen f) (f ^ Nmax * a₀) * ↑u⁻¹ := by
      rw [← hs', ← hu', mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmemW)

noncomputable def glueIdealSheafData : X.IdealSheafData :=
  Scheme.IdealSheafData.mk (fun W => glueIdeal U g hU hcomp W) (fun W f => map_glueIdeal_basicOpen U g hU hg hcomp W f) _ rfl

end LocPrinc

namespace LocPrinc

open TopologicalSpace

variable {X : Scheme.{u}}

theorem exists_affine_res_mem_span_of_germ {W : X.Opens} (a b : Γ(X, W)) (x : X) (hx : x ∈ W)
    (h : ∃ u : X.presheaf.stalk x, X.presheaf.germ W x hx a = u * X.presheaf.germ W x hx b) :
    ∃ (V : X.affineOpens) (_ : x ∈ (V : X.Opens)) (hVW : (V : X.Opens) ≤ W), res hVW a ∈ Ideal.span {res hVW b} := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨V₁, hxV₁, u', rfl⟩ := X.presheaf.exists_germ_eq (x := x) u

  have e : X.presheaf.germ (W ⊓ V₁) x ⟨hx, hxV₁⟩ (res inf_le_left a) =
      X.presheaf.germ (W ⊓ V₁) x ⟨hx, hxV₁⟩ (res inf_le_right u' * res inf_le_left b) := by
    rw [map_mul]
    erw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨hx, hxV₁⟩,
      TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨hx, hxV₁⟩,
      TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨hx, hxV₁⟩]
    exact hu
  obtain ⟨V₂, hxV₂, i₁, i₂, heq⟩ := X.presheaf.germ_eq (U := W ⊓ V₁) (V := W ⊓ V₁) x ⟨hx, hxV₁⟩ ⟨hx, hxV₁⟩ (res inf_le_left a) (res inf_le_right u' * res inf_le_left b) e
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV₂ V₂.2
  have hVW : (V : Set X) ≤ (W : X.Opens) := fun y hy => (i₁.le (hle hy)).1
  refine ⟨⟨V, hV⟩, hxV, hVW, ?_⟩
  rw [Ideal.mem_span_singleton']
  refine ⟨res (show (V : X.Opens) ≤ W ⊓ V₁ from fun y hy => i₂.le (hle hy)) (res inf_le_right u'), ?_⟩
  have := congrArg (res (show (V : X.Opens) ≤ V₂ from hle)) heq
  change res hle (X.presheaf.map i₁.op (res inf_le_left a)) = res hle (X.presheaf.map i₂.op (res inf_le_right u' * res inf_le_left b)) at this
  rw [map_mul, map_mul] at this
  erw [res_res, res_res, res_res, res_res, res_res, res_res] at this
  rw [res_res]
  exact this.symm

theorem span_le_span_of_forall_germ (W : X.affineOpens) (a b : Γ(X, (W : X.Opens)))
    (hb : ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W), res h b ∈ nonZeroDivisors Γ(X, V))
    (h : ∀ x (hx : x ∈ (W : X.Opens)), ∃ u : X.presheaf.stalk x, X.presheaf.germ W x hx a = u * X.presheaf.germ W x hx b) :
    Ideal.span {a} ≤ Ideal.span {b} := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  have key := mem_span_of_locMem (ι := PUnit.{u+1}) (fun _ => W) (fun _ => b)
    (fun _ V hV => hb V hV) (fun _ _ V hi hj => rfl) (W : X.Opens) a PUnit.unit W le_rfl le_rfl (fun x hx => by
      obtain ⟨V, hxV, hVW, hmem⟩ := exists_affine_res_mem_span_of_germ a b x hx (h x hx)
      exact ⟨V, PUnit.unit, hxV, hVW, hVW, hmem⟩)
  rwa [res_self, res_self] at key

end LocPrinc

theorem solution
    {X : Scheme.{u}} (W : X.affineOpens) (a b : Γ(X, (W : X.Opens)))
    (hb : ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W), (X.presheaf.map (homOfLE h).op).hom b ∈ nonZeroDivisors Γ(X, V))
    (h : ∀ (x : ↥X) (hx : x ∈ (W : X.Opens)), ∃ u : X.presheaf.stalk x,
      (X.presheaf.germ (W : X.Opens) x hx).hom a = u * (X.presheaf.germ (W : X.Opens) x hx).hom b) :
    Ideal.span {a} ≤ Ideal.span {b} :=
  LocPrinc.span_le_span_of_forall_germ W a b hb h

end S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul (solution)
