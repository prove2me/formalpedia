-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:57:06.495184+00:00
-- url     : https://prove2.me/theorems/3cb58bb9-b2fc-45a7-8394-64f610bad81f
-- title:
--   PCech Double
-- statement:
--   Definitions and structural lemmas for PCech Double, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
namespace CechDouble
open Cech
section General
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}
variable (S E U) in

abbrev dE (p : ℕ) : Cochain (fun _ : Cell U => E) p →ₗ[S] Cochain (fun _ : Cell U => E) (p + 1) :=
  Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p
theorem dE_const (e : E) : dE S E U 0 (fun _ => e) = 0 :=
  Cech.d_zero_of_compat (G := fun _ : Cell U => E) (ρ := Cech.idRes S E U) (fun _ => e) (fun _ _ _ => rfl)
theorem d_mem (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ)
    {s : Cochain (fun _ : Cell U => E) p} (hs : s ∈ Cdeg (fun _ : Cell U => E) G p) :
    dE S E U p s ∈ Cdeg (fun _ : Cell U => E) G (p + 1) := fun J _ => by
  rw [Cech.d_apply]
  refine Submodule.sum_mem _ fun j _ => zsmul_mem ?_ _
  exact hG _ _ (face_subset J j) (hs _ (Set.mem_univ _))
def dRes (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ) :
    Cdeg (fun _ : Cell U => E) G p →ₗ[S] Cdeg (fun _ : Cell U => E) G (p + 1) :=
  (dE S E U p).restrict fun _ hs => d_mem G hG p hs
theorem aug_mono {Ω : Type w} [Field Ω] {r : ℕ} {y : Fin (r + 1) → Ω} {ι : Type*}
    (G : ι → Chart y → Submodule S E) (A : ι → Submodule S E) (rel : ι → ι → Prop)
    (hG : ∀ i i' J, rel i i' → G i J ≤ G i' J) (hA : ∀ i, Cech.AugExact S (G i) (A i)) :
    ∀ i i', rel i i' → A i ≤ A i' := by
  intro i i' hii' e he
  by_cases h0 : Nonempty (Cech.Idx (support y) 0)
  · obtain ⟨J₀⟩ := h0
    obtain ⟨b, hb, hbe⟩ := (hA i').2.2.1 (fun _ => e)
      (fun J _ => hG i i' J.1 hii' ((hA i).1 J.1 he)) (dE_const e)
    have h1 : e = b := hbe J₀
    rw [h1]
    exact hb
  · have h1 : e = 0 := (hA i).2.1 e he fun J => (h0 ⟨J⟩).elim
    rw [h1]
    exact zero_mem _
end General
section Double
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}
variable (E x y) in

abbrev W (p q : ℕ) : Type v := Cochain (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) p
variable (S E x y) in

def vW (p q : ℕ) : W E x y p q →ₗ[S] W E x y (p + 1) q :=
  Cech.d (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) (Cech.idRes S _ (support x)) p
variable (S E x y) in

def hW (p q : ℕ) : W E x y p q →ₗ[S] W E x y p (q + 1) :=
  Cech.mapC (fun _ : Chart x => dE S E (support y) q) p
theorem hW_apply (p q : ℕ) (s : W E x y p q) (I : Idx (support x) p) :
    hW S E x y p q s I = dE S E (support y) q (s I) := rfl
theorem vW_apply (p q : ℕ) (s : W E x y p q) (I' : Idx (support x) (p + 1)) (J : Idx (support y) q) :
    vW S E x y p q s I' J = dE S E (support x) p (fun I => s I J) I' := by
  simp only [vW, dE, Cech.d_apply, Cech.idRes, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply]
theorem hW_vW (p q : ℕ) (s : W E x y p q) :
    hW S E x y (p + 1) q (vW S E x y p q s) = vW S E x y p (q + 1) (hW S E x y p q s) :=
  Cech.mapC_d (ρ := Cech.idRes S _ (support x)) (ρ' := Cech.idRes S _ (support x))
    (fun _ : Chart x => dE S E (support y) q) (fun _ _ _ _ => rfl) p s
variable (M : Chart x → Chart y → Submodule S E)
def Dsub (p q : ℕ) : Submodule S (W E x y p q) :=
  Submodule.pi Set.univ fun I : Idx (support x) p => Cdeg (fun _ : Chart y => E) (M I.1) q
theorem mem_Dsub {p q : ℕ} {s : W E x y p q} : s ∈ Dsub M p q ↔ ∀ I J, s I J ∈ M I.1 J.1 := by
  simp [Dsub, Cdeg, Submodule.mem_pi]
variable {M}
theorem vW_mem (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J) {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : vW S E x y p q s ∈ Dsub M (p + 1) q := by
  rw [mem_Dsub] at hs ⊢
  intro I' J
  rw [vW_apply]
  exact d_mem (fun I => M I J.1) (fun I I' hI => hM₁ I I' J.1 hI) p (fun I _ => hs I J) I' (Set.mem_univ _)
theorem hW_mem (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J') {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : hW S E x y p q s ∈ Dsub M p (q + 1) := by
  rw [mem_Dsub] at hs ⊢
  intro I J'
  rw [hW_apply]
  exact d_mem (M I.1) (hM₂ I.1) q (fun J _ => hs I J) J' (Set.mem_univ _)
variable (Ax : Chart x → Submodule S E) (Bx : Chart y → Submodule S E)
def dbl (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    Stair.DblData.{u, v} S where
  D p q := Dsub M p q
  v p q := (vW S E x y p q).restrict fun _ hs => vW_mem hM₁ hs
  h p q := (hW S E x y p q).restrict fun _ hs => hW_mem hM₂ hs
  comm p q := LinearMap.ext fun s => Subtype.ext (hW_vW p q s.1).symm
  A p := Cdeg (fun _ : Chart x => E) Ax p
  dA := dRes Ax (aug_mono M Ax _ hM₁ hA)
  a _ :=
    { toFun := fun s => ⟨fun I _ => s.1 I, (mem_Dsub M).2 fun I J => (hA I.1).1 J.1 (s.2 I (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  C q := Cdeg (fun _ : Chart y => E) Bx q
  dC := dRes Bx (aug_mono (fun J I => M I J) Bx _ (fun J J' I hJ => hM₂ I J J' hJ) hB)
  c _ :=
    { toFun := fun t => ⟨fun _ J => t.1 J, (mem_Dsub M).2 fun I J => (hB J.1).1 I.1 (t.2 J (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
end Double
end CechDouble
end
end GroundTheory.Heights₂.Heights.Kleiman


