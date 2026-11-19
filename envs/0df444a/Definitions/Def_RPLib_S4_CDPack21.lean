-- Prove2me | Definitions.Def_RPLib_S4_CDPack21
-- name    : RPLib_S4_CDPack21
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:46:29.561545+00:00
-- url     : https://prove2.me/theorems/476c9b32-0ca6-441c-a48b-346188b73c63
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 21 of 71
-- statement:
--   Part 21 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CupDuality_LamCoord`: S4-CurveDuality O5d-2: coordinates on the parabolic block
--   * `Def_RP_CupDuality_LamPerf`: S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack20
import Definitions.Def_RPLib_S4_CDPack05

/-!
# Curve-duality library package, part 21 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CupDuality_LamCoord`: S4-CurveDuality O5d-2: coordinates on the parabolic block
* `Def_RP_CupDuality_LamPerf`: S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_LamCoord =====
section

/-!
# S4-CurveDuality O5d-2: coordinates on the parabolic block

Constant coefficients (`σ` trivial on `Γ`). Given `ℤ/N`-valued parabolic homomorphisms `χ_i` (vanishing on every
boundary inertia group), a dual family `e_j` (`χ_i(e_j) = δ_ij`) whose coordinates span all `ℤ/N`-valued parabolic
homomorphisms, and a ring hom `ι : ℤ/N → k`:
* `eR : k^r ≃ H¹_par(Γ, k(1))`, `λ ↦ [Σ λ_i ι∘χ_i]`;
* `eL : k^r ≃ H¹_c(Γ, k) / im(k^S)`, `λ ↦ [(Σ λ_i ι∘χ_i, 0)]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

variable {N : ℕ} [NeZero N] {k : Type} [CommRing k] (ι : ZMod N →+* k)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G} {r : ℕ} (χ : Fin r → Γ → ZMod N)
  {e : Fin r → Γ}

variable (I) in
/-- `g ∈ Γ` lies in some boundary inertia group. -/
def InBdry (g : Γ) : Prop := ∃ s, (g : G) ∈ I s

/-- `λ ↦ Σ_i λ_i ι(χ_i)`. -/
def parHomL : (Fin r → k) →ₗ[k] (Γ → k) where
  toFun l g := ∑ i, l i * ι (χ i g)
  map_add' l l' := funext fun g => by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a l := funext fun g => by simp [Finset.mul_sum, mul_assoc]

theorem parHomL_apply (l : Fin r → k) (g : Γ) : parHomL ι χ l g = ∑ i, l i * ι (χ i g) := rfl

variable {ι χ}

theorem parHomL_e (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) (l : Fin r → k) (j : Fin r) :
    parHomL ι χ l (e j) = l j := by
  rw [parHomL_apply, Finset.sum_eq_single j]
  · rw [hδ, if_pos rfl, map_one, mul_one]
  · intro i _ hij
    rw [hδ, if_neg hij, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem parHomL_isParHom (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (l : Fin r → k) :
    IsParHom (InBdry I) (parHomL ι χ l) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun i => (hχ i).1.eventually_eq x).mono fun y hy => ?_, fun g h => ?_,
    fun g hg => ?_⟩
  · simp only [parHomL_apply, hy]
  · have ha : ∀ i, χ i (g * h) = χ i g + χ i h := fun i => (hχ i).2.1 g h
    simp only [parHomL_apply, ha, map_add, mul_add, Finset.sum_add_distrib]
  · have h0 : ∀ i, χ i g = 0 := fun i => (hχ i).2.2 g hg
    simp only [parHomL_apply, h0, map_zero, mul_zero, Finset.sum_const_zero]

variable {σ : Representation k G k}

theorem mem_Z1_of_isParHom {P : Γ → Prop} (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : IsParHom P x) : x ∈ Z1 σ Γ :=
  (mem_Z1 σ Γ x).2 ⟨hx.1, fun g h => by rw [htriv, hx.2.1]⟩

theorem mem_Z1par_of_isParHom (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : IsParHom (InBdry I) x) : x ∈ Z1par σ Γ I :=
  ⟨mem_Z1_of_isParHom htriv hx, fun s => ⟨0, fun g hg => by
    rw [map_zero, sub_zero]
    exact hx.2.2 g ⟨s, hg⟩⟩⟩

theorem isParHom_of_mem_Z1par (htriv : ∀ (g : Γ) (x : k), σ g x = x) {x : Γ → k}
    (hx : x ∈ Z1par σ Γ I) : IsParHom (InBdry I) x := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hlc, hco⟩ := (mem_Z1 σ Γ x).1 hx1
  refine ⟨hlc, fun g h => by rw [hco, htriv], fun g ⟨s, hg⟩ => ?_⟩
  obtain ⟨b, hb⟩ := hx2 s
  rw [hb g hg, htriv, sub_self]

theorem mem_Z1c_of_isParHom {x : Γ → k} (hx : IsParHom (InBdry I) x) (m : S → k) :
    (x, m) ∈ Z1c (Representation.trivial k G k) Γ I :=
  ⟨mem_Z1_of_isParHom (fun _ _ => rfl) hx, fun s g hg => by
    rw [Representation.trivial_apply, sub_self]
    exact hx.2.2 g ⟨s, hg⟩⟩

theorem isParHom_of_mem_Z1c {p : (Γ → k) × (S → k)} (hp : p ∈ Z1c (Representation.trivial k G k) Γ I) :
    IsParHom (InBdry I) p.1 := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hlc, hco⟩ := (mem_Z1 _ Γ _).1 hp1
  refine ⟨hlc, fun g h => by rw [hco, Representation.trivial_apply], fun g ⟨s, hg⟩ => ?_⟩
  rw [hp2 s g hg, Representation.trivial_apply, sub_self]

theorem parHomL_eval (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {x : Γ → k} (hx : IsParHom (InBdry I) x) : parHomL ι χ (fun i => x (e i)) = x := by
  funext g
  rw [parHomL_apply, span_of_zmod ι χ e hspan hx g]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mk_mem_H1par {z : Z1 σ Γ} (hz : (z : Γ → k) ∈ Z1par σ Γ I) : H1.mk σ Γ z ∈ H1par σ Γ I :=
  Submodule.mem_map_of_mem (Submodule.mem_comap.2 hz)

variable (ι)

/-- `λ ↦ Σ λ_i ι∘χ_i ∈ Z¹(Γ, k(1))`. -/
def parZ1 (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] Z1 σ Γ :=
  LinearMap.codRestrict _ (parHomL ι χ) fun l => mem_Z1_of_isParHom htriv (parHomL_isParHom hχ l)

/-- `λ ↦ [Σ λ_i ι∘χ_i] ∈ H¹_par`. -/
def eRlin (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] H1par σ Γ I :=
  LinearMap.codRestrict _ (H1.mk σ Γ ∘ₗ parZ1 ι htriv hχ) fun l =>
    mk_mem_H1par (mem_Z1par_of_isParHom htriv (parHomL_isParHom hχ l))

theorem eRlin_injective (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) : Function.Injective (eRlin ι htriv hχ) := by
  refine (injective_iff_map_eq_zero _).2 fun l hl => funext fun j => ?_
  have h1 : H1.mk σ Γ (parZ1 ι htriv hχ l) = 0 := congrArg Subtype.val hl
  rw [H1.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨-, m, hm⟩ := h1
  have h2 : parHomL ι χ l (e j) = σ (e j : G) m - m := hm (e j)
  rw [htriv, sub_self, parHomL_e hδ] at h2
  exact h2

theorem eRlin_surjective (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    Function.Surjective (eRlin ι htriv hχ) := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have hx := isParHom_of_mem_Z1par (x := (z : Γ → k)) htriv (Submodule.mem_comap.1 hz)
  refine ⟨fun i => (z : Γ → k) (e i), Subtype.ext ?_⟩
  show H1.mk σ Γ (parZ1 ι htriv hχ _) = H1.mk σ Γ z
  congr 1
  exact Subtype.ext (parHomL_eval hspan hx)

/-- `eR : k^r ≃ H¹_par(Γ, k(1))`. -/
def eR (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    (Fin r → k) ≃ₗ[k] H1par σ Γ I :=
  LinearEquiv.ofBijective (eRlin ι htriv hχ) ⟨eRlin_injective ι htriv hχ hδ, eRlin_surjective ι htriv hχ hspan⟩

theorem eR_coe (htriv : ∀ (g : Γ) (x : k), σ g x = x) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) (l : Fin r → k) :
    (eR ι htriv hχ hδ hspan l : H1 σ Γ) = H1.mk σ Γ (parZ1 ι htriv hχ l) := rfl

/-- `λ ↦ (Σ λ_i ι∘χ_i, 0) ∈ Z¹_c(Γ, k)`. -/
def parZ1c (hχ : ∀ i, IsParHom (InBdry I) (χ i)) : (Fin r → k) →ₗ[k] Z1c (Representation.trivial k G k) Γ I :=
  LinearMap.codRestrict _ (LinearMap.inl k (Γ → k) (S → k) ∘ₗ parHomL ι χ) fun l =>
    mem_Z1c_of_isParHom (parHomL_isParHom hχ l) 0

theorem parZ1c_snd (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (l : Fin r → k) :
    (parZ1c ι hχ l : (Γ → k) × (S → k)).2 = 0 := rfl

/-- `λ ↦ [(Σ λ_i ι∘χ_i, 0)] ∈ H¹_c / im(k^S)`. -/
def eLlin (hχ : ∀ i, IsParHom (InBdry I) (χ i)) :
    (Fin r → k) →ₗ[k] H1c (Representation.trivial k G k) Γ I ⧸ LinearMap.range (bdryMap (k := k) Γ I) :=
  (LinearMap.range (bdryMap (k := k) Γ I)).mkQ ∘ₗ H1c.mk _ Γ I ∘ₗ parZ1c ι hχ

theorem eLlin_injective (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0) : Function.Injective (eLlin ι hχ) := by
  refine (injective_iff_map_eq_zero _).2 fun l hl => funext fun j => ?_
  have h1 : H1c.mk (Representation.trivial k G k) Γ I (parZ1c ι hχ l) ∈ LinearMap.range (bdryMap (k := k) Γ I) :=
    (Submodule.Quotient.mk_eq_zero _).1 hl
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h1
  rw [bdryMap_apply, H1c.mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    Submodule.mem_comap] at hm
  obtain ⟨-, m', hm', -⟩ := hm
  have h2 : (0 : k) - parHomL ι χ l (e j) = Representation.trivial k G k (e j : G) m' - m' := hm' (e j)
  rw [Representation.trivial_apply, sub_self, zero_sub, neg_eq_zero, parHomL_e hδ] at h2
  exact h2

theorem eLlin_surjective (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    Function.Surjective (eLlin ι hχ) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨p, rfl⟩ :=
    (Submodule.mkQ_surjective _ : Function.Surjective (H1c.mk (Representation.trivial k G k) Γ I)) y
  have hx := isParHom_of_mem_Z1c p.2
  refine ⟨fun i => (p : (Γ → k) × (S → k)).1 (e i), ?_⟩
  have hp : p = parZ1c ι hχ (fun i => (p : (Γ → k) × (S → k)).1 (e i)) +
      ⟨((0 : Γ → k), (p : (Γ → k) × (S → k)).2), zero_mem_Z1c Γ I _⟩ := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (p : (Γ → k) × (S → k)).1 = parHomL ι χ (fun i => (p : (Γ → k) × (S → k)).1 (e i)) + 0
      rw [add_zero, parHomL_eval hspan hx]
    · show (p : (Γ → k) × (S → k)).2 = 0 + (p : (Γ → k) × (S → k)).2
      rw [zero_add]
  have h0 : (LinearMap.range (bdryMap (k := k) Γ I)).mkQ (bdryMap (k := k) Γ I (p : (Γ → k) × (S → k)).2) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ _)
  rw [bdryMap_apply, H1c.mk] at h0
  conv_rhs => rw [hp, map_add, map_add, h0, add_zero]
  rfl

/-- `eL : k^r ≃ H¹_c(Γ, k) / im(k^S)`. -/
def eL (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) :
    (Fin r → k) ≃ₗ[k] H1c (Representation.trivial k G k) Γ I ⧸ LinearMap.range (bdryMap (k := k) Γ I) :=
  LinearEquiv.ofBijective (eLlin ι hχ) ⟨eLlin_injective ι hχ hδ, eLlin_surjective ι hχ hspan⟩

theorem eL_apply (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g) (l : Fin r → k) :
    eL ι hχ hδ hspan l = Submodule.Quotient.mk (H1c.mk (Representation.trivial k G k) Γ I (parZ1c ι hχ l)) := rfl

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_LamPerf =====
section

/-!
# S4-CurveDuality O5d-3: the parabolic block over `Λ` from the block over `ℤ/N`

In the coordinates `eL`, `eR` of `LamCoord`, the parabolic block of the constant pairing at any coefficient ring
`k ← ℤ/N` is the matrix pairing of `ι(M)`, `M_ij = -Σ_s U_ij(t_s)` (`U_ij` primitives of `χ_i ∪ χ_j` over `ℤ/N`).
Hence perfectness over `ℤ/N` (an invertible `M`) gives perfectness over every `Λ` (`parabolic_of_zmod`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

variable {N : ℕ} [NeZero N] {k : Type} [CommRing k] (ι : ZMod N →+* k)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} [Fintype S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}
  {r : ℕ} {χ : Fin r → Γ → ZMod N} {e : Fin r → Γ}

/-- Level-`ℤ/N` primitives: `χ_i(g) χ_j(h) = U_ij(h) - U_ij(gh) + U_ij(g)`, `U_ij` locally constant. -/
def IsPrimFam (χ : Fin r → Γ → ZMod N) (U : Fin r → Fin r → Γ → ZMod N) : Prop :=
  ∀ i j, IsLocallyConstant (U i j) ∧ ∀ g h, χ i g * χ j h = U i j h - U i j (g * h) + U i j g

variable (t) in
/-- The intersection matrix `M_ij = -Σ_s U_ij(t_s)`. -/
def lamMat (U : Fin r → Fin r → Γ → ZMod N) : Matrix (Fin r) (Fin r) (ZMod N) :=
  Matrix.of fun i j => -∑ s, U i j (tG t s)

/-- The level-`k` primitive `Σ_ij λ_i μ_j ι(U_ij)`. -/
def primL (U : Fin r → Fin r → Γ → ZMod N) (l μ : Fin r → k) (g : Γ) : k :=
  ∑ i, ∑ j, l i * (μ j * ι (U i j g))

theorem isPrim_primL {σ : Representation k G k} (htriv : ∀ (g : Γ) (x : k), σ g x = x)
    {U : Fin r → Fin r → Γ → ZMod N} (hU : IsPrimFam χ U) (l μ : Fin r → k) :
    IsPrim σ σ (LinearMap.mul k k) Γ (parHomL ι χ l) (parHomL ι χ μ) (primL ι U l μ) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hU i j).1.eventually_eq x).mono
      fun y hy => ?_, fun g h => ?_⟩
  · simp only [primL, hy]
  · simp only [cupCochain, LinearMap.mul_apply', htriv, parHomL_apply, primL, Finset.sum_mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := congrArg ι ((hU i j).2 g h)
    simp only [map_mul, map_add, map_sub] at this
    linear_combination (l i * μ j) * this

variable [Nonempty S]

/-- **The parabolic block in coordinates** is the matrix pairing of `ι(M)`. -/
theorem pair_eLR {σ : Representation k G k}
    (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {U : Fin r → Fin r → Γ → ZMod N} (hU : IsPrimFam χ U) (l μ : Fin r → k) :
    pairQuotSub (constPair H D) _ _ (constPair_h0 H D) (eL ι hχ hδ hspan l) (eR ι D.triv hχ hδ hspan μ) =
      Matrix.toLinearMap₂' k ((lamMat t U).map ι) l μ := by
  rw [eL_apply, pairQuotSub_apply, eR_coe,
    constPair_mk H D (parZ1c ι hχ l) (parZ1 ι D.triv hχ μ) (primL ι U l μ) (isPrim_primL ι D.triv hU l μ),
    parZ1c_snd]
  simp only [Pi.zero_apply, zero_mul, zero_sub, Finset.sum_neg_distrib]
  rw [Matrix.toLinearMap₂'_apply]
  have hterm : ∀ i j, l i • μ j • (lamMat t U).map ι i j = -∑ s, l i * (μ j * ι (U i j (tG t s))) := by
    intro i j
    simp only [smul_eq_mul, Matrix.map_apply, lamMat, Matrix.of_apply, map_neg, map_sum, mul_neg,
      Finset.mul_sum]
  simp only [hterm, Finset.sum_neg_distrib]
  congr 1
  simp only [primL]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)

/-- **O5d.** If the `ℤ/N`-valued parabolic homomorphisms have a dual basis `χ_i`, `e_j`, then perfectness of the
parabolic block of the constant pairing over `ℤ/N` implies it over every coefficient ring `Λ ← ℤ/N`. -/
theorem parabolic_of_zmod {Λ : Type} [CommRing Λ] (ιΛ : ZMod N →+* Λ)
    {σ0 : Representation (ZMod N) G (ZMod N)} {σΛ : Representation Λ G Λ}
    (H0 : CupHyp (Representation.trivial (ZMod N) G (ZMod N)) σ0 σ0 (LinearMap.mul (ZMod N) (ZMod N)) Γ)
    (D0 : ConstData σ0 Γ I t)
    (HΛ : CupHyp (Representation.trivial Λ G Λ) σΛ σΛ (LinearMap.mul Λ Λ) Γ) (DΛ : ConstData σΛ Γ I t)
    (hχ : ∀ i, IsParHom (InBdry I) (χ i)) (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    (h0 : (pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)).IsPerfPair) :
    (pairQuotSub (constPair HΛ DΛ) _ _ (constPair_h0 HΛ DΛ)).IsPerfPair := by
  obtain ⟨U, hU⟩ : ∃ U : Fin r → Fin r → Γ → ZMod N, IsPrimFam χ U := by
    choose U hU using fun i j => exists_prim H0
      (mem_Z1_of_isParHom (σ := Representation.trivial (ZMod N) G (ZMod N)) (fun _ _ => rfl) (hχ i))
      (mem_Z1_of_isParHom D0.triv (hχ j))
    refine ⟨U, fun i j => ⟨(hU i j).1, fun g h => ?_⟩⟩
    have := (hU i j).2 g h
    simpa only [cupCochain, LinearMap.mul_apply', D0.triv] using this
  have hid : (lamMat t U).map (RingHom.id (ZMod N)) = lamMat t U := Matrix.ext fun _ _ => rfl
  have hM : (Matrix.toLinearMap₂' (ZMod N) (lamMat t U)).IsPerfPair := by
    have := h0
    refine LinearMap.IsPerfPair.congr (p := pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0))
      (eM := eL (RingHom.id _) hχ hδ hspan) (eN := eR (RingHom.id _) D0.triv hχ hδ hspan) (q := _) ?_
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    have := pair_eLR (RingHom.id (ZMod N)) H0 D0 hχ hδ hspan hU ((eL (RingHom.id _) hχ hδ hspan).symm x)
      ((eR (RingHom.id _) D0.triv hχ hδ hspan).symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hid] at this
    exact this.symm
  have := isPerfPair_map ιΛ hM
  refine LinearMap.IsPerfPair.congr (p := Matrix.toLinearMap₂' Λ ((lamMat t U).map ιΛ))
    (eM := (eL ιΛ hχ hδ hspan).symm) (eN := (eR ιΛ DΛ.triv hχ hδ hspan).symm) (q := _) ?_
  refine LinearMap.ext fun l => LinearMap.ext fun μ => ?_
  exact pair_eLR ιΛ HΛ DΛ hχ hδ hspan hU l μ

end

end CupDuality
end RamanujanPetersson

end


