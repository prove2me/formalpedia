-- Prove2me | Definitions.Def_OddOrder_GroupTheory_FreeActionOrbitCount
-- name    : OddOrder_GroupTheory_FreeActionOrbitCount
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:14.656849+00:00
-- url     : https://prove2.me/theorems/0b4a8dd6-d656-4f4b-9491-1ab4bfcdc965
-- title:
--   Free-action orbit count
-- statement:
--   A purely combinatorial fact used for Peterfalvi (9.1), the kernel fixed-point-free count (†) in step 3d.3a. A finite group $\Gamma$ of order $d>1$ acting on a finite nonempty type of size $n$ with exactly $1+(n-1)/d$ orbits (and $d\mid n-1$) has every orbit of size $1$ or $d$, and at most one fixed point.
--
--   The main result is `orbit_trivial_or_free_of_card_orbits`, with companion statements on orbit sizes dividing the group order (orbit–stabiliser), fixed points having singleton orbits, and divisibility from a free-off-unique-fixed action. The bundle consists of lemmas only.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/FreeActionOrbitCount.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/FreeActionOrbitCount.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

open MulAction

namespace OddOrder.GroupTheory.FreeActionOrbitCount

variable {Γ S : Type*} [Group Γ] [Finite Γ] [Finite S] [MulAction Γ S]

omit [Finite Γ] [Finite S] in
/-- Each orbit's cardinality divides the group order (orbit–stabiliser). -/
theorem card_orbit_dvd_card_group (x : S) : Nat.card (orbit Γ x) ∣ Nat.card Γ := by
  rw [Nat.card_congr (orbitEquivQuotientStabilizer Γ x)]
  exact (stabilizer Γ x).index_dvd_card

/-- A proper divisor `s` of `d` satisfies `2 * s ≤ d` (its cofactor is `≥ 2`). -/
theorem two_mul_le_of_dvd_of_lt {s d : ℕ} (hdvd : s ∣ d) (_hpos : 0 < s) (hlt : s < d) :
    2 * s ≤ d := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 2 ≤ k := by
    by_contra hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · simp at hlt
    · simp at hlt
  calc 2 * s ≤ k * s := by gcongr
    _ = s * k := mul_comm k s

omit [Finite Γ] [Finite S] in
/-- A fixed point has a singleton orbit. -/
theorem orbit_eq_singleton_of_mem_fixedPoints {x : S} (hx : x ∈ fixedPoints Γ S) :
    orbit Γ x = {x} := by
  ext w
  simp only [Set.mem_singleton_iff, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩; exact (mem_fixedPoints.mp hx) g
  · rintro rfl; exact ⟨1, one_smul _ _⟩

omit [Finite Γ] in
set_option backward.isDefEq.respectTransparency false in
/-- **Free-action orbit count.**  If a finite group `Γ` of order `d > 1` acts on a finite nonempty
type `S` of size `n`, with exactly `1 + (n − 1) / d` orbits and `d ∣ n − 1`, then every orbit has
size `1` or `d`, and there is at most one fixed point.  (For Peterfalvi (9.1): the count carried
over from the free-on-nontrivial-classes side forces freeness on the nontrivial simples.) -/
theorem orbit_trivial_or_free_of_card_orbits [Nonempty S]
    (hd : 1 < Nat.card Γ)
    (horb : Nat.card (orbitRel.Quotient Γ S) = 1 + (Nat.card S - 1) / Nat.card Γ)
    (hdvd : Nat.card Γ ∣ Nat.card S - 1) :
    (∀ x : S, Nat.card (orbit Γ x) = 1 ∨ Nat.card (orbit Γ x) = Nat.card Γ) ∧
      (∀ x y : S, x ∈ fixedPoints Γ S → y ∈ fixedPoints Γ S → x = y) := by
  classical
  set d := Nat.card Γ with hd_def
  have : Fintype (orbitRel.Quotient Γ S) := Fintype.ofFinite _
  have hn_pos : 1 ≤ Nat.card S := Nat.card_pos
  -- per-orbit cardinality facts.
  have hs_dvd : ∀ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit ∣ d := by
    intro ω
    obtain ⟨a, rfl⟩ := Quotient.mk''_surjective ω
    rw [orbitRel.Quotient.orbit_mk]
    exact card_orbit_dvd_card_group a
  have hs_pos : ∀ ω : orbitRel.Quotient Γ S, 0 < Nat.card ω.orbit := by
    intro ω
    obtain ⟨a, rfl⟩ := Quotient.mk''_surjective ω
    rw [orbitRel.Quotient.orbit_mk]
    have : Nonempty (orbit Γ a) := ⟨⟨a, mem_orbit_self a⟩⟩
    have : Finite (orbit Γ a) := Set.finite_coe_iff.mpr (Set.toFinite _)
    exact Nat.card_pos
  have hs_le : ∀ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit ≤ d :=
    fun ω => Nat.le_of_dvd (by omega) (hs_dvd ω)
  -- the partition sum and the count hypothesis give the defect sum `∑ (d - sω) = d - 1`.
  have hsum : ∑ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit = Nat.card S := by
    have : ∀ ω : orbitRel.Quotient Γ S, Finite ω.orbit :=
      fun ω => Set.finite_coe_iff.mpr (Set.toFinite _)
    rw [← Nat.card_sigma]
    exact Nat.card_congr (selfEquivSigmaOrbits' Γ S).symm
  have hdm : d * Nat.card (orbitRel.Quotient Γ S) = Nat.card S + (d - 1) := by
    have hc : d * ((Nat.card S - 1) / d) = Nat.card S - 1 := Nat.mul_div_cancel' hdvd
    rw [horb, mul_add, mul_one, hc]; omega
  have hdefect : ∑ ω : orbitRel.Quotient Γ S, (d - Nat.card ω.orbit) = d - 1 := by
    have h1 : ∑ ω : orbitRel.Quotient Γ S, ((d - Nat.card ω.orbit) + Nat.card ω.orbit)
        = ∑ _ω : orbitRel.Quotient Γ S, d :=
      Finset.sum_congr rfl fun ω _ => Nat.sub_add_cancel (hs_le ω)
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, mul_comm, hdm] at h1
    omega
  -- the "proper" orbits (size `< d`).
  set P : Finset (orbitRel.Quotient Γ S) := Finset.univ.filter (fun ω => Nat.card ω.orbit < d)
    with hP_def
  have hmem_P : ∀ ω, ω ∈ P ↔ Nat.card ω.orbit < d := by intro ω; rw [hP_def]; simp
  -- defects vanish off `P`; the defect sum restricts to `P`.
  have hdefect_P : ∑ ω ∈ P, (d - Nat.card ω.orbit) = d - 1 := by
    rw [← hdefect]
    apply Finset.sum_subset (Finset.subset_univ P)
    intro ω _ hω
    have hnlt : ¬ Nat.card ω.orbit < d := by rwa [hmem_P] at hω
    have : Nat.card ω.orbit = d := le_antisymm (hs_le ω) (by omega)
    omega
  -- each proper orbit contributes a defect with `2 * defect ≥ d`.
  have hbig : ∀ ω ∈ P, d ≤ 2 * (d - Nat.card ω.orbit) := by
    intro ω hω
    have hlt : Nat.card ω.orbit < d := (hmem_P ω).mp hω
    have := two_mul_le_of_dvd_of_lt (hs_dvd ω) (hs_pos ω) hlt
    omega
  -- `#P * d ≤ 2 * (d - 1) < 2 * d`, forcing `#P ≤ 1`.
  have hPcard : P.card ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ P.card := by omega
    have hsum_big : P.card * d ≤ 2 * (d - 1) := by
      calc P.card * d = ∑ _ω ∈ P, d := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ ω ∈ P, 2 * (d - Nat.card ω.orbit) := Finset.sum_le_sum hbig
        _ = 2 * ∑ ω ∈ P, (d - Nat.card ω.orbit) := by rw [Finset.mul_sum]
        _ = 2 * (d - 1) := by rw [hdefect_P]
    have hge : 2 * d ≤ P.card * d := Nat.mul_le_mul_right d h2
    omega
  -- `#P ≥ 1`: the defect sum `d - 1 ≥ 1` is nonzero, so some orbit is proper.
  have hP_pos : 1 ≤ P.card := by
    rcases Nat.eq_zero_or_pos P.card with h0 | h
    · rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hdefect_P
      omega
    · exact h
  have hPcard1 : P.card = 1 := le_antisymm hPcard hP_pos
  obtain ⟨ω₀, hω₀⟩ := Finset.card_eq_one.mp hPcard1
  -- the unique proper orbit `ω₀` has size `1`.
  have hω₀_one : Nat.card ω₀.orbit = 1 := by
    rw [hω₀, Finset.sum_singleton] at hdefect_P
    have := hs_pos ω₀; have := hs_le ω₀; omega
  -- a proper orbit must be `ω₀`.
  have hproper : ∀ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit < d → ω = ω₀ := by
    intro ω hlt
    have : ω ∈ P := (hmem_P ω).mpr hlt
    rw [hω₀] at this
    exact Finset.mem_singleton.mp this
  -- bridge: the orbit of `x` is the quotient-orbit of `⟦x⟧`.
  have horbeq : ∀ x : S, Nat.card (orbit Γ x)
      = Nat.card (orbitRel.Quotient.orbit (Quotient.mk'' x : orbitRel.Quotient Γ S)) :=
    fun x => by rw [orbitRel.Quotient.orbit_mk]
  -- (A): every orbit has size `1` or `d`.
  have hA : ∀ x : S, Nat.card (orbit Γ x) = 1 ∨ Nat.card (orbit Γ x) = d := by
    intro x
    rcases lt_or_ge (Nat.card (orbit Γ x)) d with hlt | hge
    · have hmkω₀ : (Quotient.mk'' x : orbitRel.Quotient Γ S) = ω₀ := hproper _ (horbeq x ▸ hlt)
      left; rw [horbeq x, hmkω₀]; exact hω₀_one
    · exact Or.inr (le_antisymm (by rw [horbeq x]; exact hs_le _) hge)
  refine ⟨hA, ?_⟩
  -- (B): at most one fixed point (two fixed points lie in the unique size-`1` orbit `ω₀`).
  intro x y hx hy
  have hfix1 : ∀ z : S, z ∈ fixedPoints Γ S → (Quotient.mk'' z : orbitRel.Quotient Γ S) = ω₀ := by
    intro z hz
    apply hproper
    rw [← horbeq z, orbit_eq_singleton_of_mem_fixedPoints hz, Nat.card_coe_set_eq,
      Set.ncard_singleton]
    omega
  have hxy : (Quotient.mk'' x : orbitRel.Quotient Γ S) = Quotient.mk'' y := by
    rw [hfix1 x hx, hfix1 y hy]
  have hmem : x ∈ orbit Γ y := Quotient.eq''.mp hxy
  rw [orbit_eq_singleton_of_mem_fixedPoints hy] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- **Forward orbit count** (converse of `orbit_trivial_or_free_of_card_orbits`).  If a finite group
`Γ` acts on a finite type `S` with a *unique* fixed point `x₀` and acts *freely* off it (every
non-fixed orbit has size `|Γ|`), then the number of orbits is `1 + (|S| − 1) / |Γ|`.  (For
Peterfalvi (9.1): the class side — `⟨E⟩` free on the nontrivial classes, trivial class fixed — has
this orbit count, which the Brauer equality then carries to the simples.) -/
theorem card_orbits_eq_of_free_off_unique_fixed
    (x₀ : S) (hx₀ : x₀ ∈ fixedPoints Γ S)
    (huniq : ∀ x : S, x ∈ fixedPoints Γ S → x = x₀)
    (hfree : ∀ x : S, x ∉ fixedPoints Γ S → Nat.card (orbit Γ x) = Nat.card Γ) :
    Nat.card (orbitRel.Quotient Γ S) = 1 + (Nat.card S - 1) / Nat.card Γ := by
  classical
  set d := Nat.card Γ with hd_def
  have : Fintype (orbitRel.Quotient Γ S) := Fintype.ofFinite _
  have : Nonempty (orbitRel.Quotient Γ S) := ⟨Quotient.mk'' x₀⟩
  have hd_pos : 0 < d := Nat.card_pos
  -- the fixed orbit `⟦x₀⟧` has size `1`; every other orbit has size `d`.
  have h1 : Nat.card (orbitRel.Quotient.orbit (Quotient.mk'' x₀ : orbitRel.Quotient Γ S)) = 1 := by
    rw [orbitRel.Quotient.orbit_mk, orbit_eq_singleton_of_mem_fixedPoints hx₀, Nat.card_coe_set_eq,
      Set.ncard_singleton]
  have hd_orbit : ∀ ω : orbitRel.Quotient Γ S, ω ≠ Quotient.mk'' x₀ → Nat.card ω.orbit = d := by
    intro ω hne
    obtain ⟨a, rfl⟩ := Quotient.mk''_surjective ω
    rw [orbitRel.Quotient.orbit_mk]
    exact hfree a fun hmem => hne (by rw [huniq a hmem])
  -- the orbits partition `S`, and the defect sum collapses to the single fixed orbit.
  have hsum : ∑ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit = Nat.card S := by
    have : ∀ ω : orbitRel.Quotient Γ S, Finite ω.orbit :=
      fun ω => Set.finite_coe_iff.mpr (Set.toFinite _)
    rw [← Nat.card_sigma]
    exact Nat.card_congr (selfEquivSigmaOrbits' Γ S).symm
  have hsize_le : ∀ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit ≤ d := by
    intro ω
    obtain ⟨a, rfl⟩ := Quotient.mk''_surjective ω
    rw [orbitRel.Quotient.orbit_mk]
    exact Nat.le_of_dvd hd_pos (card_orbit_dvd_card_group a)
  have hdefect : ∑ ω : orbitRel.Quotient Γ S, (d - Nat.card ω.orbit) = d - 1 := by
    rw [Finset.sum_eq_single (Quotient.mk'' x₀ : orbitRel.Quotient Γ S)]
    · rw [h1]
    · intro ω _ hne; rw [hd_orbit ω hne, Nat.sub_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- `d * #orbits = n + (d - 1)`.
  have hdm : d * Nat.card (orbitRel.Quotient Γ S) = Nat.card S + (d - 1) := by
    have hcancel : ∑ ω : orbitRel.Quotient Γ S, ((d - Nat.card ω.orbit) + Nat.card ω.orbit)
        = ∑ _ω : orbitRel.Quotient Γ S, d :=
      Finset.sum_congr rfl fun ω _ => Nat.sub_add_cancel (hsize_le ω)
    rw [Finset.sum_add_distrib, hsum, hdefect, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card, mul_comm] at hcancel
    omega
  -- divide out by `d`.
  obtain ⟨m', hm'⟩ : ∃ m', Nat.card (orbitRel.Quotient Γ S) = m' + 1 := by
    have := Nat.card_pos (α := orbitRel.Quotient Γ S)
    exact ⟨Nat.card (orbitRel.Quotient Γ S) - 1, by omega⟩
  rw [hm'] at hdm ⊢
  have hdm' : d * m' = Nat.card S - 1 := by
    have hexp : d * (m' + 1) = d * m' + d := Nat.mul_succ d m'
    omega
  rw [show Nat.card S - 1 = d * m' from hdm'.symm, Nat.mul_div_cancel_left _ hd_pos]
  omega

omit [Finite Γ] in
/-- **Divisibility from a free-off-unique-fixed action.**  If a finite group `Γ` acts on a finite
`S` with a unique fixed point `x₀` and acts freely off it, then `|Γ|` divides `|S| − 1`: the
non-fixed points split into free orbits, each of size `|Γ|`.  (For Peterfalvi (9.1): the
divisibility hypothesis `d ∣ |S| − 1` that `orbit_trivial_or_free_of_card_orbits` needs on simples,
obtained from the free structure on the class side and carried over by `|simples| = |classes|`.) -/
theorem dvd_card_sub_one_of_free_off_unique_fixed
    (x₀ : S) (hx₀ : x₀ ∈ fixedPoints Γ S)
    (huniq : ∀ x : S, x ∈ fixedPoints Γ S → x = x₀)
    (hfree : ∀ x : S, x ∉ fixedPoints Γ S → Nat.card (orbit Γ x) = Nat.card Γ) :
    Nat.card Γ ∣ Nat.card S - 1 := by
  classical
  have : Fintype (orbitRel.Quotient Γ S) := Fintype.ofFinite _
  set d := Nat.card Γ with hd_def
  -- orbit sizes sum to `|S|`; the fixed orbit `⟦x₀⟧` has size `1`, every other orbit size `d`.
  have hsum : ∑ ω : orbitRel.Quotient Γ S, Nat.card ω.orbit = Nat.card S := by
    have : ∀ ω : orbitRel.Quotient Γ S, Finite ω.orbit :=
      fun ω => Set.finite_coe_iff.mpr (Set.toFinite _)
    rw [← Nat.card_sigma]
    exact Nat.card_congr (selfEquivSigmaOrbits' Γ S).symm
  have h1 : Nat.card (orbitRel.Quotient.orbit (Quotient.mk'' x₀ : orbitRel.Quotient Γ S)) = 1 := by
    rw [orbitRel.Quotient.orbit_mk, orbit_eq_singleton_of_mem_fixedPoints hx₀, Nat.card_coe_set_eq,
      Set.ncard_singleton]
  have hd_orbit : ∀ ω : orbitRel.Quotient Γ S, ω ≠ Quotient.mk'' x₀ → Nat.card ω.orbit = d := by
    intro ω hne
    obtain ⟨a, rfl⟩ := Quotient.mk''_surjective ω
    rw [orbitRel.Quotient.orbit_mk]
    exact hfree a fun hmem => hne (by rw [huniq a hmem])
  -- splitting off `⟦x₀⟧`: `|S| = 1 + (#orbits − 1)·d`.
  have hsplit : Nat.card S = 1 + (Nat.card (orbitRel.Quotient Γ S) - 1) * d := by
    have hx₀mem := Finset.mem_univ (Quotient.mk'' x₀ : orbitRel.Quotient Γ S)
    rw [← hsum, ← Finset.add_sum_erase _ _ hx₀mem, h1]
    congr 1
    rw [Finset.sum_congr rfl (fun ω hω => hd_orbit ω (Finset.ne_of_mem_erase hω)),
      Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hsplit, Nat.add_sub_cancel_left]
  exact dvd_mul_left d _

end OddOrder.GroupTheory.FreeActionOrbitCount

namespace OddOrder.RepresentationTheory

/-- **A free action of a finite group divides the cardinality of the set acted on.** If a finite
group `Γ` acts on a finite type `β` *freely* — every point has trivial stabilizer — then
`|Γ| ∣ |β|`.  Equivalently (the contrapositive direction used below): if every orbit has the full
size `|Γ|`, the set decomposes as a disjoint union of `|Γ|`-element orbits.

This is the orbit-counting primitive behind Peterfalvi (6.7.1): a `p`-group `P` acting
fixed-point-freely (here `freely`) on a finite set `Ω` forces `|P| ∣ |Ω|`.  The proof is the
free-action decomposition `β ≃ (β / Γ) × Γ` (`MulAction.selfEquivOrbitsQuotientProd`), which makes
`|β| = |β / Γ| · |Γ|`. -/
theorem card_dvd_of_stabilizer_eq_bot {Γ : Type*} [Group Γ] [Finite Γ] {β : Type*} [Finite β]
    [MulAction Γ β] (h : ∀ b : β, MulAction.stabilizer Γ b = ⊥) :
    Nat.card Γ ∣ Nat.card β := by
  -- 名前付き implicit (`α := Γ`) は mathlib 側の変数名リネームで壊れるので、`h` から推論させる。
  have e := MulAction.selfEquivOrbitsQuotientProd h
  rw [Nat.card_congr e, Nat.card_prod]
  exact Dvd.intro_left _ rfl

/-- **A finite group acting with no non-trivial fixed pairs divides the cardinality.** Variant of
`card_dvd_of_stabilizer_eq_bot` whose hypothesis is the form actually checked in Peterfalvi (6.7.1):
no element `x ≠ 1` fixes any point.  (Trivial stabilizers and "no non-identity element fixes a
point" are equivalent for a group action.) -/
theorem card_dvd_of_no_nontrivial_fixed {Γ : Type*} [Group Γ] [Finite Γ] {β : Type*} [Finite β]
    [MulAction Γ β] (h : ∀ (x : Γ), x ≠ 1 → ∀ b : β, x • b ≠ b) :
    Nat.card Γ ∣ Nat.card β := by
  refine card_dvd_of_stabilizer_eq_bot fun b => ?_
  rw [eq_bot_iff]
  intro x hx
  rw [MulAction.mem_stabilizer_iff] at hx
  by_contra hx1
  exact h x (by simpa using hx1) b hx

end OddOrder.RepresentationTheory


