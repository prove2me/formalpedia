-- Prove2me | Definitions.Def_RPLib_FX_GOSC_01
-- name    : RPLib_FX_GOSC_01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:35:52.687549+00:00
-- url     : https://prove2.me/theorems/8c14c731-e1c7-496d-a45a-d2456e79d6dc
-- title:
--   Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 01 of 14
-- statement:
--   File 01 of 14 of the Grothendieck–Ogg–Shafarevich library for the affine line over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Swan_Herb`: S4-Swan (K2), part 1: ramification functions, lower and upper numbering, the Herbrand function
--   * `S4.Def_RP_Swan_Loc`: S4-Swan (K2), part 6: local totally ramified data give a ramification function
--   * `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
--   * `S4.Def_RP_Swan_LocQa`: S4-Swan (K2), part 7: tools for the quotient formula (Serre, Local Fields IV §1 Prop 3)
--   * `S4.Def_RP_Swan_LocQb`: S4-Swan (K2), part 9: the quotient formula `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)`
--   * `S4.Def_RP_Swan_HerbQ`: S4-Swan (K2), part 2: Herbrand's theorem from the quotient formula
--   * `S4.Def_RP_Swan_Rep`: S4-Swan (K2), part 3: the Swan conductor of a representation
--   * `S4.Def_RP_Swan_RepQ`: S4-Swan (K2), part 4: Swan conductor as an upper-numbering integral; quotient compatibility
--   * `S4.Def_RP_Swan_LocQc`: S4-Swan (K2), part 10: the quotient ramification function and Herbrand for local data
--   * `S4.Def_RP_Swan_GlobT`: S4-Swan (K2), part 11: towers of local data (independence of the level)
--   * `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
--   * `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
--   * `S4.Def_RP_GOS_A_Ord`: S4-GOS-A, part 1: the exponent of a height-one prime in an ideal
--   * `S4.Def_RP_GOS_A_Gen`: S4-GOS-A, part 2: the conductor of `A[ϖ]` in a totally ramified extension
--   * `S4.Def_RP_GOS_A_Min`: S4-GOS-A, part 3: the minimal polynomial of an element with trivial stabilizer
--   * `S4.Def_RP_GOS_A_Tot`: S4-GOS-A, part 4: Hilbert's different formula in the totally ramified case
--   * `S4.Def_RP_GOS_A_Unr`: S4-GOS-A, part 5: the inertia ring is unramified
--   * `S4.Def_RP_GOS_B_Per`: S4-GOS-B, part Per: periodicity of Frobenius traces on finite modules, the shifted recurrence at position `0`,
--   * `S4.Def_RP_GOS_B_Seq`: S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex
--   * `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
--   * `S4.Def_RP_GOS_B_Hank`: S4-GOS-B, part Hank: an integer sequence with monic recurrences of bounded order modulo every `l ^ n`
--   * `S4.Def_RP_GOS_B_Loc`: S4-GOS-B, part Loc: local trace bounds from the different (Riemann-Hurwitz input F2)
--   * `S4.Def_RP_GOS_B_Loc2`: S4-GOS-B, part Loc2: sharpness of the trace bound (F4) and residue approximation (R)
--   * `S4.Def_RP_GOS_B_Chart`: S4-GOS-B, part Chart: chart-level inputs for `Cotrace` (approximation, fibres, valuations)
--   * `S4.Def_RP_GOS_B_Inst`: S4-GOS-B, part Inst: the cotrace data of a two-chart extension
--   * `S4.Def_RP_GOS_B_FF`: S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`
--   * `S4.Def_RP_GOS_B_Gal`: S4-GOS-B, part Gal: the charts of a Galois extension of function fields
--   * `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
--   * `S4.Def_RP_GOS_B_Inv`: S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order
--   * `S4.Def_RP_GOS_B_Mob`: S4-GOS-B, part Mob: a class function on cyclic subgroups is determined by its subgroup sums
--   * `S4.Def_RP_GOS_B_Rat`: S4-GOS-B, part Rat: an integral class function with the subgroup sums of `Φ` and Fermat congruences is `Φ`
--   * `S4.Def_RP_GOS_B_Fer`: S4-GOS-B, part Fer: Fermat congruence for characters over `𝔽_l`
--   * `S4.Def_RP_GOS_B_Sub`: S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)
--   * `S4.Def_RP_GOS_B_Shf`: S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)
--
--   **Formalization note.** One file of a library formalizing the Grothendieck–Ogg–Shafarevich formula on the affine line over a finite field: for a lisse sheaf $M$ of finite $\mathbb F_\ell$-vector spaces on $\mathbb A^1_{\mathbb F_q}$ trivialized on a finite étale Galois cover ($\ell \nmid q$), $\dim H^2_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) - \dim H^1_c(\mathbb A^1_{\overline{\mathbb F}_q}, M) = \dim M - \mathrm{Sw}_\infty(M)$, with the cohomology written in continuous cochains of the geometric fundamental group and the Swan conductor in the lower numbering at a place over infinity. It extends the published flat library (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), p. 13; M. Raynaud, Caractéristique d'Euler–Poincaré d'un faisceau et cohomologie des variétés abéliennes, Séminaire Bourbaki, exposé 286 (1965); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapters IV and VI

import Mathlib

/-!
# Grothendieck–Ogg–Shafarevich on the affine line over a finite field, library file 01 of 14

Declarations of the formalization of the Grothendieck–Ogg–Shafarevich formula for lisse sheaves on the affine
line over a finite field (h²_c - h¹_c = rank - Swan conductor at infinity), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Swan_Herb`: S4-Swan (K2), part 1: ramification functions, lower and upper numbering, the Herbrand function
* `S4.Def_RP_Swan_Loc`: S4-Swan (K2), part 6: local totally ramified data give a ramification function
* `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
* `S4.Def_RP_Swan_LocQa`: S4-Swan (K2), part 7: tools for the quotient formula (Serre, Local Fields IV §1 Prop 3)
* `S4.Def_RP_Swan_LocQb`: S4-Swan (K2), part 9: the quotient formula `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)`
* `S4.Def_RP_Swan_HerbQ`: S4-Swan (K2), part 2: Herbrand's theorem from the quotient formula
* `S4.Def_RP_Swan_Rep`: S4-Swan (K2), part 3: the Swan conductor of a representation
* `S4.Def_RP_Swan_RepQ`: S4-Swan (K2), part 4: Swan conductor as an upper-numbering integral; quotient compatibility
* `S4.Def_RP_Swan_LocQc`: S4-Swan (K2), part 10: the quotient ramification function and Herbrand for local data
* `S4.Def_RP_Swan_GlobT`: S4-Swan (K2), part 11: towers of local data (independence of the level)
* `S4.Def_RP_Lefschetz_PtPro`: S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)
* `S4.Def_RP_Lefschetz_PtData`: S4-Lefschetz, L6b: the point data of the trace formula
* `S4.Def_RP_GOS_A_Ord`: S4-GOS-A, part 1: the exponent of a height-one prime in an ideal
* `S4.Def_RP_GOS_A_Gen`: S4-GOS-A, part 2: the conductor of `A[ϖ]` in a totally ramified extension
* `S4.Def_RP_GOS_A_Min`: S4-GOS-A, part 3: the minimal polynomial of an element with trivial stabilizer
* `S4.Def_RP_GOS_A_Tot`: S4-GOS-A, part 4: Hilbert's different formula in the totally ramified case
* `S4.Def_RP_GOS_A_Unr`: S4-GOS-A, part 5: the inertia ring is unramified
* `S4.Def_RP_GOS_B_Per`: S4-GOS-B, part Per: periodicity of Frobenius traces on finite modules, the shifted recurrence at position `0`,
* `S4.Def_RP_GOS_B_Seq`: S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex
* `S4.Def_RP_GOS_B_Cnt`: S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts
* `S4.Def_RP_GOS_B_Hank`: S4-GOS-B, part Hank: an integer sequence with monic recurrences of bounded order modulo every `l ^ n`
* `S4.Def_RP_GOS_B_Loc`: S4-GOS-B, part Loc: local trace bounds from the different (Riemann-Hurwitz input F2)
* `S4.Def_RP_GOS_B_Loc2`: S4-GOS-B, part Loc2: sharpness of the trace bound (F4) and residue approximation (R)
* `S4.Def_RP_GOS_B_Chart`: S4-GOS-B, part Chart: chart-level inputs for `Cotrace` (approximation, fibres, valuations)
* `S4.Def_RP_GOS_B_Inst`: S4-GOS-B, part Inst: the cotrace data of a two-chart extension
* `S4.Def_RP_GOS_B_FF`: S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`
* `S4.Def_RP_GOS_B_Gal`: S4-GOS-B, part Gal: the charts of a Galois extension of function fields
* `S4.Def_RP_GOS_B_TowH`: S4-GOS-B, part TowH: the tower identity for a subgroup
* `S4.Def_RP_GOS_B_Inv`: S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order
* `S4.Def_RP_GOS_B_Mob`: S4-GOS-B, part Mob: a class function on cyclic subgroups is determined by its subgroup sums
* `S4.Def_RP_GOS_B_Rat`: S4-GOS-B, part Rat: an integral class function with the subgroup sums of `Φ` and Fermat congruences is `Φ`
* `S4.Def_RP_GOS_B_Fer`: S4-GOS-B, part Fer: Fermat congruence for characters over `𝔽_l`
* `S4.Def_RP_GOS_B_Sub`: S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)
* `S4.Def_RP_GOS_B_Shf`: S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Swan_Herb =====
section

/-!
# S4-Swan (K2), part 1: ramification functions, lower and upper numbering, the Herbrand function

A *ramification function* on a group `G` (the inertia group of a totally ramified finite Galois extension of
discretely valued fields, so `G = G_0`) is `i : G → ℕ∞` with `i σ = ⊤ ↔ σ = 1`, `1 ≤ i σ`, the ultrametric
inequality `min (i σ) (i τ) ≤ i (σ τ)`, and invariance under inversion and conjugation (Serre, *Local Fields*
IV §1: `i_G(σ) = v_L(σ x - x)` for a generator `x` of the valuation ring).

* lower numbering `G_u = {σ | u + 1 ≤ i σ}` (`lower`), normal subgroups, `G_0 = G`;
* the Herbrand function, defined by Serre's sum formula (IV §3)
  `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` on `ℕ`; `φ(m+1) = φ(m) + |G_{m+1}|/|G|`, strictly monotone, unbounded;
* upper numbering `G^v = G_{ψ(v)}` with `ψ(v) = min {m | v ≤ φ m}` (`upper`), and
  `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1` (`mem_upper`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- A ramification function on a group (the totally ramified case `G = G_0`). -/
structure RamFn (G : Type*) [Group G] where
  /-- `i σ = v_L(σ π - π)`. -/
  i : G → ℕ∞
  i_eq_top : ∀ σ, i σ = ⊤ ↔ σ = 1
  one_le : ∀ σ, 1 ≤ i σ
  le_mul : ∀ σ τ, min (i σ) (i τ) ≤ i (σ * τ)
  i_inv : ∀ σ, i σ⁻¹ = i σ
  i_conj : ∀ σ τ, i (τ * σ * τ⁻¹) = i σ

namespace RamFn

variable {G : Type*} [Group G] (R : RamFn G)

theorem i_one : R.i 1 = ⊤ := (R.i_eq_top 1).2 rfl

theorem i_ne_top {σ : G} (h : σ ≠ 1) : R.i σ ≠ ⊤ := fun h' => h ((R.i_eq_top σ).1 h')

theorem exists_i_eq {σ : G} (h : σ ≠ 1) : ∃ n : ℕ, 1 ≤ n ∧ R.i σ = n := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (R.i_ne_top h)
  refine ⟨n, ?_, hn.symm⟩
  have h1 := R.one_le σ
  rw [← hn] at h1
  exact_mod_cast h1

/-- Ultrametric equality: `i (σ τ) = i τ` when `i τ < i σ`. -/
theorem i_mul_of_lt {σ τ : G} (h : R.i τ < R.i σ) : R.i (σ * τ) = R.i τ := by
  apply le_antisymm
  · have h1 := R.le_mul σ⁻¹ (σ * τ)
    rw [R.i_inv, inv_mul_cancel_left] at h1
    by_contra hc
    exact absurd h1 (not_le.2 (lt_min h (not_le.1 hc)))
  · calc R.i τ = min (R.i σ) (R.i τ) := (min_eq_right h.le).symm
      _ ≤ _ := R.le_mul σ τ

/-- If `σ` has maximal `i` on `σ τ`, then `i (σ τ) = min (i τ) (i σ)` (Serre IV §3, proof of Lemma 5). -/
theorem i_mul_eq_min {σ τ : G} (hmax : R.i (σ * τ) ≤ R.i σ) :
    R.i (σ * τ) = min (R.i τ) (R.i σ) := by
  rcases lt_or_ge (R.i τ) (R.i σ) with h | h
  · rw [R.i_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    exact le_antisymm hmax (le_trans (le_min le_rfl h) (R.le_mul σ τ))

/-- Lower numbering ramification groups `G_u = {σ | u + 1 ≤ i σ}`. -/
def lower (u : ℕ) : Subgroup G where
  carrier := {σ | ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ}
  one_mem' := by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i 1
    rw [R.i_one]; exact le_top
  mul_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (R.le_mul a b)
  inv_mem' := fun {a} ha => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i a⁻¹
    rw [R.i_inv]; exact ha

theorem mem_lower {u : ℕ} {σ : G} : σ ∈ R.lower u ↔ ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ := Iff.rfl

instance lower_normal (u : ℕ) : (R.lower u).Normal where
  conj_mem := fun σ hσ τ => by
    show ((u + 1 : ℕ) : ℕ∞) ≤ R.i (τ * σ * τ⁻¹)
    rw [R.i_conj]; exact hσ

theorem lower_antitone : Antitone R.lower := fun u v h σ hσ => by
  show ((u + 1 : ℕ) : ℕ∞) ≤ R.i σ
  exact le_trans (Nat.cast_le.2 (Nat.succ_le_succ h)) hσ

/-- The lower index `j σ = i σ - 1` (`σ ∈ G_u ↔ u ≤ j σ` for `σ ≠ 1`). -/
def jdx (σ : G) : ℕ := (R.i σ).toNat - 1

theorem mem_lower_iff {σ : G} (h : σ ≠ 1) (u : ℕ) : σ ∈ R.lower u ↔ u ≤ R.jdx σ := by
  obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
  rw [mem_lower, jdx, hn, ENat.toNat_coe, Nat.cast_le]
  omega

/-- The restriction of a ramification function to a subgroup. -/
def restrict (H : Subgroup G) : RamFn H where
  i := fun τ => R.i τ
  i_eq_top := fun τ => by
    rw [R.i_eq_top]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  one_le := fun τ => R.one_le τ
  le_mul := fun σ τ => R.le_mul σ τ
  i_inv := fun τ => R.i_inv τ
  i_conj := fun σ τ => R.i_conj σ τ

theorem restrict_i (H : Subgroup G) (τ : H) : (R.restrict H).i τ = R.i τ := rfl

/-! ## The Herbrand function -/

variable [Fintype G]

/-- `w σ m = min (i σ) (m + 1)` as a natural number. -/
def w (σ : G) (m : ℕ) : ℕ := (min (R.i σ) ((m + 1 : ℕ) : ℕ∞)).toNat

theorem w_one (m : ℕ) : R.w 1 m = m + 1 := by
  rw [w, R.i_one, min_eq_right le_top, ENat.toNat_coe]

theorem w_of_eq {σ : G} {n : ℕ} (h : R.i σ = n) (m : ℕ) : R.w σ m = min n (m + 1) := by
  rw [w, h]
  rcases le_total n (m + 1) with hh | hh
  · rw [min_eq_left (Nat.cast_le.2 hh), min_eq_left hh, ENat.toNat_coe]
  · rw [min_eq_right (Nat.cast_le.2 hh), min_eq_right hh, ENat.toNat_coe]

theorem w_zero (σ : G) : R.w σ 0 = 1 := by
  by_cases h : σ = 1
  · rw [h, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h
    rw [R.w_of_eq hn]; omega

theorem w_succ_of_mem {σ : G} {m : ℕ} (h : σ ∈ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m + 1 := by
  by_cases h1 : σ = 1
  · rw [h1, R.w_one, R.w_one]
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

theorem w_succ_of_not_mem {σ : G} {m : ℕ} (h : σ ∉ R.lower (m + 1)) : R.w σ (m + 1) = R.w σ m := by
  by_cases h1 : σ = 1
  · exact absurd (h1 ▸ (R.lower (m + 1)).one_mem) h
  · obtain ⟨n, hn1, hn⟩ := R.exists_i_eq h1
    rw [mem_lower, hn, Nat.cast_le] at h
    rw [R.w_of_eq hn, R.w_of_eq hn]; omega

/-- The Herbrand function `φ(m) = (1/|G|) ∑_σ min (i σ, m + 1) - 1` (Serre IV §3). -/
def phi (m : ℕ) : ℚ := (∑ σ : G, (R.w σ m : ℚ)) / Nat.card G - 1

theorem cardG_pos : (0 : ℚ) < Nat.card G := by exact_mod_cast Nat.card_pos

theorem phi_zero : R.phi 0 = 0 := by
  have h : (∑ σ : G, (R.w σ 0 : ℚ)) = Nat.card G := by
    simp [R.w_zero, Nat.card_eq_fintype_card]
  rw [phi, h, div_self ((cardG_pos (G := G))).ne', sub_self]

theorem phi_succ (m : ℕ) : R.phi (m + 1) = R.phi m + Nat.card (R.lower (m + 1)) / Nat.card G := by
  classical
  have h : (∑ σ : G, (R.w σ (m + 1) : ℚ)) =
      (∑ σ : G, (R.w σ m : ℚ)) + ∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσ : σ ∈ R.lower (m + 1)
    · rw [R.w_succ_of_mem hσ, if_pos hσ]; push_cast; ring
    · rw [R.w_succ_of_not_mem hσ, if_neg hσ, add_zero]
  have hc : (∑ σ : G, (if σ ∈ R.lower (m + 1) then (1 : ℚ) else 0)) = Nat.card (R.lower (m + 1)) := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [phi, phi, h, hc, add_div]; ring

theorem phi_lt_succ (m : ℕ) : R.phi m < R.phi (m + 1) := by
  rw [R.phi_succ]
  have : (0 : ℚ) < Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
  linarith [div_pos this (cardG_pos (G := G))]

theorem phi_strictMono : StrictMono R.phi := strictMono_nat_of_lt_succ R.phi_lt_succ

theorem phi_le_iff {a b : ℕ} : R.phi a ≤ R.phi b ↔ a ≤ b := R.phi_strictMono.le_iff_le

theorem phi_ge (m : ℕ) : (m : ℚ) / Nat.card G ≤ R.phi m := by
  induction m with
  | zero => rw [R.phi_zero]; simp
  | succ m ih =>
    rw [R.phi_succ]
    have h1 : (1 : ℚ) ≤ Nat.card (R.lower (m + 1)) := by exact_mod_cast Nat.card_pos
    have h2 : (1 : ℚ) / Nat.card G ≤ Nat.card (R.lower (m + 1)) / Nat.card G :=
      div_le_div_of_nonneg_right h1 (cardG_pos (G := G)).le
    have h3 : ((m + 1 : ℕ) : ℚ) / Nat.card G = (m : ℚ) / Nat.card G + 1 / Nat.card G := by
      push_cast; ring
    linarith

theorem exists_le_phi (v : ℚ) : ∃ m : ℕ, v ≤ R.phi m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (v * Nat.card G)
  refine ⟨m, le_trans ?_ (R.phi_ge m)⟩
  rw [le_div_iff₀ (cardG_pos (G := G))]; exact hm.le

/-! ## Upper numbering -/

/-- `ψ(v) = min {m | v ≤ φ m}`. -/
def upperIdx (v : ℚ) : ℕ := Nat.find (R.exists_le_phi v)

/-- Upper numbering ramification groups `G^v = G_{ψ(v)}`. -/
def upper (v : ℚ) : Subgroup G := R.lower (R.upperIdx v)

instance upper_normal (v : ℚ) : (R.upper v).Normal := R.lower_normal _

theorem upperIdx_le_iff (v : ℚ) (n : ℕ) : R.upperIdx v ≤ n ↔ v ≤ R.phi n := by
  rw [upperIdx, Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, hv⟩; exact le_trans hv (R.phi_le_iff.2 hm)
  · intro h; exact ⟨n, le_rfl, h⟩

/-- `σ ∈ G^v ↔ v ≤ φ(i σ - 1)` for `σ ≠ 1`. -/
theorem mem_upper {σ : G} (h : σ ≠ 1) (v : ℚ) : σ ∈ R.upper v ↔ v ≤ R.phi (R.jdx σ) := by
  rw [upper, R.mem_lower_iff h, R.upperIdx_le_iff]

end RamFn

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_Loc =====
section

/-!
# S4-Swan (K2), part 6: local totally ramified data give a ramification function

`LocData G L`: a finite group `G` acting faithfully on a field `L`, a `G`-invariant discrete valuation
`v : L → ℤ ∪ {⊤}` with a uniformizer `ϖ` (`v ϖ = 1`), and the residue condition `res`: every integral `x` is
congruent mod `𝔭` to a `G`-invariant element (residue field of `L^G` = residue field of `L`, `G` acts trivially on it).
No completeness and no monogenicity are assumed: `res` gives the successive approximation that replaces
`B = A[ϖ]` (Serre, Local Fields IV §1). Then (`lb`) `v(σ ϖ_H - ϖ_H) ≤ v(σ x - x)` for every integral `H`-invariant
`x` and every element `ϖ_H` of `L^H` of minimal valuation, so `i(σ) = v(σ ϖ - ϖ)` is independent of `ϖ` and
defines a `RamFn G` (`LocData.ramFn`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

/-- `ℤ ∪ {⊤} → ℕ∞`, truncating negatives. -/
def toENat (w : WithTop ℤ) : ℕ∞ := WithTop.map Int.toNat w

theorem toENat_top : toENat ⊤ = ⊤ := rfl

theorem toENat_coe (m : ℤ) : toENat (m : WithTop ℤ) = (m.toNat : ℕ∞) := rfl

theorem toENat_eq_top_iff (w : WithTop ℤ) : toENat w = ⊤ ↔ w = ⊤ := WithTop.map_eq_top_iff

theorem toENat_mono : Monotone toENat := by
  intro a b h
  induction b with
  | top => rw [toENat_top]; exact le_top
  | coe b =>
    induction a with
    | top => exact absurd h (by simp)
    | coe a =>
      rw [toENat_coe, toENat_coe]
      exact_mod_cast Int.toNat_le_toNat (WithTop.coe_le_coe.1 h)

theorem eq_top_of_forall_nat_le {w : WithTop ℤ} (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ w) : w = ⊤ := by
  induction w with
  | top => rfl
  | coe m =>
    exfalso
    have := h (m.toNat + 1)
    rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
    omega

variable (G L : Type*) [Group G] [Field L] [MulSemiringAction G L]

/-- Local totally ramified data (see the module docstring). -/
structure LocData where
  v : AddValuation L (WithTop ℤ)
  v_smul : ∀ (σ : G) (x : L), v (σ • x) = v x
  faithful : ∀ σ : G, (∀ x : L, σ • x = x) → σ = 1
  ϖ : L
  v_ϖ : v ϖ = 1
  res : ∀ x : L, 0 ≤ v x → ∃ a : L, (∀ σ : G, σ • a = a) ∧ 1 ≤ v (x - a)

namespace LocData

variable {G L} (D : LocData G L)

theorem v_sub_smul_nonneg (σ : G) {x : L} (hx : 0 ≤ D.v x) : 0 ≤ D.v (σ • x - x) :=
  D.v.map_le_sub (by rw [D.v_smul]; exact hx) hx

/-- Successive approximation through `res`, the key estimate: for `ϖH ∈ L^H` with `v ϖH = e` and `res` at
level `e` on `L^H`, `v(σ ϖH - ϖH) ≤ v(σ x - x)` for integral `x ∈ L^H`. -/
theorem lb (H : Subgroup G) (e : ℕ) (he : 1 ≤ e) {ϖH : L} (hfix : ∀ h ∈ H, h • ϖH = ϖH)
    (hv : D.v ϖH = e)
    (resH : ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      ∃ a : L, (∀ σ : G, σ • a = a) ∧ (e : WithTop ℤ) ≤ D.v (x - a))
    (σ : G) {x : L} (hxH : ∀ h ∈ H, h • x = x) (hx : 0 ≤ D.v x) :
    D.v (σ • ϖH - ϖH) ≤ D.v (σ • x - x) := by
  set V := D.v (σ • ϖH - ϖH)
  have hne : ϖH ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hϖ0 : 0 ≤ D.v ϖH := by rw [hv]; exact_mod_cast Nat.zero_le e
  have hV0 : 0 ≤ V := D.v_sub_smul_nonneg σ hϖ0
  have step : ∀ n : ℕ, ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
      min V (n : WithTop ℤ) ≤ D.v (σ • x - x) := by
    intro n
    induction n with
    | zero =>
      intro x _ hx
      exact (min_le_right _ _).trans (by exact_mod_cast D.v_sub_smul_nonneg σ hx)
    | succ n ih =>
      intro x hxH hx
      obtain ⟨a, ha, hva⟩ := resH x hxH hx
      set y := (x - a) * ϖH⁻¹ with hy
      have hxy : x = a + ϖH * y := by rw [hy]; field_simp; ring
      have hyH : ∀ h ∈ H, h • y = y := fun h hh => by
        rw [hy, smul_mul', smul_sub, smul_inv'', hxH h hh, ha h, hfix h hh]
      have hy0 : 0 ≤ D.v y := by
        have h1 : D.v (x - a) = e + D.v y := by
          rw [show x - a = ϖH * y by rw [hxy]; ring, AddValuation.map_mul, hv]
        rw [h1] at hva
        have h2 : (e : WithTop ℤ) + 0 ≤ (e : WithTop ℤ) + D.v y := by rwa [add_zero]
        exact (WithTop.add_le_add_iff_left (WithTop.natCast_ne_top e)).1 h2
      have hσx : σ • x - x = (σ • ϖH - ϖH) * (σ • y) + ϖH * (σ • y - y) := by
        rw [hxy, smul_add, smul_mul', ha σ]; ring
      rw [hσx]
      refine le_trans ?_ (D.v.map_add _ _)
      refine le_min ?_ ?_
      · rw [AddValuation.map_mul, D.v_smul]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right hy0)
      · rw [AddValuation.map_mul, hv]
        have := ih y hyH hy0
        calc min V ((n + 1 : ℕ) : WithTop ℤ) ≤ (e : WithTop ℤ) + min V (n : WithTop ℤ) := by
              rcases min_choice V (n : WithTop ℤ) with h | h <;> rw [h]
              · exact (min_le_left _ _).trans (le_add_of_nonneg_left (by exact_mod_cast Nat.zero_le e))
              · refine (min_le_right _ _).trans ?_
                rw [← Nat.cast_add]; exact_mod_cast (by omega : n + 1 ≤ e + n)
          _ ≤ (e : WithTop ℤ) + D.v (σ • y - y) := add_le_add le_rfl this
  rcases eq_or_ne V ⊤ with hVt | hVt
  · have hall : ∀ n : ℕ, (n : WithTop ℤ) ≤ D.v (σ • x - x) := fun n => by
      have h := step n x hxH hx
      rwa [hVt, min_eq_right le_top] at h
    rw [eq_top_of_forall_nat_le hall]; exact le_top
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hVt
    have hm0 : 0 ≤ m := by rw [← hm] at hV0; exact_mod_cast hV0
    have h := step m.toNat x hxH hx
    have hc : ((m.toNat : ℕ) : WithTop ℤ) = (m : WithTop ℤ) := by
      rw [← WithTop.coe_natCast, Int.toNat_of_nonneg hm0]
    rw [← hm, hc, min_self] at h
    rw [← hm]; exact h

theorem mem_bot_fix (x : L) : ∀ h ∈ (⊥ : Subgroup G), h • x = x := fun h hh => by
  rw [Subgroup.mem_bot.1 hh, one_smul]

/-- `v(σ ϖ - ϖ) ≤ v(σ x - x)` for all integral `x`, for any uniformizer `ϖ'`. -/
theorem lb_bot {ϖ' : L} (hv : D.v ϖ' = 1) (σ : G) {x : L} (hx : 0 ≤ D.v x) :
    D.v (σ • ϖ' - ϖ') ≤ D.v (σ • x - x) :=
  D.lb ⊥ 1 le_rfl (mem_bot_fix ϖ') (by rw [hv]; rfl)
    (fun x _ hx => by obtain ⟨a, ha, h⟩ := D.res x hx; exact ⟨a, ha, by exact_mod_cast h⟩) σ
    (mem_bot_fix x) hx

/-- Independence of the uniformizer. -/
theorem v_unif_eq {ϖ₁ ϖ₂ : L} (h₁ : D.v ϖ₁ = 1) (h₂ : D.v ϖ₂ = 1) (σ : G) :
    D.v (σ • ϖ₁ - ϖ₁) = D.v (σ • ϖ₂ - ϖ₂) :=
  le_antisymm (D.lb_bot h₁ σ (by rw [h₂]; exact zero_le_one))
    (D.lb_bot h₂ σ (by rw [h₁]; exact zero_le_one))

theorem v_inv_nonneg {x : L} (hx : D.v x < 0) : 0 ≤ D.v x⁻¹ := by
  rw [AddValuation.map_inv]
  induction hvx : D.v x with
  | top => rw [hvx] at hx; exact absurd hx (not_lt.2 le_top)
  | coe m =>
    rw [hvx] at hx
    have : m < 0 := by exact_mod_cast hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (by omega : (0 : ℤ) ≤ -m)

theorem eq_one_of_fix_ϖ {σ : G} (h : σ • D.ϖ = D.ϖ) : σ = 1 := by
  have hO : ∀ x : L, 0 ≤ D.v x → σ • x = x := fun x hx => by
    have := D.lb_bot D.v_ϖ σ hx
    rw [h, sub_self, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact sub_eq_zero.1 this
  refine D.faithful σ fun x => ?_
  rcases le_or_gt 0 (D.v x) with hx | hx
  · exact hO x hx
  · have := hO x⁻¹ (D.v_inv_nonneg hx)
    rw [smul_inv''] at this
    exact inv_injective this

/-- The ramification function `i(σ) = v(σ ϖ - ϖ)`. -/
def ramFn : RamFn G where
  i σ := toENat (D.v (σ • D.ϖ - D.ϖ))
  i_eq_top σ := by
    rw [toENat_eq_top_iff, AddValuation.top_iff, sub_eq_zero]
    exact ⟨D.eq_one_of_fix_ϖ, fun h => by rw [h, one_smul]⟩
  one_le σ := by
    have : (1 : WithTop ℤ) ≤ D.v (σ • D.ϖ - D.ϖ) :=
      D.v.map_le_sub (by rw [D.v_smul, D.v_ϖ]) (by rw [D.v_ϖ])
    have h2 := toENat_mono this
    rwa [show toENat 1 = 1 from rfl] at h2
  le_mul σ τ := by
    rw [← toENat_mono.map_min]
    apply toENat_mono
    have : (σ * τ) • D.ϖ - D.ϖ = σ • (τ • D.ϖ - D.ϖ) + (σ • D.ϖ - D.ϖ) := by
      rw [mul_smul, smul_sub]; ring
    rw [this, min_comm]
    refine le_trans ?_ (D.v.map_add _ _)
    rw [D.v_smul]
  i_inv σ := by
    congr 1
    have : σ⁻¹ • D.ϖ - D.ϖ = σ⁻¹ • (D.ϖ - σ • D.ϖ) := by
      rw [smul_sub, inv_smul_smul]
    rw [this, D.v_smul, AddValuation.map_sub_swap]
  i_conj σ τ := by
    congr 1
    have : (τ * σ * τ⁻¹) • D.ϖ - D.ϖ = τ • (σ • (τ⁻¹ • D.ϖ) - τ⁻¹ • D.ϖ) := by
      rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
    rw [this, D.v_smul]
    exact D.v_unif_eq (by rw [D.v_smul, D.v_ϖ]) D.v_ϖ σ

theorem ramFn_i (σ : G) : D.ramFn.i σ = toENat (D.v (σ • D.ϖ - D.ϖ)) := rfl

/-- `i(σ)` through any uniformizer. -/
theorem ramFn_i_of_unif {ϖ' : L} (h : D.v ϖ' = 1) (σ : G) :
    D.ramFn.i σ = toENat (D.v (σ • ϖ' - ϖ')) := by
  rw [ramFn_i, D.v_unif_eq D.v_ϖ h]

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_GlobV =====
section

/-!
# S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group

For a Dedekind domain `S` with fraction field `L` and a height-one prime `P`, `adicAdd P` is the `P`-adic
valuation of `L` as an `AddValuation L (WithTop ℤ)` (`-log` of Mathlib's multiplicative `P.valuation L`).
It has a uniformizer, integral elements are approximated by elements of `S` modulo `P`, and it is invariant
under every automorphism of `S` (compatibly extended to `L`) that stabilizes `P`.

If a finite group `G` is a Galois group for `S / R` (`IsGaloisGroup G R S`) and `S ⧸ P` is finite, every element
of `S` is congruent mod `P` to an element fixed by the inertia group `I = P.inertia G` (the residue field
extension of `S` over `S^I` is trivial: `card_stabilizer_eq_card_inertia_mul_finrank` with stabilizer = inertia
= `I`). Hence `(I, L, adicAdd P)` is local data (`inertiaLocData`), so `Swan.LocData.ramFn` applies.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped Pointwise

namespace RamanujanPetersson.Swan

theorem withTop_eq_of_natCast_le_iff {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, (n : WithTop ℤ) ≤ a ↔ (n : WithTop ℤ) ≤ b) : a = b := by
  induction a with
  | top =>
    induction b with
    | top => rfl
    | coe b =>
      have := (h (b.toNat + 1)).1 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
  | coe a =>
    induction b with
    | top =>
      have := (h (a.toNat + 1)).2 le_top
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at this
      omega
    | coe b =>
      have ha' : 0 ≤ a := by exact_mod_cast ha
      have hb' : 0 ≤ b := by exact_mod_cast hb
      have h1 := (h a.toNat).1 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      have h2 := (h b.toNat).2 (by rw [← WithTop.coe_natCast, WithTop.coe_le_coe]; omega)
      rw [← WithTop.coe_natCast, WithTop.coe_le_coe] at h1 h2
      congr 1
      omega

section AdicAdd

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

section Smul

variable {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

end Smul

end AdicAdd

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

include R in
attribute [local instance] Ideal.Quotient.field in
/-- Every element of `S` is congruent mod `Q` to an element fixed by the inertia group of `Q`. -/
theorem exists_inertia_fixed_sub_mem (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)] (b : S) :
    ∃ a : S, (∀ σ ∈ Q.inertia G, σ • a = a) ∧ b - a ∈ Q := by
  set I := Q.inertia G with hI
  let A := FixedPoints.subalgebra R S I
  haveI : Algebra.IsInvariant A S I := IsGaloisGroup.isInvariant
  haveI : Algebra.IsIntegral A S := Algebra.IsInvariant.isIntegral A S I
  let p := Q.under A
  have : Finite (A ⧸ p) :=
    Finite.of_injective (algebraMap (A ⧸ p) (S ⧸ Q)) (RingHom.injective _)
  have : Finite p.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := I) p Q
  have hinert : Q.inertia I = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true]
    exact σ.2
  rw [hinert, Subgroup.card_top] at hcard
  have hle : Nat.card I * Q.inertiaDeg A ≤ Nat.card I * 1 := by
    rw [mul_one, ← hcard]; exact Subgroup.card_le_card_group _
  rw [Ideal.inertiaDeg_eq_of_isMaximal p Q] at hle
  haveI : Module.Finite (A ⧸ p) (S ⧸ Q) := Module.Finite.of_finite
  haveI : Module.Free (A ⧸ p) (S ⧸ Q) := Module.Free.of_divisionRing _ _
  have hpos : 0 < Module.finrank (A ⧸ p) (S ⧸ Q) := Module.finrank_pos
  have h1 : Module.finrank (A ⧸ p) (S ⧸ Q) = 1 := by
    have := Nat.le_of_mul_le_mul_left hle Nat.card_pos
    omega
  have hsurj : Function.Surjective (algebraMap (A ⧸ p) (S ⧸ Q)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
  obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk Q b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨(a : S), fun σ hσ => a.2 ⟨σ, hσ⟩, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Ideal.Quotient.algebraMap_mk_of_liesOver]
  rfl

end Residue

section Inertia

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

end Inertia

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_Swan_LocQa =====
section

/-!
# S4-Swan (K2), part 7: tools for the quotient formula (Serre, Local Fields IV §1 Prop 3)

For `H` normal in `G` and `ϖH ∈ L^H` with `v ϖH = |H|`, where `v(L^H \ 0) ⊆ |H| ℤ` (`QData`):
`v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)` for `σ ∉ H` (`v_quot`). Serre's proof with `f = ∏_{h ∈ H} (X - h ϖ)`;
monogenicity `B = A[ϖ]` is replaced by successive approximation through `res` (`approx`) plus the fact that
`∑_{k < |H|} c_k ϖ^k` with `c_k ∈ L^H` has the valuation of its smallest term (`v_sum_le_of_distinct`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Polynomial

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- Integral `H`-fixed elements. -/
def intSub (H : Subgroup G) : Subring L where
  carrier := {x | (∀ h ∈ H, h • x = x) ∧ 0 ≤ D.v x}
  mul_mem' := fun ha hb => ⟨fun h hh => by rw [smul_mul', ha.1 h hh, hb.1 h hh],
    by rw [AddValuation.map_mul]; exact add_nonneg ha.2 hb.2⟩
  one_mem' := ⟨fun h _ => smul_one h, (AddValuation.map_one D.v).symm.le⟩
  add_mem' := fun ha hb => ⟨fun h hh => by rw [smul_add, ha.1 h hh, hb.1 h hh],
    D.v.map_le_add ha.2 hb.2⟩
  zero_mem' := ⟨fun h _ => smul_zero h, by rw [AddValuation.map_zero]; exact le_top⟩
  neg_mem' := fun ha => ⟨fun h hh => by rw [smul_neg, ha.1 h hh],
    by rw [AddValuation.map_neg]; exact ha.2⟩

theorem mem_intSub {H : Subgroup G} {x : L} :
    x ∈ D.intSub H ↔ (∀ h ∈ H, h • x = x) ∧ 0 ≤ D.v x := Iff.rfl

/-- All coefficients of `p` lie in `T`. -/
def CoeffIn (T : Subring L) (p : L[X]) : Prop := ∀ k, p.coeff k ∈ T

omit [MulSemiringAction G L] in
theorem coeffIn_mul {T : Subring L} {p q : L[X]} (hp : CoeffIn T p) (hq : CoeffIn T q) :
    CoeffIn T (p * q) := fun k => by
  rw [coeff_mul]; exact T.sum_mem fun x _ => T.mul_mem (hp _) (hq _)

omit [MulSemiringAction G L] in
theorem coeffIn_prod {ι : Type*} {T : Subring L} (s : Finset ι) (f : ι → L[X])
    (hf : ∀ i ∈ s, CoeffIn T (f i)) : CoeffIn T (∏ i ∈ s, f i) :=
  Finset.prod_induction f (CoeffIn T) (fun _ _ => coeffIn_mul)
    (fun k => by rw [coeff_one]; split_ifs; exacts [T.one_mem, T.zero_mem]) hf

omit [MulSemiringAction G L] in
theorem coeffIn_X_sub_C {T : Subring L} {c : L} (hc : c ∈ T) : CoeffIn T (X - C c) := fun k => by
  rw [coeff_sub, coeff_X, coeff_C]
  refine T.sub_mem ?_ ?_ <;> split_ifs
  exacts [T.one_mem, T.zero_mem, hc, T.zero_mem]

omit [MulSemiringAction G L] in
/-- Division by a monic polynomial stays inside a subring. -/
theorem coeffIn_div {T : Subring L} {p f : L[X]} (hf : f.Monic) (hp : CoeffIn T p)
    (hfT : CoeffIn T f) : CoeffIn T (p /ₘ f) ∧ CoeffIn T (p %ₘ f) := by
  have sub : ∀ q : L[X], CoeffIn T q → (↑q.coeffs : Set L) ⊆ T := fun q hq c hc => by
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hc; exact hq n
  have hfS : (f.toSubring T (sub f hfT)).Monic := by rw [monic_toSubring]; exact hf
  have e1 := map_divByMonic (p := p.toSubring T (sub p hp)) T.subtype hfS
  have e2 := map_modByMonic (p := p.toSubring T (sub p hp)) T.subtype hfS
  rw [map_toSubring, map_toSubring] at e1 e2
  exact ⟨fun k => by rw [← e1, coeff_map]; exact SetLike.coe_mem _,
    fun k => by rw [← e2, coeff_map]; exact SetLike.coe_mem _⟩

theorem v_ϖ_ne_zero : D.ϖ ≠ 0 := fun h0 => by
  have h := D.v_ϖ; rw [h0, AddValuation.map_zero] at h; exact WithTop.top_ne_coe h

/-- Successive approximation: `x ≡ g(ϖ) mod 𝔭^N` with `g` having `G`-fixed integral coefficients. -/
theorem approx (N : ℕ) : ∀ x : L, 0 ≤ D.v x → ∃ g : L[X], CoeffIn (D.intSub ⊤) g ∧
    (N : WithTop ℤ) ≤ D.v (x - g.eval D.ϖ) := by
  induction N with
  | zero =>
    intro x hx
    exact ⟨0, fun k => by rw [coeff_zero]; exact (D.intSub ⊤).zero_mem,
      by rw [eval_zero, sub_zero, Nat.cast_zero]; exact hx⟩
  | succ N ih =>
    intro x hx
    obtain ⟨a, ha, hva⟩ := D.res x hx
    set y := (x - a) * D.ϖ⁻¹ with hy
    have hxa : x - a = D.ϖ * y := by
      rw [hy, mul_comm (x - a), ← mul_assoc, mul_inv_cancel₀ D.v_ϖ_ne_zero, one_mul]
    have hy0 : 0 ≤ D.v y := by
      rw [hxa, AddValuation.map_mul, D.v_ϖ] at hva
      have h2 : (1 : WithTop ℤ) + 0 ≤ 1 + D.v y := by rwa [add_zero]
      exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 h2
    have ha0 : 0 ≤ D.v a := by
      have h := D.v.map_le_sub hx (zero_le_one.trans hva)
      rwa [sub_sub_cancel] at h
    obtain ⟨g, hg, hvg⟩ := ih y hy0
    refine ⟨C a + X * g, fun k => ?_, ?_⟩
    · rcases k with _ | k
      · rw [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
        exact (D.mem_intSub).2 ⟨fun σ _ => ha σ, ha0⟩
      · rw [coeff_add, coeff_C_succ, coeff_X_mul, zero_add]; exact hg k
    · have he : x - (C a + X * g).eval D.ϖ = D.ϖ * (y - g.eval D.ϖ) := by
        rw [eval_add, eval_C, eval_mul, eval_X, mul_sub, ← hxa]; ring
      rw [he, AddValuation.map_mul, D.v_ϖ, Nat.cast_succ, add_comm (N : WithTop ℤ)]
      exact add_le_add le_rfl hvg

theorem v_prod {ι : Type*} (s : Finset ι) (f : ι → L) :
    D.v (∏ i ∈ s, f i) = ∑ i ∈ s, D.v (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem coe_add_one_le {m : ℤ} {w : WithTop ℤ} (h : (m : WithTop ℤ) < w) :
    ((m + 1 : ℤ) : WithTop ℤ) ≤ w := by
  induction w with
  | top => exact le_top
  | coe a => exact WithTop.coe_le_coe.2 (Int.add_one_le_of_lt (WithTop.coe_lt_coe.1 h))

/-- A sum whose nonzero terms have pairwise distinct valuations has the valuation of its smallest term. -/
theorem v_sum_le_of_distinct {ι : Type*} (s : Finset ι) (t : ι → L)
    (hd : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → t i ≠ 0 → D.v (t i) ≠ D.v (t k)) :
    ∀ k ∈ s, D.v (∑ i ∈ s, t i) ≤ D.v (t k) := by
  classical
  intro k hk
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s (fun i => D.v (t i)) ⟨k, hk⟩
  refine le_trans ?_ (hmin k hk)
  by_cases htj : t j = 0
  · rw [htj, AddValuation.map_zero]; exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (fun h => htj ((D.v.top_iff).1 h))
  rw [← Finset.add_sum_erase s t hj]
  refine le_of_eq (AddValuation.map_add_eq_of_lt_left D.v ?_)
  rw [← hm]
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one m)) (D.v.map_le_sum fun i hi => ?_)
  have hi' := Finset.mem_of_mem_erase hi
  refine coe_add_one_le ?_
  rw [hm]
  exact lt_of_le_of_ne (hmin i hi') (hd j hj i hi' (Finset.ne_of_mem_erase hi).symm htj)

theorem le_v_eval (p : L[X]) {N : WithTop ℤ} (hp : ∀ k, N ≤ D.v (p.coeff k * D.ϖ ^ k)) :
    N ≤ D.v (p.eval D.ϖ) := by
  rw [eval_eq_sum, sum_def]; exact D.v.map_le_sum fun k _ => hp k

theorem v_mul_pow (c : L) (k : ℕ) : D.v (c * D.ϖ ^ k) = D.v c + (k : WithTop ℤ) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, D.v_ϖ, nsmul_one]

variable (H : Subgroup G) [Fintype H]

/-- `f = ∏_{h ∈ H} (X - h ϖ)`. -/
def fpol : L[X] := ∏ h : H, (X - C ((h : G) • D.ϖ))

theorem fpol_monic : (D.fpol H).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_fpol : (D.fpol H).natDegree = Fintype.card H := by
  rw [fpol, natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C _)]
  simp

theorem eval_fpol : (D.fpol H).eval D.ϖ = 0 := by
  rw [fpol, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

theorem map_fpol (σ : G) : (D.fpol H).map (MulSemiringAction.toRingHom G L σ) =
    ∏ h : H, (X - C ((σ * h) • D.ϖ)) := by
  rw [fpol, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, mul_smul]

theorem fpol_coeff_fix {h₀ : G} (hh₀ : h₀ ∈ H) (k : ℕ) :
    h₀ • (D.fpol H).coeff k = (D.fpol H).coeff k := by
  have e1 := D.map_fpol H h₀
  have e2 : ∏ h : H, (X - C ((h₀ * h) • D.ϖ)) = D.fpol H :=
    Equiv.prod_comp (Equiv.mulLeft (⟨h₀, hh₀⟩ : H)) (fun h : H => X - C ((h : G) • D.ϖ))
  rw [e2] at e1
  have := congrArg (fun p => p.coeff k) e1
  simpa [coeff_map] using this

theorem fpol_coeffIn : CoeffIn (D.intSub H) (D.fpol H) := by
  have hint : CoeffIn (D.intSub ⊥) (D.fpol H) := coeffIn_prod _ _ fun h _ => coeffIn_X_sub_C
    ((D.mem_intSub).2 ⟨mem_bot_fix _, by rw [D.v_smul, D.v_ϖ]; exact zero_le_one⟩)
  exact fun k => (D.mem_intSub).2
    ⟨fun h₀ hh₀ => D.fpol_coeff_fix H hh₀ k, ((D.mem_intSub).1 (hint k)).2⟩

/-- Hypotheses of the quotient formula: `ϖH ∈ L^H`, `v ϖH = |H|`, `v(L^H \ 0) ⊆ |H| ℤ`. -/
structure QData (ϖH : L) : Prop where
  fix : ∀ h ∈ H, h • ϖH = ϖH
  v_eq : D.v ϖH = (Fintype.card H : ℕ)
  val : ∀ x : L, (∀ h ∈ H, h • x = x) → x ≠ 0 →
    ∃ k : ℤ, D.v x = (((Fintype.card H : ℤ) * k : ℤ) : WithTop ℤ)

variable {D H}

theorem QData.resH {ϖH : L} (hq : D.QData H ϖH) : ∀ x : L, (∀ h ∈ H, h • x = x) → 0 ≤ D.v x →
    ∃ a : L, (∀ σ : G, σ • a = a) ∧ ((Fintype.card H : ℕ) : WithTop ℤ) ≤ D.v (x - a) := by
  intro x hxH hx
  obtain ⟨a, ha, hva⟩ := D.res x hx
  refine ⟨a, ha, ?_⟩
  by_cases h0 : x - a = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  obtain ⟨k, hk⟩ := hq.val (x - a) (fun h hh => by rw [smul_sub, hxH h hh, ha h]) h0
  rw [hk] at hva ⊢
  have h1 : (1 : ℤ) ≤ Fintype.card H * k := WithTop.coe_le_coe.1 (by rw [WithTop.coe_one]; exact hva)
  have hc : (0 : ℤ) ≤ Fintype.card H := Int.natCast_nonneg _
  have hk1 : 1 ≤ k := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  rw [← WithTop.coe_natCast, WithTop.coe_le_coe]
  exact le_mul_of_one_le_right hc hk1

theorem QData.v_term_ne {ϖH : L} (hq : D.QData H ϖH) {c d : L} (hc : ∀ h ∈ H, h • c = c)
    (hd : ∀ h ∈ H, h • d = d) {i j : ℕ} (hi : i < Fintype.card H) (hj : j < Fintype.card H)
    (hij : i ≠ j) (hc0 : c * D.ϖ ^ i ≠ 0) : D.v (c * D.ϖ ^ i) ≠ D.v (d * D.ϖ ^ j) := by
  obtain ⟨m, hm⟩ := hq.val c hc (left_ne_zero_of_mul hc0)
  by_cases hd0 : d = 0
  · rw [hd0, zero_mul, AddValuation.map_zero]
    exact fun h => hc0 ((D.v.top_iff).1 h)
  obtain ⟨n, hn⟩ := hq.val d hd hd0
  rw [D.v_mul_pow, D.v_mul_pow, hm, hn, ← WithTop.coe_natCast, ← WithTop.coe_natCast,
    ← WithTop.coe_add, ← WithTop.coe_add, Ne, WithTop.coe_eq_coe]
  intro h
  have he : (0 : ℤ) ≤ Fintype.card H := Int.natCast_nonneg _
  have hi' : (i : ℤ) < Fintype.card H := by exact_mod_cast hi
  have hj' : (j : ℤ) < Fintype.card H := by exact_mod_cast hj
  have hij' : (i : ℤ) ≠ j := by exact_mod_cast hij
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · have : m + 1 ≤ n := hmn
    nlinarith
  · subst hmn; exact hij' (by linarith)
  · have : n + 1 ≤ m := hmn
    nlinarith

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_LocQb =====
section

/-!
# S4-Swan (K2), part 9: the quotient formula `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)`

Serre, Local Fields IV §1 Prop 3, for `σ ∉ H` (`LocData.v_quot`), from the tools of part 7.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Polynomial

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)
  (H : Subgroup G) [Fintype H]

theorem v_eval_map_fpol (σ : G) :
    D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) =
      ∑ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) := by
  rw [D.map_fpol H σ, eval_prod, D.v_prod]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [eval_sub, eval_X, eval_C, AddValuation.map_sub_swap]

theorem eval_map_fpol_ne_zero {σ : G} (hσ : σ ∉ H) :
    ((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ ≠ 0 := by
  rw [D.map_fpol H σ, eval_prod, Finset.prod_ne_zero_iff]
  intro h _
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h'
  have h1 := D.eq_one_of_fix_ϖ h'.symm
  rw [mul_eq_one_iff_eq_inv] at h1
  exact hσ (h1 ▸ H.inv_mem h.2)

variable {D H}

/-- Serre IV §1 Prop 3 in valuation form: `v(σ ϖH - ϖH) = v(f^σ(ϖ))`. -/
theorem QData.v_quot' [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) := by
  have he : 1 ≤ Fintype.card H := Fintype.card_pos
  have hf := D.fpol_monic H
  have hfT := D.fpol_coeffIn H
  have hϖH0 : 0 ≤ D.v ϖH := by rw [hq.v_eq]; exact_mod_cast Nat.zero_le _
  refine le_antisymm ?_ ?_
  · have h0 : ((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ =
        ((D.fpol H).map (MulSemiringAction.toRingHom G L σ) - D.fpol H).eval D.ϖ := by
      rw [eval_sub, D.eval_fpol, sub_zero]
    rw [h0]
    refine D.le_v_eval _ fun k => ?_
    rw [D.v_mul_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    refine le_trans ?_ (le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le k))
    obtain ⟨hfix, hint⟩ := (D.mem_intSub).1 (hfT k)
    exact D.lb H _ he hq.fix hq.v_eq hq.resH σ hfix hint
  · obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.1
      (fun h => D.eval_map_fpol_ne_zero H hσ ((D.v.top_iff).1 h))
    obtain ⟨g, hg, hvg⟩ := D.approx (B.toNat + 1) ϖH hϖH0
    have hgT : CoeffIn (D.intSub H) (g - C ϖH) := fun k => by
      rw [coeff_sub, coeff_C]
      refine (D.intSub H).sub_mem ?_ ?_
      · obtain ⟨h1, h2⟩ := (D.mem_intSub).1 (hg k)
        exact (D.mem_intSub).2 ⟨fun h _ => h1 h trivial, h2⟩
      · split_ifs
        · exact (D.mem_intSub).2 ⟨hq.fix, hϖH0⟩
        · exact (D.intSub H).zero_mem
    obtain ⟨hqT, hρT⟩ := coeffIn_div hf hgT hfT
    have hdiv := modByMonic_add_div (g - C ϖH) (D.fpol H)
    have hρdeg : ((g - C ϖH) %ₘ D.fpol H).natDegree < Fintype.card H := by
      rw [← D.natDegree_fpol H]
      refine natDegree_modByMonic_lt _ hf fun h1 => ?_
      have := D.natDegree_fpol H
      rw [h1, natDegree_one] at this
      omega
    have hρv : ((B.toNat + 1 : ℕ) : WithTop ℤ) ≤ D.v (((g - C ϖH) %ₘ D.fpol H).eval D.ϖ) := by
      have h2 := congrArg (eval D.ϖ) hdiv
      rw [eval_add, eval_mul, D.eval_fpol, zero_mul, add_zero, eval_sub, eval_C] at h2
      rw [h2, AddValuation.map_sub_swap]; exact hvg
    have hterm : ∀ k, ((B.toNat + 1 : ℕ) : WithTop ℤ) ≤
        D.v (((g - C ϖH) %ₘ D.fpol H).coeff k * D.ϖ ^ k) := by
      intro k
      by_cases hk : k < Fintype.card H
      · refine hρv.trans ?_
        rw [eval_eq_sum_range' hρdeg]
        refine D.v_sum_le_of_distinct _ _ (fun i hi j hj hij hi0 => ?_) k (Finset.mem_range.2 hk)
        exact hq.v_term_ne ((D.mem_intSub).1 (hρT i)).1 ((D.mem_intSub).1 (hρT j)).1
          (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij hi0
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, AddValuation.map_zero]
        exact le_top
    have hgσ : g.map (MulSemiringAction.toRingHom G L σ) = g := by
      ext k
      rw [coeff_map, MulSemiringAction.toRingHom_apply]
      exact ((D.mem_intSub).1 (hg k)).1 σ trivial
    have hdivσ := congrArg (fun p => (p.map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) hdiv
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, hgσ, map_C, eval_add,
      eval_mul, eval_sub, eval_C, MulSemiringAction.toRingHom_apply] at hdivσ
    have hlt : D.v (((D.fpol H).map (MulSemiringAction.toRingHom G L σ)).eval D.ϖ) ≤
        ((B.toNat + 1 : ℕ) : WithTop ℤ) := by
      rw [← hB, ← WithTop.coe_natCast, WithTop.coe_le_coe]
      have := Int.self_le_toNat B
      push_cast; omega
    rw [AddValuation.map_sub_swap,
      show ϖH - σ • ϖH = (ϖH - g.eval D.ϖ) + ((g.eval D.ϖ) - σ • ϖH) by ring, ← hdivσ]
    refine D.v.map_le_add (hlt.trans hvg) (D.v.map_le_add ?_ ?_)
    · refine hlt.trans (D.le_v_eval _ fun k => ?_)
      rw [coeff_map, MulSemiringAction.toRingHom_apply, D.v_mul_pow, D.v_smul, ← D.v_mul_pow]
      exact hterm k
    · rw [AddValuation.map_mul]
      refine le_add_of_nonneg_right (D.le_v_eval _ fun k => ?_)
      rw [coeff_map, MulSemiringAction.toRingHom_apply, D.v_mul_pow, D.v_smul]
      exact add_nonneg ((D.mem_intSub).1 (hqT k)).2 (by exact_mod_cast Nat.zero_le k)

/-- **Quotient formula** (Serre IV §1 Prop 3): `v(σ ϖH - ϖH) = ∑_{h ∈ H} v(σ h ϖ - ϖ)` for `σ ∉ H`. -/
theorem QData.v_quot [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = ∑ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) := by
  rw [hq.v_quot' hσ, D.v_eval_map_fpol H σ]

theorem QData.v_ne_top [H.Normal] {ϖH : L} (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) ≠ ⊤ := by
  rw [hq.v_quot' hσ]
  exact fun h => D.eval_map_fpol_ne_zero H hσ ((D.v.top_iff).1 h)

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_HerbQ =====
section

/-!
# S4-Swan (K2), part 2: Herbrand's theorem from the quotient formula

`π : G →* Q` surjective with kernel `H`, ramification functions `R` on `G` and `S` on `Q` satisfying Serre's
quotient formula (IV §1 Prop 3) `i_Q(s) |H| = ∑_{π σ = s} i_G(σ)` for `s ≠ 1` (`QuotFormula`). Then
(Serre IV §3 Lemma 5, Prop 15, Herbrand's theorem):
* `i_Q(s) - 1 = φ_H(i_G(σ_s) - 1)` for a lift `σ_s` of maximal `i` (`toNat_i_eq`);
* `φ_Q(φ_H(m)) = φ_G(m)` whenever `φ_H(m)` is a natural number (`phi_trans`);
* `π(G^v) = Q^v` (`map_upper`): upper numbering is compatible with quotients.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

namespace RamFn

theorem cast_min_enat (a b : ℕ) : ((min a b : ℕ) : ℕ∞) = min (a : ℕ∞) b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Nat.cast_le.2 h)]
  · rw [min_eq_right h, min_eq_right (Nat.cast_le.2 h)]

variable {G Q : Type*} [Group G] [Group Q] [Fintype G] [Fintype Q] [DecidableEq Q]
  (R : RamFn G) (S : RamFn Q) (π : G →* Q)

/-- The fibre of `π` over `s`. -/
def fib (s : Q) : Finset G := Finset.univ.filter (fun σ => π σ = s)

/-- Serre IV §1 Prop 3: `i_Q(s) |H| = ∑_{π σ = s} i_G(σ)` for `s ≠ 1`. -/
def QuotFormula : Prop :=
  ∀ s : Q, s ≠ 1 → (S.i s).toNat * Nat.card π.ker = ∑ σ ∈ fib π s, (R.i σ).toNat

/-- `∑_σ w σ m = |G| (φ m + 1)`. -/
theorem sum_w {K : Type*} [Group K] [Fintype K] (T : RamFn K) (m : ℕ) :
    (∑ σ : K, (T.w σ m : ℚ)) = Nat.card K * (T.phi m + 1) := by
  rw [phi, sub_add_cancel, mul_div_cancel₀ _ (cardG_pos (G := K)).ne']

variable {π} (hπ : Function.Surjective π)
include R hπ

theorem fib_nonempty (s : Q) : (fib π s).Nonempty := by
  obtain ⟨σ, hσ⟩ := hπ s
  exact ⟨σ, by simp [fib, hσ]⟩

/-- A lift of `s` with maximal `i`. -/
def best (s : Q) : G :=
  Classical.choose (Finset.exists_max_image (fib π s) R.i (fib_nonempty R hπ s))

theorem best_spec (s : Q) :
    R.best hπ s ∈ fib π s ∧ ∀ σ ∈ fib π s, R.i σ ≤ R.i (R.best hπ s) :=
  Classical.choose_spec (Finset.exists_max_image (fib π s) R.i (fib_nonempty R hπ s))

theorem map_best (s : Q) : π (R.best hπ s) = s := by
  have h := (R.best_spec hπ s).1
  simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem best_one : R.best hπ 1 = 1 := by
  rw [← R.i_eq_top]
  have h := (R.best_spec hπ 1).2 1 (by simp [fib])
  rw [R.i_one] at h
  exact top_le_iff.1 h

theorem best_ne_one {s : Q} (hs : s ≠ 1) : R.best hπ s ≠ 1 := fun h => hs (by
  rw [← R.map_best hπ s, h, map_one])

theorem map_best_mul (s : Q) (τ : π.ker) : π (R.best hπ s * τ) = s := by
  rw [map_mul, R.map_best hπ s, (MonoidHom.mem_ker).1 τ.2, mul_one]

theorem i_best_mul (s : Q) (τ : π.ker) :
    R.i (R.best hπ s * τ) = min (R.i τ) (R.i (R.best hπ s)) :=
  R.i_mul_eq_min ((R.best_spec hπ s).2 _ (by simp [fib, R.map_best_mul hπ s τ]))

/-- The fibre over `s` is `σ_s H`. -/
theorem sum_fib {M : Type*} [AddCommMonoid M] (s : Q) (g : G → M) :
    ∑ σ ∈ fib π s, g σ = ∑ τ : π.ker, g (R.best hπ s * τ) := by
  symm
  refine Finset.sum_bij (fun τ _ => R.best hπ s * τ) (fun τ _ => ?_) (fun a _ b _ h => ?_)
    (fun σ hσ => ?_) (fun τ _ => rfl)
  · simp [fib, R.map_best_mul hπ s τ]
  · exact Subtype.ext (mul_left_cancel h)
  · simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨⟨(R.best hπ s)⁻¹ * σ, ?_⟩, Finset.mem_univ _, mul_inv_cancel_left _ _⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, R.map_best hπ s, hσ, inv_mul_cancel]

theorem sum_total {M : Type*} [AddCommMonoid M] (g : G → M) :
    ∑ σ : G, g σ = ∑ s : Q, ∑ τ : π.ker, g (R.best hπ s * τ) := by
  rw [← Finset.sum_fiberwise Finset.univ π g]
  exact Finset.sum_congr rfl fun s _ => R.sum_fib hπ s g

theorem card_eq : (Nat.card G : ℚ) = Nat.card Q * Nat.card π.ker := by
  have h := R.sum_total hπ (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

/-- Serre IV §3 Lemma 5: `i_Q(s) = φ_H(i_G(σ_s) - 1) + 1`. -/
theorem toNat_i_eq (hq : QuotFormula R S π) {s : Q} (hs : s ≠ 1) :
    ((S.i s).toNat : ℚ) = (R.restrict π.ker).phi (R.jdx (R.best hπ s)) + 1 := by
  obtain ⟨n, hn1, hn⟩ := R.exists_i_eq (R.best_ne_one hπ hs)
  have h1 := hq s hs
  rw [R.sum_fib hπ s] at h1
  have h2 : ∀ τ : π.ker, (R.i (R.best hπ s * τ)).toNat = (R.restrict π.ker).w τ (R.jdx (R.best hπ s)) := by
    intro τ
    rw [R.i_best_mul hπ s τ, w, restrict_i, jdx, hn, ENat.toNat_coe, Nat.sub_add_cancel hn1]
  simp_rw [h2] at h1
  have h3 := sum_w (R.restrict π.ker) (R.jdx (R.best hπ s))
  have hH : (0 : ℚ) < Nat.card π.ker := cardG_pos (G := π.ker)
  have h4 : ((S.i s).toNat : ℚ) * Nat.card π.ker = Nat.card π.ker * ((R.restrict π.ker).phi
      (R.jdx (R.best hπ s)) + 1) := by
    rw [← h3]; exact_mod_cast h1
  rw [mul_comm] at h4
  exact mul_left_cancel₀ hH.ne' h4

/-- Serre IV §3 Prop 15 (at the points needed): `φ_Q(n) = φ_G(m)` when `n = φ_H(m)`. -/
theorem phi_trans (hq : QuotFormula R S π) (m n : ℕ) (hmn : (n : ℚ) = (R.restrict π.ker).phi m) :
    S.phi n = R.phi m := by
  have key : ∀ s : Q, ((S.w s n : ℕ) : ℚ) * Nat.card π.ker = ∑ τ : π.ker, (R.w (R.best hπ s * τ) m : ℚ) := by
    intro s
    by_cases hs : s = 1
    · subst hs
      rw [S.w_one, R.best_one hπ]
      simp_rw [one_mul]
      have : ∀ τ : π.ker, R.w τ m = (R.restrict π.ker).w τ m := fun τ => rfl
      simp_rw [this]
      rw [sum_w (R.restrict π.ker) m, ← hmn]; push_cast; ring
    · obtain ⟨a, ha1, ha⟩ := S.exists_i_eq hs
      obtain ⟨b, hb1, hb⟩ := R.exists_i_eq (R.best_ne_one hπ hs)
      have hta := R.toNat_i_eq S hπ hq hs
      rw [ha, ENat.toNat_coe, jdx, hb, ENat.toNat_coe] at hta
      have hk : ∀ τ : π.ker, R.w (R.best hπ s * τ) m = (R.restrict π.ker).w τ (min (b - 1) m) := by
        intro τ
        rw [w, w, R.i_best_mul hπ s τ, hb, restrict_i, min_assoc]
        congr 2
        rw [← cast_min_enat]; congr 1; omega
      simp_rw [hk]
      rw [sum_w (R.restrict π.ker), S.w_of_eq ha, Nat.cast_min]
      have hmono : (R.restrict π.ker).phi (min (b - 1) m) = min ((R.restrict π.ker).phi (b - 1)) ((R.restrict π.ker).phi m) :=
        (R.restrict π.ker).phi_strictMono.monotone.map_min
      rw [hmono, hta]; push_cast; rw [hmn, min_add_add_right]; ring
  have hsum : (∑ s : Q, (S.w s n : ℚ)) * Nat.card π.ker = ∑ σ : G, (R.w σ m : ℚ) := by
    rw [Finset.sum_mul, R.sum_total hπ]
    exact Finset.sum_congr rfl fun s _ => key s
  have hH : (0 : ℚ) < Nat.card π.ker := cardG_pos (G := π.ker)
  have hQ : (0 : ℚ) < Nat.card Q := cardG_pos (G := Q)
  rw [sum_w S, sum_w R, R.card_eq hπ] at hsum
  have : (S.phi n + 1) * (Nat.card Q * Nat.card π.ker) = (R.phi m + 1) * (Nat.card Q * Nat.card π.ker) := by
    linarith
  have := mul_right_cancel₀ (mul_pos hQ hH).ne' this
  linarith

theorem mem_upper_iff_best (hq : QuotFormula R S π) {s : Q} (hs : s ≠ 1) (v : ℚ) :
    s ∈ S.upper v ↔ R.best hπ s ∈ R.upper v := by
  obtain ⟨a, ha1, ha⟩ := S.exists_i_eq hs
  have hta := R.toNat_i_eq S hπ hq hs
  rw [ha, ENat.toNat_coe] at hta
  have hj : ((S.jdx s : ℕ) : ℚ) = (R.restrict π.ker).phi (R.jdx (R.best hπ s)) := by
    rw [jdx, ha, ENat.toNat_coe, Nat.cast_sub ha1]; push_cast; linarith
  rw [S.mem_upper hs, R.mem_upper (R.best_ne_one hπ hs), R.phi_trans S hπ hq _ _ hj]

/-- **Herbrand's theorem**: upper numbering is compatible with quotients, `π(G^v) = Q^v`. -/
theorem map_upper (hq : QuotFormula R S π) (v : ℚ) : (R.upper v).map π = S.upper v := by
  ext s
  rw [Subgroup.mem_map]
  by_cases hs : s = 1
  · subst hs; exact ⟨fun _ => Subgroup.one_mem _, fun _ => ⟨1, Subgroup.one_mem _, map_one π⟩⟩
  rw [R.mem_upper_iff_best S hπ hq hs]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hle := (R.best_spec hπ (π σ)).2 σ (by simp [fib])
    have h1 : σ ≠ 1 := fun h => hs (by rw [h, map_one])
    show ((R.upperIdx v + 1 : ℕ) : ℕ∞) ≤ R.i (R.best hπ (π σ))
    exact le_trans hσ hle
  · intro h; exact ⟨_, h, R.map_best hπ s⟩

end RamFn

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_Rep =====
section

/-!
# S4-Swan (K2), part 3: the Swan conductor of a representation

For a ramification function `R` on a finite group `G` (totally ramified, `G = G_0`) and a finite-dimensional
representation `ρ` of `G` over a field `k`, the Swan conductor (Serre, Local Fields VI §2)
`Sw(ρ) = ∑_{u ≥ 1} (|G_u|/|G|) codim V^{G_u}` (`swan`). It needs no hypothesis on `k`.
In characteristic zero it has the character form
`|G| Sw(ρ) = ∑_σ (i(σ) - 1)(dim V - tr ρ(σ))` (`card_mul_swan`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module

section Fix

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The subspace fixed by a subgroup `H`. -/
def fixd (H : Subgroup G) : Submodule k V := Representation.invariants (ρ.comp H.subtype)

theorem mem_fixd {H : Subgroup G} {v : V} : v ∈ fixd ρ H ↔ ∀ σ ∈ H, ρ σ v = v :=
  ⟨fun h σ hσ => h ⟨σ, hσ⟩, fun h τ => h τ τ.2⟩

/-- Codimension of the fixed space of `H`. -/
def cod (H : Subgroup G) : ℕ := finrank k V - finrank k (fixd ρ H)

theorem fixd_bot : fixd ρ ⊥ = ⊤ := by
  rw [eq_top_iff]; intro v _
  rw [mem_fixd]; intro σ hσ
  rw [Subgroup.mem_bot.1 hσ, map_one, Module.End.one_apply]

theorem cod_bot : cod ρ ⊥ = 0 := by
  rw [cod, fixd_bot, finrank_top, Nat.sub_self]

theorem fixd_anti {H K : Subgroup G} (h : H ≤ K) : fixd ρ K ≤ fixd ρ H := fun _ hv =>
  (mem_fixd ρ).2 fun σ hσ => (mem_fixd ρ).1 hv σ (h hσ)

/-- Inflation: fixed vectors of `H` acting through `π` are the fixed vectors of `π(H)`. -/
theorem fixd_comp {Q : Type*} [Group Q] (ρ' : Representation k Q V) (π : G →* Q) (H : Subgroup G) :
    fixd (ρ'.comp π) H = fixd ρ' (H.map π) := by
  ext v
  rw [mem_fixd, mem_fixd]
  constructor
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ
  · intro h σ hσ
    exact h (π σ) ⟨σ, hσ, rfl⟩

theorem cod_comp {Q : Type*} [Group Q] (ρ' : Representation k Q V) (π : G →* Q) (H : Subgroup G) :
    cod (ρ'.comp π) H = cod ρ' (H.map π) := by
  rw [cod, cod, fixd_comp]

end Fix

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)

/-- An index past every jump of the lower filtration. -/
def top : ℕ := Finset.univ.sup R.jdx

theorem jdx_le_top (σ : G) : R.jdx σ ≤ R.top := Finset.le_sup (Finset.mem_univ σ)

theorem lower_eq_bot {u : ℕ} (hu : R.top ≤ u) : R.lower (u + 1) = ⊥ := by
  rw [eq_bot_iff]; intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra h
  have h1 := (R.mem_lower_iff h (u + 1)).1 hσ
  have h2 := R.jdx_le_top σ
  omega

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The Swan conductor `Sw(ρ) = ∑_{u ≥ 1} (|G_u|/|G|) codim V^{G_u}` (Serre VI §2). -/
def swan : ℚ := ∑ u ∈ Finset.range R.top,
  (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G * cod ρ (R.lower (u + 1))

theorem swan_eq_range {n : ℕ} (hn : R.top ≤ n) : R.swan ρ = ∑ u ∈ Finset.range n,
    (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G * cod ρ (R.lower (u + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [swan, Finset.sum_range_add]
  have h0 : ∀ x ∈ Finset.range d, (Nat.card (R.lower (R.top + x + 1)) : ℚ) / Nat.card G *
      cod ρ (R.lower (R.top + x + 1)) = 0 := by
    intro x _
    rw [R.lower_eq_bot (by omega : R.top ≤ R.top + x), cod_bot]
    simp
  rw [Finset.sum_eq_zero h0, add_zero]

/-- The Swan conductor as a sum of `φ`-increments (the integral of `codim V^{G^v}` over `v > 0`). -/
theorem swan_eq_phi {n : ℕ} (hn : R.top ≤ n) : R.swan ρ = ∑ u ∈ Finset.range n,
    (R.phi (u + 1) - R.phi u) * cod ρ (R.lower (u + 1)) := by
  rw [R.swan_eq_range ρ hn]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [R.phi_succ u, add_sub_cancel_left]

end RamFn

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_RepQ =====
section

/-!
# S4-Swan (K2), part 4: Swan conductor as an upper-numbering integral; quotient compatibility

`G^v = G_{idxR v}` for real `v` (`idxR v` = least `m` with `v ≤ φ(m)`), and
`Sw(ρ) = ∫_0^T codim V^{G^v} dv` for `T ≥ φ(top)` (`swan_eq_integral`). With Herbrand's theorem (`map_upper`)
this gives the quotient compatibility `Sw_G(Infl ρ) = Sw_{G/H}(ρ)` over any field (`swan_comp`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

open Module MeasureTheory

theorem cod_mono {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) {H K : Subgroup G} (h : H ≤ K) : cod ρ H ≤ cod ρ K := by
  unfold cod
  have := Submodule.finrank_mono (fixd_anti ρ h)
  omega

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] (R : RamFn G)

theorem exists_le_phiR (v : ℝ) : ∃ m : ℕ, v ≤ (R.phi m : ℝ) := by
  obtain ⟨m, hm⟩ := R.exists_le_phi ((⌈v⌉ : ℤ) : ℚ)
  refine ⟨m, (Int.le_ceil v).trans ?_⟩
  have : (((⌈v⌉ : ℤ) : ℚ) : ℝ) ≤ (R.phi m : ℝ) := by exact_mod_cast hm
  simpa using this

/-- Upper index for real `v`: the least `m` with `v ≤ φ(m)`, so `G^v = G_{idxR v}`. -/
def idxR (v : ℝ) : ℕ := Nat.find (R.exists_le_phiR v)

theorem idxR_le_iff (v : ℝ) (n : ℕ) : R.idxR v ≤ n ↔ v ≤ (R.phi n : ℝ) := by
  constructor
  · intro h
    exact (Nat.find_spec (R.exists_le_phiR v)).trans (by exact_mod_cast R.phi_strictMono.monotone h)
  · intro h
    exact Nat.find_min' _ h

theorem idxR_mono : Monotone R.idxR := fun v w h => by
  rw [R.idxR_le_iff]
  exact h.trans ((R.idxR_le_iff w _).1 le_rfl)

theorem idxR_eq {v : ℝ} {u : ℕ} (h1 : (R.phi u : ℝ) < v) (h2 : v ≤ (R.phi (u + 1) : ℝ)) :
    R.idxR v = u + 1 := by
  apply le_antisymm ((R.idxR_le_iff v _).2 h2)
  by_contra hlt
  have := (R.idxR_le_iff v u).1 (by omega)
  linarith

theorem idxR_ratCast (q : ℚ) : R.idxR q = R.upperIdx q := by
  apply le_antisymm
  · rw [R.idxR_le_iff]
    exact_mod_cast (R.upperIdx_le_iff q _).1 le_rfl
  · rw [R.upperIdx_le_iff]
    exact_mod_cast (R.idxR_le_iff q _).1 le_rfl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

/-- `v ↦ codim V^{G^v}` for real `v`. -/
def codU (v : ℝ) : ℝ := cod ρ (R.lower (R.idxR v))

theorem codU_antitone : Antitone (R.codU ρ) := fun _ _ h => by
  unfold codU
  exact_mod_cast cod_mono ρ (R.lower_antitone (R.idxR_mono h))

theorem integral_codU_piece (u : ℕ) :
    ∫ v in (R.phi u : ℝ)..(R.phi (u + 1) : ℝ), R.codU ρ v =
      ((R.phi (u + 1) : ℝ) - R.phi u) * cod ρ (R.lower (u + 1)) := by
  have hle : (R.phi u : ℝ) ≤ R.phi (u + 1) := by exact_mod_cast (R.phi_lt_succ u).le
  rw [intervalIntegral.integral_congr_ae' (g := fun _ => (cod ρ (R.lower (u + 1)) : ℝ)) ?_ ?_,
    intervalIntegral.integral_const, smul_eq_mul]
  · exact Filter.Eventually.of_forall fun v hv => by
      unfold codU
      rw [R.idxR_eq hv.1 hv.2]
  · exact Filter.Eventually.of_forall fun v hv => absurd (hv.1.trans_le hv.2) (not_lt.2 hle)

theorem integral_codU_tail {T : ℝ} (hT : (R.phi R.top : ℝ) ≤ T) :
    ∫ v in (R.phi R.top : ℝ)..T, R.codU ρ v = 0 := by
  rw [intervalIntegral.integral_congr_ae' (g := fun _ => (0 : ℝ)) ?_ ?_, intervalIntegral.integral_zero]
  · exact Filter.Eventually.of_forall fun v hv => by
      unfold codU
      have h : R.top + 1 ≤ R.idxR v := by
        by_contra h
        have := (R.idxR_le_iff v R.top).1 (by omega)
        linarith [hv.1]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      rw [hd, show R.top + 1 + d = (R.top + d) + 1 by omega, R.lower_eq_bot (by omega), cod_bot]
      simp
  · exact Filter.Eventually.of_forall fun v hv => absurd (hv.1.trans_le hv.2) (not_lt.2 hT)

/-- `Sw(ρ) = ∫_0^T codim V^{G^v} dv` for any `T ≥ φ(top)`. -/
theorem swan_eq_integral {T : ℝ} (hT : (R.phi R.top : ℝ) ≤ T) :
    (R.swan ρ : ℝ) = ∫ v in (0 : ℝ)..T, R.codU ρ v := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (R.codU ρ) volume a b := fun _ _ =>
    (R.codU_antitone ρ).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 (R.phi R.top)) (hI _ T),
    R.integral_codU_tail ρ hT, add_zero]
  have hs := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := R.codU ρ)
    (a := fun u => (R.phi u : ℝ)) (n := R.top) (fun u _ => hI _ _)
  simp only [R.phi_zero, Rat.cast_zero] at hs
  rw [← hs, R.swan_eq_phi ρ le_rfl]
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [R.integral_codU_piece ρ u]

section Quot

variable {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q] (S : RamFn Q) {π : G →* Q}

theorem map_lower_idxR (hπ : Function.Surjective π) (hq : QuotFormula R S π) (v : ℝ) :
    (R.lower (R.idxR v)).map π = S.lower (S.idxR v) := by
  set q : ℚ := min (R.phi (R.idxR v)) (S.phi (S.idxR v))
  have hv : v ≤ (q : ℝ) := by
    rw [Rat.cast_min]
    exact le_min ((R.idxR_le_iff v _).1 le_rfl) ((S.idxR_le_iff v _).1 le_rfl)
  have hR : R.idxR q = R.idxR v := le_antisymm
    ((R.idxR_le_iff _ _).2 (by rw [Rat.cast_min]; exact min_le_left _ _)) (R.idxR_mono hv)
  have hS : S.idxR q = S.idxR v := le_antisymm
    ((S.idxR_le_iff _ _).2 (by rw [Rat.cast_min]; exact min_le_right _ _)) (S.idxR_mono hv)
  have h := R.map_upper S hπ hq q
  rw [upper, upper, ← R.idxR_ratCast, ← S.idxR_ratCast, hR, hS] at h
  exact h

variable {k' W : Type*} [Field k'] [AddCommGroup W] [Module k' W] [FiniteDimensional k' W]
  (ρ' : Representation k' Q W)

theorem codU_comp (hπ : Function.Surjective π) (hq : QuotFormula R S π) (v : ℝ) :
    R.codU (ρ'.comp π) v = S.codU ρ' v := by
  unfold codU
  rw [cod_comp, R.map_lower_idxR S hπ hq v]

/-- Quotient compatibility of the Swan conductor (Serre VI §2): inflation from `Q = G/H` preserves `Sw`,
over any field. -/
theorem swan_comp (hπ : Function.Surjective π) (hq : QuotFormula R S π) :
    R.swan (ρ'.comp π) = S.swan ρ' := by
  have h1 := R.swan_eq_integral (ρ'.comp π) (le_max_left (R.phi R.top : ℝ) (S.phi S.top))
  have h2 := S.swan_eq_integral ρ' (le_max_right (R.phi R.top : ℝ) (S.phi S.top))
  have h : (R.swan (ρ'.comp π) : ℝ) = S.swan ρ' := by
    rw [h1, h2]
    congr 1
    funext v
    exact R.codU_comp S ρ' hπ hq v
  exact_mod_cast h

end Quot

end RamFn

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_LocQc =====
section

/-!
# S4-Swan (K2), part 10: the quotient ramification function and Herbrand for local data

For `H ⊴ G` and `ϖH` with `D.QData H ϖH`, `nq σ = v(σ ϖH - ϖH)` is right-`H`-invariant, divisible by `|H|`
off `H`, and (quotient formula, part 9) `nq σ = ∑_{h ∈ H} i_G(σ h)`. So `i_{G/H}(σH) := nq σ / |H|` is a
`RamFn (G ⧸ H)` (`QData.ram`) satisfying Serre's `QuotFormula` (`QData.quotFormula`); hence Herbrand's theorem
`π(G^v) = (G/H)^v` (`QData.map_upper`) and `Sw_G(inf ρ) = Sw_{G/H}(ρ)` (`QData.swan_comp`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

theorem natCast_inj' {a b : ℕ} : ((a : ℕ) : WithTop ℤ) = (b : WithTop ℤ) ↔ a = b := by
  rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_eq_coe, Nat.cast_inj]

theorem eq_natCast {w : WithTop ℤ} (h0 : 0 ≤ w) (ht : w ≠ ⊤) :
    w = ((toENat w).toNat : WithTop ℤ) := by
  induction w with
  | top => exact absurd rfl ht
  | coe a =>
    have ha : 0 ≤ a := by exact_mod_cast h0
    rw [toENat_coe, ENat.toNat_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg ha]

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- `v(σ ϖH - ϖH)` as a natural number. -/
def nq (ϖH : L) (σ : G) : ℕ := (toENat (D.v (σ • ϖH - ϖH))).toNat

variable {D} {H : Subgroup G} [Fintype H] {ϖH : L}

theorem QData.v_nonneg (hq : D.QData H ϖH) : 0 ≤ D.v ϖH := by
  rw [hq.v_eq]; exact_mod_cast Nat.zero_le _

theorem QData.v_eq_nq [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.v (σ • ϖH - ϖH) = (D.nq ϖH σ : WithTop ℤ) :=
  eq_natCast (D.v_sub_smul_nonneg σ hq.v_nonneg) (hq.v_ne_top hσ)

/-- `nq σ = ∑_{h ∈ H} i_G(σ h)` (the quotient formula in `ℕ`). -/
theorem QData.nq_sum [H.Normal] (hq : D.QData H ϖH) {σ : G} (hσ : σ ∉ H) :
    D.nq ϖH σ = ∑ h : H, (D.ramFn.i (σ * h)).toNat := by
  have h1 := hq.v_quot hσ
  rw [hq.v_eq_nq hσ] at h1
  have h2 : ∀ h : H, D.v ((σ * h) • D.ϖ - D.ϖ) = ((D.ramFn.i (σ * h)).toNat : WithTop ℤ) := by
    intro h
    rw [ramFn_i]
    refine eq_natCast (D.v_sub_smul_nonneg _ (by rw [D.v_ϖ]; exact zero_le_one)) fun ht => ?_
    have h3 := D.eq_one_of_fix_ϖ (sub_eq_zero.1 ((D.v.top_iff).1 ht))
    rw [mul_eq_one_iff_eq_inv] at h3
    exact hσ (h3 ▸ H.inv_mem h.2)
  rw [Finset.sum_congr rfl fun h _ => h2 h, ← Nat.cast_sum] at h1
  exact natCast_inj'.1 h1

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_GlobT =====
section

/-!
# S4-Swan (K2), part 11: towers of local data (independence of the level)

`LocData.Tower D D' ι r`: local data `D` on `L` (group `G`) and `D'` on `L'` (group `G'`), a field embedding
`ι : L → L'` and a surjection `r : G' → G` with `σ • ι x = ι (r σ • x)`, such that `v' ∘ ι = |ker r| · v` and
`v'` takes values in `|ker r| ℤ` on `ker r`-invariants. Then `ι ϖ` is `QData` for `ker r`, Serre's quotient formula
holds for `(D'.ramFn, D.ramFn, r)`, and the Swan conductor and the upper numbering are compatible with `r`.
This is the level-independence step of the global theory (`L ⊆ L'` two finite levels at a place over `∞`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

namespace LocData

variable {G L G' L' : Type*} [Group G] [Field L] [MulSemiringAction G L]
  [Group G'] [Field L'] [MulSemiringAction G' L']
  (D : LocData G L) (D' : LocData G' L') (ι : L →+* L') (r : G' →* G) [Fintype r.ker]

/-- Tower hypotheses (see the module docstring). -/
structure Tower : Prop where
  surj : Function.Surjective r
  compat : ∀ (σ : G') (x : L), σ • ι x = ι (r σ • x)
  v_iota : ∀ (x : L) (m : ℤ), D.v x = m →
    D'.v (ι x) = (((Fintype.card r.ker : ℤ) * m : ℤ) : WithTop ℤ)
  val : ∀ x : L', (∀ h ∈ r.ker, h • x = x) → x ≠ 0 →
    ∃ k : ℤ, D'.v x = (((Fintype.card r.ker : ℤ) * k : ℤ) : WithTop ℤ)

variable {D D' ι r}

/-- `ι ϖ` is quotient data for `ker r`. -/
theorem Tower.qdata (hT : Tower D D' ι r) : D'.QData r.ker (ι D.ϖ) where
  fix h hh := by rw [hT.compat, (MonoidHom.mem_ker).1 hh, one_smul]
  v_eq := by
    rw [hT.v_iota D.ϖ 1 (by rw [D.v_ϖ]; rfl), mul_one]
    rfl
  val := hT.val

theorem Tower.nq_eq (hT : Tower D D' ι r) {s : G} (hs : s ≠ 1) (σ : G') (hσ : r σ = s) :
    D'.nq (ι D.ϖ) σ = (D.ramFn.i s).toNat * Fintype.card r.ker := by
  have hne : s • D.ϖ - D.ϖ ≠ 0 := by
    intro h0
    exact hs (D.eq_one_of_fix_ϖ (sub_eq_zero.1 h0))
  have h0 : 0 ≤ D.v (s • D.ϖ - D.ϖ) := D.v_sub_smul_nonneg s (by rw [D.v_ϖ]; exact zero_le_one)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, D.v (s • D.ϖ - D.ϖ) = m := by
    induction h : D.v (s • D.ϖ - D.ϖ) with
    | top => exact absurd ((AddValuation.top_iff _).1 h) hne
    | coe a => exact ⟨a, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm] at h0; exact_mod_cast h0
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  have h1 : σ • ι D.ϖ - ι D.ϖ = ι (s • D.ϖ - D.ϖ) := by rw [hT.compat, hσ, map_sub]
  rw [LocData.nq, h1, hT.v_iota _ _ hm, D.ramFn_i, hm, toENat_coe, toENat_coe]
  have : ((Fintype.card r.ker : ℤ) * (k : ℤ)) = ((Fintype.card r.ker * k : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast, Int.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast, mul_comm]

/-- **Serre's quotient formula** along a tower of local data. -/
theorem Tower.quotFormula [Fintype G] [Fintype G'] [DecidableEq G] (hT : Tower D D' ι r) :
    RamFn.QuotFormula D'.ramFn D.ramFn r := by
  intro s hs
  set σ := D'.ramFn.best hT.surj s
  have hσ : r σ = s := D'.ramFn.map_best hT.surj s
  have hσH : σ ∉ r.ker := fun h => hs (by rw [← hσ]; exact h)
  rw [D'.ramFn.sum_fib hT.surj s]
  calc (D.ramFn.i s).toNat * Nat.card r.ker = D'.nq (ι D.ϖ) σ := by
        rw [hT.nq_eq hs σ hσ, Nat.card_eq_fintype_card]
    _ = ∑ h : r.ker, (D'.ramFn.i (σ * h)).toNat := hT.qdata.nq_sum hσH
    _ = _ := by convert rfl

/-- The Swan conductor does not depend on the level. -/
theorem Tower.swan_comp [Fintype G] [Fintype G'] [DecidableEq G] (hT : Tower D D' ι r)
    {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G W) : D'.ramFn.swan (ρ.comp r) = D.ramFn.swan ρ :=
  RamFn.swan_comp D'.ramFn D.ramFn ρ hT.surj hT.quotFormula

end LocData

end

end Swan
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtPro =====
section

/-!
# S4-Lefschetz, L5c3a: Frobenius elements of `π₁(U)` at points (compactness)

* `finite_setOf_pow_eq`, `finite_quot_ker`: points with values in a finite set have finite residue rings.
* `resPt`, `jPt`: restriction `π₁(U) → Gal(L/K)` and the inclusion `O_L → O_{K_U}` (the pro-chart over `A`) for a
  finite unramified Galois level `L`, with `resPt_surjective`, `jPt_smul`.
* `exists_frob_pro`: for a point `w` of the pro-chart with `Fr ∘ w = w` on `A` (finite image), some `F ∈ π₁(U)` has
  `w ∘ F = Fr ∘ w` (finite levels by `hom_smul_trans`, then compactness of `π₁(U)`).
* `IsFrobPt Fr u F` and `exists_isFrobPt`: every point `u` of `A` has a Frobenius element.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtProGen

/-- A set stable under right multiplication by an open subgroup is closed. -/
theorem isClosed_of_mul_mem {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] (U : Subgroup P)
    (hU : IsOpen (U : Set P)) (T : Set P) (hT : ∀ σ ∈ T, ∀ s ∈ U, σ * s ∈ T) : IsClosed T := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun σ hσ => ?_)
  refine ⟨(fun s => σ * s) '' U, ?_, isOpenMap_mul_left σ _ hU, ⟨1, U.one_mem, mul_one σ⟩⟩
  rintro _ ⟨s, hs, rfl⟩ hsT
  apply hσ
  have := hT _ hsT _ (U.inv_mem hs)
  rwa [mul_inv_cancel_right] at this

end PtProGen

section PtPro

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

end PtPro

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtData =====
section

/-!
# S4-Lefschetz, L6b: the point data of the trace formula

* `finite_homs_of_adjoin`: ring maps `R → Ω` out of a finitely generated `k`-algebra, with fixed restriction to `k`
  and values in a finite set, form a finite set.
* `finite_ptSet`: the `F_{q^m}`-points of `U` (ring maps `u : R → Ω` with prescribed restriction to `F_q` and
  `Fr ∘ u = u`, `Fr = (·)^(q^m)`) form a finite set.
* **`exists_ptData`**: a finite set `S` of these points together with normalized Frobenius elements `F_u`: exactly the
  hypotheses `hS`, `hFu` of `lefschetz_twist`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtDataGen

/-- Ring maps out of `R = k[s]` with fixed restriction to `k` and values in a finite set form a finite set. -/
theorem finite_homs_of_adjoin {k R Ω : Type} [CommRing k] [CommRing R] [Algebra k R] [Field Ω]
    (s : Finset R) (hs : Algebra.adjoin k (s : Set R) = ⊤) (c : k →+* Ω) (Z : Set Ω) (hZ : Z.Finite) :
    {u : R →+* Ω | u.comp (algebraMap k R) = c ∧ ∀ a, u a ∈ Z}.Finite := by
  classical
  let f : (R →+* Ω) → (s → Ω) := fun u x => u x
  have hinj : Set.InjOn f {u : R →+* Ω | u.comp (algebraMap k R) = c ∧ ∀ a, u a ∈ Z} := by
    intro u1 h1 u2 h2 h12
    obtain ⟨h1c, -⟩ := h1
    obtain ⟨h2c, -⟩ := h2
    refine RingHom.ext fun a => ?_
    have ha : a ∈ Algebra.adjoin k (s : Set R) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact congrFun h12 ⟨x, hx⟩
    | algebraMap r => exact (RingHom.congr_fun h1c r).trans (RingHom.congr_fun h2c r).symm
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
  refine Set.Finite.of_finite_image ?_ hinj
  have hpi : (Set.univ.pi fun _ : s => Z).Finite := Set.Finite.pi fun _ => hZ
  refine hpi.subset ?_
  rintro _ ⟨u, hu, rfl⟩ x _
  exact hu.2 x

end PtDataGen

section PtData

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e)

end PtData

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_GOS_A_Ord =====
section

/-!
# S4-GOS-A, part 1: the exponent of a height-one prime in an ideal

For a height-one prime `Q` of a Dedekind domain `S`, `ordI Q J` is the exponent of `Q` in the factorization of
the ideal `J` (the exponent in Mathlib's `Q.intValuation`). Multiplicativity, the membership criterion
`n ≤ ordI Q (span {x}) ↔ x ∈ Q ^ n`, products of principal ideals, uniformizers (`ordI = 1`), and one step of
`Q`-adic approximation by multiples of `ϖ ^ n`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped Classical

namespace RamanujanPetersson.GOS

section Ord

variable {S : Type*} [CommRing S] [IsDedekindDomain S] (Q : HeightOneSpectrum S)

/-- The exponent of `Q` in the factorization of an ideal `J`. -/
def ordI (J : Ideal S) : ℕ := (Associates.mk Q.asIdeal).count (Associates.mk J).factors

theorem ordI_mul {J J' : Ideal S} (hJ : J ≠ ⊥) (hJ' : J' ≠ ⊥) :
    ordI Q (J * J') = ordI Q J + ordI Q J' := by
  unfold ordI
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.2 hJ) (Associates.mk_ne_zero.2 hJ')
    (Associates.irreducible_mk.2 Q.irreducible)

theorem ordI_eq_zero_iff {J : Ideal S} (hJ : J ≠ ⊥) : ordI Q J = 0 ↔ ¬ J ≤ Q.asIdeal := by
  rw [← Ideal.dvd_iff_le, ← Associates.count_ne_zero_iff_dvd hJ Q.irreducible, not_not]
  rfl

theorem le_ordI_iff {J : Ideal S} (hJ : J ≠ ⊥) (n : ℕ) : n ≤ ordI Q J ↔ J ≤ Q.asIdeal ^ n := by
  unfold ordI
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hJ)
    (Associates.irreducible_mk.2 Q.irreducible), ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le]

theorem ordI_top : ordI Q ⊤ = 0 :=
  (ordI_eq_zero_iff Q top_ne_bot).2 fun h => Q.isPrime.ne_top (top_le_iff.1 h)

omit [IsDedekindDomain S] in
theorem span_ne_bot {x : S} (hx : x ≠ 0) : Ideal.span {x} ≠ ⊥ := by
  rwa [ne_eq, Ideal.span_singleton_eq_bot]

theorem le_ordI_span_iff {x : S} (hx : x ≠ 0) (n : ℕ) :
    n ≤ ordI Q (Ideal.span {x}) ↔ x ∈ Q.asIdeal ^ n := by
  rw [le_ordI_iff Q (span_ne_bot hx), Ideal.span_singleton_le_iff_mem]

theorem ordI_span_prod {ι : Type*} (s : Finset ι) (f : ι → S) (hf : ∀ i ∈ s, f i ≠ 0) :
    ordI Q (Ideal.span {∏ i ∈ s, f i}) = ∑ i ∈ s, ordI Q (Ideal.span {f i}) := by
  induction s using Finset.induction_on with
  | empty => simp [Ideal.span_singleton_one, ordI_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← Ideal.span_singleton_mul_span_singleton,
      ordI_mul Q (span_ne_bot (hf a (Finset.mem_insert_self a s)))
        (span_ne_bot (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem intValuation_eq_exp_ordI {x : S} (hx : x ≠ 0) :
    Q.intValuation x = exp (-(ordI Q (Ideal.span {x}) : ℤ)) :=
  Q.intValuation_if_neg hx

theorem ordI_span_eq_one {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (Ideal.span {ϖ}) = 1 := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have a := (le_ordI_span_iff Q hϖ 1).2 (by rwa [pow_one])
  have b := mt (le_ordI_span_iff Q hϖ 2).1 h2
  omega

theorem ordI_span_pow {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (n : ℕ) :
    ordI Q (Ideal.span {ϖ ^ n}) = n := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have := ordI_span_prod Q (Finset.range n) (fun _ => ϖ) (fun _ _ => hϖ)
  simpa [Finset.prod_const, ordI_span_eq_one Q h1 h2] using this

theorem exists_unif : ∃ ϖ : S, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  refine ⟨π, ?_, ?_⟩
  · rw [← pow_one Q.asIdeal, ← Q.intValuation_le_pow_iff_mem, hπ]; simp
  · rw [← Q.intValuation_le_pow_iff_mem, hπ, exp_le_exp]; norm_num

/-- One step of `Q`-adic approximation by multiples of `ϖ ^ n`. -/
theorem exists_sub_mul_pow_mem {ϖ : S} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) {x : S}
    {n : ℕ} (hx : x ∈ Q.asIdeal ^ n) : ∃ y : S, x - y * ϖ ^ n ∈ Q.asIdeal ^ (n + 1) := by
  have hϖ : ϖ ≠ 0 := by rintro rfl; exact h2 (Ideal.zero_mem _)
  have hv : Q.intValuation x ≤ Q.intValuation (ϖ ^ n) :=
    ((Q.intValuation_le_pow_iff_mem x n).2 hx).trans_eq
      (by rw [intValuation_eq_exp_ordI Q (pow_ne_zero n hϖ), ordI_span_pow Q h1 h2])
  obtain ⟨y, hy⟩ := Q.exists_intValuation_mul_sub_lt hv (Multiplicative.ofAdd (-((n + 1 : ℕ) : ℤ)))
  exact ⟨y, (Q.intValuation_le_pow_iff_mem _ _).1 hy.le⟩

end Ord

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_A_Gen =====
section

/-!
# S4-GOS-A, part 2: the conductor of `A[ϖ]` in a totally ramified extension

`S / A` is a finite torsion-free extension of Dedekind domains with Galois group `G` (`IsGaloisGroup G A S`) and
`Q` is a height-one prime of `S` with finite residue field whose inertia group is all of `G` (`hI`). Then `Q` is the
only prime of `S` over `q = Q ∩ A` (`eq_of_map_le`), so `Q ^ k ⊆ q S` for some `k`; every element of `S` is
`Q`-adically approximated by `A[ϖ]` for a uniformizer `ϖ` (`exists_adjoin_sub_mem`, residue field of `S` = that of
`A` by `Swan.exists_inertia_fixed_sub_mem`), and Nakayama over `q` gives `t ∈ A \ q` with `t S ⊆ A[ϖ]`, i.e. the
conductor of `A[ϖ]` is prime to `Q` (`exists_mem_conductor_not_mem`). No completion is used.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped Classical Pointwise

namespace RamanujanPetersson.GOS

section Tot

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G A S]
  (Q : HeightOneSpectrum S) (hI : ∀ σ : G, σ ∈ Q.asIdeal.inertia G)

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] in
include hI in
theorem exists_algebraMap_sub_mem [Finite (S ⧸ Q.asIdeal)] (y : S) :
    ∃ a : A, y - algebraMap A S a ∈ Q.asIdeal := by
  have := Q.isMaximal
  obtain ⟨b, hb, hyb⟩ := Swan.exists_inertia_fixed_sub_mem (R := A) (G := G) Q.asIdeal y
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b (fun σ => hb σ (hI σ))
  exact ⟨a, hyb⟩

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] in
include hI in
theorem exists_adjoin_sub_mem [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) (n : ℕ) (s : S) :
    ∃ m ∈ Algebra.adjoin A {ϖ}, s - m ∈ Q.asIdeal ^ n := by
  induction n with
  | zero => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, hsm⟩ := ih
    obtain ⟨y, hy⟩ := exists_sub_mul_pow_mem Q h1 h2 hsm
    obtain ⟨a, ha⟩ := exists_algebraMap_sub_mem (A := A) Q hI y
    have hϖm : ϖ ∈ Algebra.adjoin A {ϖ} := Algebra.self_mem_adjoin_singleton A ϖ
    refine ⟨m + algebraMap A S a * ϖ ^ n, Subalgebra.add_mem _ hm (Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ a) (Subalgebra.pow_mem _ hϖm n)), ?_⟩
    have e : s - (m + algebraMap A S a * ϖ ^ n) =
        (s - m - y * ϖ ^ n) + (y - algebraMap A S a) * ϖ ^ n := by ring
    rw [e]
    refine Ideal.add_mem _ hy ?_
    have := Ideal.mul_mem_mul ha (Ideal.pow_mem_pow h1 n)
    rwa [← pow_succ'] at this

omit [Module.IsTorsionFree A S] in
include hI in
/-- In the totally ramified case `Q` is the only prime of `S` over `Q ∩ A`. -/
theorem eq_of_map_le (P : Ideal S) [P.IsPrime]
    (hP : (Q.under A).asIdeal.map (algebraMap A S) ≤ P) : P = Q.asIdeal := by
  have hq := (Q.under A).isMaximal
  have hle : (Q.under A).asIdeal ≤ P.under A := Ideal.map_le_iff_le_comap.1 hP
  have heq : P.under A = (Q.under A).asIdeal :=
    (hq.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have : P.LiesOver (Q.under A).asIdeal := ⟨heq.symm⟩
  have : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under A).asIdeal Q.asIdeal P G
  rw [← hσ]
  exact MulAction.mem_stabilizer_iff.1 (Ideal.inertia_le_stabilizer Q.asIdeal (hI σ))

include hI in
theorem exists_pow_le_map : ∃ k : ℕ, Q.asIdeal ^ k ≤ (Q.under A).asIdeal.map (algebraMap A S) := by
  have := Q.isMaximal
  have hne : (Q.under A).asIdeal.map (algebraMap A S) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A S)).not.mpr
      (Q.under A).ne_bot
  obtain ⟨J, hQJ, heq⟩ := Ideal.eq_prime_pow_mul_coprime hne Q.asIdeal
  have hJ : J = ⊤ := by
    by_contra hJ
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
    have hMQ : M = Q.asIdeal := eq_of_map_le Q hI M (by rw [heq]; exact Ideal.mul_le_right.trans hJM)
    exact Q.isPrime.ne_top (top_le_iff.1 (hQJ ▸ sup_le le_rfl (hMQ ▸ hJM)))
  rw [hJ, Ideal.mul_top] at heq
  exact ⟨_, heq.symm.le⟩

include hI in
/-- The conductor of `A[ϖ]` in `S` is prime to `Q` (Nakayama over `Q ∩ A`). -/
theorem exists_mem_conductor_not_mem [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) : ∃ t ∈ conductor A ϖ, t ∉ Q.asIdeal := by
  obtain ⟨k, hk⟩ := exists_pow_le_map (A := A) Q hI
  let N : Submodule A S := Subalgebra.toSubmodule (Algebra.adjoin A {ϖ})
  have hfg : (⊤ : Submodule A (S ⧸ N)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule A (S ⧸ N)) ≤ (Q.under A).asIdeal • ⊤ := by
    rintro z -
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective N z
    obtain ⟨m, hm, hsm⟩ := exists_adjoin_sub_mem (A := A) Q hI h1 h2 k s
    have hw : s - m ∈ (Q.under A).asIdeal • (⊤ : Submodule A S) := by
      rw [Ideal.smul_top_eq_map]; exact hk hsm
    have e : (Submodule.Quotient.mk s : S ⧸ N) = N.mkQ (s - m) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq, sub_sub_cancel]
      exact hm
    rw [e]
    have := Submodule.mem_map_of_mem (f := N.mkQ) hw
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ ⊤ hfg hle
  refine ⟨algebraMap A S r, mem_conductor_iff.2 fun b => ?_, fun hr' => ?_⟩
  · have := hr (Submodule.Quotient.mk b) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def] at this
    exact this
  · have hr2 : r ∈ (Q.under A).asIdeal := hr'
    exact (Q.under A).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hr2 hr1))

end Tot

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_A_Min =====
section

/-!
# S4-GOS-A, part 3: the minimal polynomial of an element with trivial stabilizer

`S / A` is a finite torsion-free extension of Dedekind domains with Galois group `G`. If `σ ϖ = ϖ` only for
`σ = 1`, then `minpoly A ϖ` maps to `∏_σ (X - σ ϖ)` (`minpoly_map_eq_charpoly`), has degree `|G|`,
`f'(ϖ) = ∏_{σ ≠ 1} (ϖ - σ ϖ)` (`aeval_derivative_minpoly`), and `ϖ` generates `Frac S` over `Frac A`
(`adjoin_eq_top`), the hypothesis of Mathlib's `conductor_mul_differentIdeal`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField
open scoped Classical nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Min

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G A S]

omit [IsDedekindDomain A] [IsDedekindDomain S] [Module.Finite A S] [Module.IsTorsionFree A S]
  [Fintype G] in
theorem aeval_smul (σ : G) (f : A[X]) (x : S) : aeval (σ • x) f = σ • aeval x f := by
  have := IsGaloisGroup.commutes (G := G) (A := A) (B := S)
  have h := aeval_algHom_apply (MulSemiringAction.toAlgHom A S σ) x f
  simpa using h

variable {ϖ : S} (hst : ∀ σ : G, σ • ϖ = ϖ → σ = 1)

include hst in
/-- An element with trivial stabilizer has minimal polynomial `∏_σ (X - σ ϖ)`. -/
theorem minpoly_map_eq_charpoly :
    (minpoly A ϖ).map (algebraMap A S) = MulSemiringAction.charpoly G ϖ := by
  obtain ⟨p, hp, hdeg, hmon⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A S G ϖ) (MulSemiringAction.monic_charpoly G ϖ)
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  have hev : aeval ϖ p = 0 := by
    rw [aeval_def, ← eval_map, hp, MulSemiringAction.eval_charpoly]
  have hdvd : minpoly A ϖ ∣ p := minpoly.isIntegrallyClosed_dvd hint hev
  have hroot : ∀ σ : G, aeval (σ • ϖ) (minpoly A ϖ) = 0 := by
    intro σ; rw [aeval_smul, minpoly.aeval, smul_zero]
  have hinj : Function.Injective fun σ : G => σ • ϖ := by
    intro σ τ h
    have h' : (τ⁻¹ * σ) • ϖ = ϖ := by
      simp only at h
      rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.1 (hst _ h')).symm
  have hf0 : (minpoly A ϖ).map (algebraMap A S) ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hsub : (Finset.univ.image fun σ : G => σ • ϖ) ⊆
      ((minpoly A ϖ).map (algebraMap A S)).roots.toFinset := by
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, eval_map, ← aeval_def]
    exact hroot σ
  have hcard : Fintype.card G ≤ (minpoly A ϖ).natDegree := by
    calc Fintype.card G = (Finset.univ.image fun σ : G => σ • ϖ).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      _ ≤ ((minpoly A ϖ).map (algebraMap A S)).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card ((minpoly A ϖ).map (algebraMap A S)).roots := Multiset.toFinset_card_le _
      _ ≤ ((minpoly A ϖ).map (algebraMap A S)).natDegree := card_roots' _
      _ = (minpoly A ϖ).natDegree := (minpoly.monic hint).natDegree_map _
  have hdegp : p.natDegree = Fintype.card G := by
    rw [hdeg, MulSemiringAction.charpoly_eq, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
  have heq : p = minpoly A ϖ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd (hdegp ▸ hcard)
  rw [← heq, hp]

include hst in
theorem natDegree_minpoly : (minpoly A ϖ).natDegree = Fintype.card G := by
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  rw [← (minpoly.monic hint).natDegree_map (algebraMap A S), minpoly_map_eq_charpoly hst,
    MulSemiringAction.charpoly_eq, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]

include hst in
/-- Hilbert's formula for `f'(ϖ)`: `f'(ϖ) = ∏_{σ ≠ 1} (ϖ - σ ϖ)`. -/
theorem aeval_derivative_minpoly :
    aeval ϖ (derivative (minpoly A ϖ)) = ∏ σ ∈ Finset.univ.erase (1 : G), (ϖ - σ • ϖ) := by
  rw [aeval_def, ← eval_map, ← derivative_map, minpoly_map_eq_charpoly hst,
    MulSemiringAction.charpoly_eq, derivative_prod_finset, eval_finsetSum,
    Finset.sum_eq_single (1 : G)]
  · simp [eval_prod]
  · intro σ _ hσ
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := 1)
      (Finset.mem_erase.2 ⟨Ne.symm hσ, Finset.mem_univ _⟩) (by simp), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

include hst in
/-- `ϖ` generates the fraction field extension. -/
theorem adjoin_eq_top :
    Algebra.adjoin (FractionRing A) {algebraMap S (FractionRing S) ϖ} = ⊤ := by
  have hint : IsIntegral A ϖ := Algebra.IsIntegral.isIntegral ϖ
  set x := algebraMap S (FractionRing S) ϖ
  have hxA : IsIntegral A x := hint.map (IsScalarTower.toAlgHom A S (FractionRing S))
  have hxK : IsIntegral (FractionRing A) x := hxA.tower_top
  have hmin : minpoly (FractionRing A) x = (minpoly A ϖ).map (algebraMap A (FractionRing A)) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing A) hxA,
      minpoly.algebraMap_eq (IsFractionRing.injective S (FractionRing S))]
  have hdeg : Module.finrank (FractionRing A) (FractionRing A)⟮x⟯ = Fintype.card G := by
    rw [IntermediateField.adjoin.finrank hxK, hmin, (minpoly.monic hint).natDegree_map,
      natDegree_minpoly hst]
  have hfin : Module.finrank (FractionRing A) (FractionRing S) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank' G A S,
      IsFractionRing.finrank_eq A (FractionRing A) S (FractionRing S)]
  have : FiniteDimensional (FractionRing A) (FractionRing S) := .of_isLocalization A S A⁰
  have htop : (FractionRing A)⟮x⟯ = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hdeg, IntermediateField.finrank_top', hfin])
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic, htop,
    IntermediateField.top_toSubalgebra]

end Min

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_A_Tot =====
section

/-!
# S4-GOS-A, part 4: Hilbert's different formula in the totally ramified case

`S / A` finite torsion-free extension of Dedekind domains with Galois group `G`, `Q` a height-one prime of `S` with
finite residue field and inertia group all of `G`. For a uniformizer `ϖ` of `Q`, the conductor of `A[ϖ]` is prime
to `Q` (part 2), `ϖ` has trivial stabilizer and generates `Frac S` (part 3), so Mathlib's
`conductor_mul_differentIdeal` gives `v_Q(𝔇_{S/A}) = v_Q(f'(ϖ)) = ∑_{σ ≠ 1} v_Q(ϖ - σ ϖ)`
(`ordI_differentIdeal_of_totally`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain Polynomial
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Tot

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S] [IsGaloisGroup G A S]

variable (A S) in
theorem isSeparable_frac (H : Type*) [Group H] [Finite H] [MulSemiringAction H S]
    [IsGaloisGroup H A S] : Algebra.IsSeparable (FractionRing A) (FractionRing S) := by
  let := IsFractionRing.mulSemiringAction H S (FractionRing S)
  have := IsGaloisGroup.isGalois H (FractionRing A) (FractionRing S)
  infer_instance

omit [IsDedekindDomain A] [Module.Finite A S] [Module.IsTorsionFree A S] [Fintype G] in
/-- An element of `G` fixing `ϖ` fixes `A[ϖ]`, hence (through a nonzero conductor element) all of `S`. -/
theorem eq_one_of_smul_eq {ϖ t : S} (ht : t ∈ conductor A ϖ) (ht0 : t ≠ 0) (σ : G)
    (hσ : σ • ϖ = ϖ) : σ = 1 := by
  have := IsGaloisGroup.commutes (G := G) (A := A) (B := S)
  have hfix : ∀ y ∈ Algebra.adjoin A {ϖ}, σ • y = y := by
    intro y hy
    have hle : Algebra.adjoin A {ϖ} ≤
        AlgHom.equalizer (MulSemiringAction.toAlgHom A S σ) (AlgHom.id A S) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 (by simpa [AlgHom.mem_equalizer] using hσ))
    simpa [AlgHom.mem_equalizer] using hle hy
  have := IsGaloisGroup.faithful (G := G) (A := A) (B := S)
  apply eq_of_smul_eq_smul (α := S)
  intro b
  rw [one_smul]
  have h1 := hfix _ (mem_conductor_iff.1 ht b)
  have h2 := hfix _ (mem_conductor_iff.1 ht 1)
  rw [mul_one] at h2
  rw [smul_mul', h2] at h1
  exact mul_left_cancel₀ ht0 h1

variable (Q : HeightOneSpectrum S) (hI : ∀ σ : G, σ ∈ Q.asIdeal.inertia G)

include hI in
/-- **Hilbert's different formula, totally ramified case**: for a uniformizer `ϖ` of `Q`,
`v_Q(𝔇_{S/A}) = ∑_{σ ≠ 1} v_Q(ϖ - σ ϖ)`. -/
theorem ordI_differentIdeal_of_totally [Finite (S ⧸ Q.asIdeal)] {ϖ : S} (h1 : ϖ ∈ Q.asIdeal)
    (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    ordI Q (differentIdeal A S) =
      ∑ σ ∈ Finset.univ.erase (1 : G), ordI Q (Ideal.span {ϖ - σ • ϖ}) := by
  obtain ⟨t, ht, htQ⟩ := exists_mem_conductor_not_mem (A := A) Q hI h1 h2
  have ht0 : t ≠ 0 := fun h => htQ (h ▸ Q.asIdeal.zero_mem)
  have hst : ∀ σ : G, σ • ϖ = ϖ → σ = 1 := fun σ hσ => eq_one_of_smul_eq ht ht0 σ hσ
  have := isSeparable_frac A S G
  have : FiniteDimensional (FractionRing A) (FractionRing S) := .of_isLocalization A S A⁰
  have : IsIntegralClosure S A (FractionRing S) :=
    IsIntegralClosure.of_isIntegrallyClosed S A (FractionRing S)
  have hcd := conductor_mul_differentIdeal A (FractionRing A) (FractionRing S) ϖ (adjoin_eq_top hst)
  rw [aeval_derivative_minpoly hst] at hcd
  have hne : ∀ σ ∈ Finset.univ.erase (1 : G), ϖ - σ • ϖ ≠ 0 := by
    intro σ hσ h
    exact (Finset.mem_erase.1 hσ).1 (hst σ (sub_eq_zero.1 h).symm)
  have hc0 : conductor A ϖ ≠ ⊥ := fun h => ht0 (Ideal.mem_bot.1 (h ▸ ht))
  rw [← ordI_span_prod Q _ _ hne, ← hcd, ordI_mul Q hc0 (differentIdeal_ne_bot (A := A) (B := S)),
    (ordI_eq_zero_iff Q hc0).2 (fun h => htQ (h ht)), zero_add]

end Tot

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_A_Unr =====
section

/-!
# S4-GOS-A, part 5: the inertia ring is unramified

For `S / R` Dedekind with Galois group `G` and `Q` a height-one prime of `S` with finite residue field, the inertia
ring `S ^ (I_Q)` (`inertiaRing R G Q`) is Dedekind and finite over `R` (global instances `fixed_*`), the prime
`Q ∩ S^(I_Q)` has ramification index one over `R` (`ramificationIdx_inertiaRing`), so `Q` does not divide the
extended different of `S^(I_Q) / R` (`not_dvd_map_differentIdeal`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Classical Pointwise nonZeroDivisors

namespace RamanujanPetersson.GOS

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Instances

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G) [Module.Finite R S]

variable [IsDedekindDomain R] [IsDedekindDomain S]

instance fixed_finite_bot : Module.Finite R (FixedPoints.subalgebra R S H) :=
  have : IsNoetherian R (FixedPoints.subalgebra R S H) :=
    isNoetherian_of_injective (FixedPoints.subalgebra R S H).val.toLinearMap Subtype.val_injective
  Module.IsNoetherian.finite R _

end Instances

section Unr

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

variable (R G) in
/-- The inertia ring `S ^ (I_Q)`. -/
abbrev inertiaRing : Subalgebra R S := FixedPoints.subalgebra R S (Q.asIdeal.inertia G)

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [Module.IsTorsionFree R S] in
attribute [local instance] Ideal.Quotient.field in
theorem finite_residueField {T : Type*} [CommRing T] [Algebra T S] (p : Ideal T) [p.IsMaximal]
    [Q.asIdeal.LiesOver p] : Finite p.ResidueField := by
  have : Finite (T ⧸ p) :=
    Finite.of_injective (algebraMap (T ⧸ p) (S ⧸ Q.asIdeal)) (RingHom.injective _)
  exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2

end Unr

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Per =====
section

/-!
# S4-GOS-B, part Per: periodicity of Frobenius traces on finite modules, the shifted recurrence at position `0`,
and Cayley–Hamilton for twisted traces

* `exists_pow_eq_one`: an injective endomorphism of a finite module has a power equal to `1`;
* `periodic_mul`: `x (m + c T) = x m` for a `T`-periodic sequence;
* **`mul_zero_eq_of_periodic`**: if `μ` (first nonzero coefficient `μ e`) annihilates the integer sequence `s` at all
  positions `k ≥ 1` and `x` is periodic with `x m = s m` for `m ≥ 1`, then `μ e * x 0 = -Σ_{j > e} μ j s (j - e)`;
* **`trace_rec_of_charpoly`**: `Tr(A F^(k+D)) = Σ_{j<D} c_j Tr(A F^(k+j))` on a free module of rank `D`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace RamanujanPetersson.GOS

theorem exists_pow_eq_one {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [Finite V]
    (F : V →ₗ[R] V) (hF : Function.Injective F) : ∃ T, 0 < T ∧ F ^ T = 1 := by
  have : Finite (V →ₗ[R] V) := Finite.of_injective _ DFunLike.coe_injective
  have aux : ∀ a b : ℕ, a < b → F ^ a = F ^ b → ∃ T, 0 < T ∧ F ^ T = 1 := by
    intro a b hab he
    refine ⟨b - a, by omega, ?_⟩
    have hinj : Function.Injective (F ^ a) := by
      rw [Module.End.coe_pow]; exact hF.iterate a
    ext x
    apply hinj
    rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le, ← he, Module.End.one_apply]
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F ^ n)
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact aux a b h he
  · exact aux b a h he.symm

theorem periodic_mul {R : Type*} {x : ℕ → R} {T : ℕ} (hx : ∀ m, x (m + T) = x m) (m c : ℕ) :
    x (m + c * T) = x m := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.succ_mul, ← add_assoc, hx, ih]

theorem mul_zero_eq_of_periodic {R : Type*} [CommRing R] {D : ℕ} (μ : Fin (D + 1) → ℤ) (e : Fin (D + 1))
    (he : ∀ j : Fin (D + 1), j < e → μ j = 0) {s : ℕ → ℤ}
    (hμ : ∀ k, 1 ≤ k → ∑ j : Fin (D + 1), μ j * s (k + j) = 0) {x : ℕ → R} {T : ℕ} (hT : 0 < T)
    (hx : ∀ m, x (m + T) = x m) (hxs : ∀ m, 1 ≤ m → x m = s m) :
    (μ e : R) * x 0 = -∑ j : Fin (D + 1), if e < j then ((μ j * s (j - e) : ℤ) : R) else 0 := by
  set k := (e + 1) * T - e with hk
  have hk1 : 1 ≤ k := by
    have : (e : ℕ) + 1 ≤ (e + 1) * T := Nat.le_mul_of_pos_right _ hT
    omega
  have h1 := congrArg (fun z : ℤ => (z : R)) (hμ k hk1)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at h1
  have h2 : ∀ j : Fin (D + 1), (μ j : R) * (s (k + j) : R) =
      (if j = e then (μ e : R) * x 0 else 0) + if e < j then ((μ j * s (j - e) : ℤ) : R) else 0 := by
    intro j
    rcases lt_trichotomy j e with hj | hj | hj
    · rw [he j hj, if_neg hj.ne, if_neg (not_lt.2 hj.le)]; simp
    · rw [hj, if_pos rfl, if_neg (lt_irrefl _), add_zero]
      have : k + (e : ℕ) = 0 + (e + 1) * T := by omega
      rw [← hxs (k + e) (by omega), this, periodic_mul hx]
    · rw [if_neg hj.ne', if_pos hj, zero_add]
      have hje' : (e : ℕ) < j := hj
      have hje : 1 ≤ (j : ℕ) - e := by omega
      have : k + (j : ℕ) = ((j : ℕ) - e) + (e + 1) * T := by
        have : (e : ℕ) + 1 ≤ (e + 1) * T := Nat.le_mul_of_pos_right _ hT
        omega
      have hs : (s (k + j) : R) = (s (j - e) : R) := by
        rw [← hxs (k + j) (by omega), ← hxs _ hje, this, periodic_mul hx]
      rw [hs]
      push_cast
      rfl
  simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [← sub_eq_zero, sub_neg_eq_add]
  exact h1

theorem trace_rec_of_charpoly {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V] (A F : Module.End R V) :
    ∃ c : Fin (Module.finrank R V) → R, ∀ k : ℕ,
      LinearMap.trace R V (A * F ^ (k + Module.finrank R V)) =
        ∑ j : Fin (Module.finrank R V), c j * LinearMap.trace R V (A * F ^ (k + j)) := by
  set D := Module.finrank R V
  have hsum := (LinearMap.charpoly_monic F).as_sum
  rw [LinearMap.charpoly_natDegree] at hsum
  have h0 := LinearMap.aeval_self_charpoly F
  rw [hsum] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  refine ⟨fun j => -(LinearMap.charpoly F).coeff j, fun k => ?_⟩
  have hFD : F ^ D = -∑ i ∈ Finset.range D, algebraMap R (Module.End R V) ((LinearMap.charpoly F).coeff i) * F ^ i :=
    eq_neg_of_add_eq_zero_left h0
  rw [pow_add, ← mul_assoc, hFD, mul_neg, Finset.mul_sum, map_neg, map_sum, ← Finset.sum_neg_distrib,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, map_smul, smul_eq_mul, pow_add,
    ← mul_assoc]
  ring

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Seq =====
section

/-!
# S4-GOS-B, part Seq: the twisted Frobenius trace sequence of the perfect complex

`pcSeq Λ π Γ I ψ t h hI g m = Σ_{i<3} (-1)^i Tr(ρPC_i(g⁻¹) ∘ F_i^m)` (`F = frobPC`).

* `prodMap_pow'`; `pcSeq_eq_trace`: `pcSeq` is one trace on `PC₀ × (PC₁ × PC₂)`;
* **`pcSeq_rec`**: a monic linear recurrence of order `finrank (PC₀ × (PC₁ × PC₂))` (Cayley–Hamilton);
* **`pcSeq_periodic`**: `pcSeq` is periodic in `m` when `Λ` is finite and every `F_i` is injective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.GOS

theorem prodMap_pow' {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : Module.End R M) (g : Module.End R N) (m : ℕ) : (f.prodMap g) ^ m = (f ^ m).prodMap (g ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, LinearMap.prodMap_one]
  | succ m ih => rw [pow_succ, ih, LinearMap.prodMap_mul, ← pow_succ, ← pow_succ]

section PC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)

end PC

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Cnt =====
section

/-!
# S4-GOS-B, part Cnt: the twisted Frobenius traces of the perfect complex are `l`-independent point counts

* `exists_ptData_alg`: the point data of `exists_ptData` for `Ω = K̄`, `Fr = z ↦ z ^ (q ^ m)`, `ιS` the inclusion.
* **`ptSeq`**: `ptSeq g m = |C(g)| · #{u ∈ U(𝔽_{q^m}) : π(F_u) ~ g}` (an integer, `0` at `m = 0`), independent of `l`.
* **`pcSeq_eq_ptSeq`**: for `l ∤ q`, `n > 0`, `m > 0`: `pcSeq (ℤ/l^n) … g m = ptSeq g m`
  (`lefschetz_trace_inv_comp` + `lefschetz_count_main`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Representation Lefschetz

section Cnt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

theorem hQ_of {r : ℕ} (hr : 0 < r) (he : 0 < e) : 1 < p ^ (e * r) :=
  Nat.one_lt_pow (Nat.mul_pos he hr).ne' (Fact.out : p.Prime).one_lt

end Cnt

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Hank =====
section

/-!
# S4-GOS-B, part Hank: an integer sequence with monic recurrences of bounded order modulo every `l ^ n`
satisfies a nonzero integer linear recurrence

* `den_clear`: clearing one denominator;
* **`exists_rec_of_mod_pow`**: if for every `n` the sequence `s : ℕ → ℤ` satisfies, modulo `l ^ n`, a monic linear
  recurrence of order `D` (`s (k + D) = Σ_{j<D} c_j s (k + j)`), then some nonzero `μ : Fin (D+1) → ℤ` satisfies
  `Σ_j μ_j s (k + j) = 0` for all `k` (Hankel rank over `ℚ` + a left inverse with cleared denominators).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

theorem den_clear (q : ℚ) {d : ℕ} (hd : q.den ∣ d) :
    ((((d / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = (d : ℚ) * q := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left _ q.den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- The truncated Hankel matrix `(s (k + j))_{k < M, j ≤ D}` over `ℚ`. -/
def hankA (s : ℕ → ℤ) (D M : ℕ) : Matrix (Fin M) (Fin (D + 1)) ℚ := Matrix.of fun k j => (s (k + j) : ℚ)

theorem mem_ker_hankA {s : ℕ → ℤ} {D M : ℕ} (μ : Fin (D + 1) → ℚ) :
    μ ∈ LinearMap.ker (hankA s D M).mulVecLin ↔ ∀ k : Fin M, ∑ j : Fin (D + 1), (s (k + j) : ℚ) * μ j = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
  simp [hankA, Matrix.mulVec, dotProduct]

theorem ker_hankA_anti {s : ℕ → ℤ} {D M M' : ℕ} (h : M ≤ M') :
    LinearMap.ker (hankA s D M').mulVecLin ≤ LinearMap.ker (hankA s D M).mulVecLin := by
  intro μ hμ
  rw [mem_ker_hankA] at hμ ⊢
  exact fun k => hμ ⟨k, lt_of_lt_of_le k.2 h⟩

theorem exists_rec_of_mod_pow {s : ℕ → ℤ} {l D : ℕ} (hl : 2 ≤ l)
    (h : ∀ n : ℕ, ∃ c : Fin D → ZMod (l ^ n), ∀ k,
      (s (k + D) : ZMod (l ^ n)) = ∑ j : Fin D, c j * (s (k + j) : ZMod (l ^ n))) :
    ∃ μ : Fin (D + 1) → ℤ, μ ≠ 0 ∧ ∀ k, ∑ j : Fin (D + 1), μ j * s (k + j) = 0 := by
  classical
  set K : ℕ → Submodule ℚ (Fin (D + 1) → ℚ) := fun M => LinearMap.ker (hankA s D M).mulVecLin with hK
  have hQ : ∃ v, ∃ M, Module.finrank ℚ (K M) ≤ v := ⟨_, 0, le_rfl⟩
  obtain ⟨M0, hM0⟩ := Nat.find_spec hQ
  have hmin : ∀ M, Nat.find hQ ≤ Module.finrank ℚ (K M) := fun M => Nat.find_min' hQ ⟨M, le_rfl⟩
  have hstab : ∀ M, M0 ≤ M → K M = K M0 := fun M hM =>
    Submodule.eq_of_le_of_finrank_le (ker_hankA_anti hM) (le_trans hM0 (hmin M))
  have hall : ∀ μ ∈ K M0, ∀ k : ℕ, ∑ j : Fin (D + 1), (s (k + j) : ℚ) * μ j = 0 := by
    intro μ hμ k
    have h1 : μ ∈ K (max M0 (k + 1)) := by rw [hstab _ (le_max_left _ _)]; exact hμ
    exact (mem_ker_hankA μ).1 h1 ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)⟩
  by_cases hbot : K M0 = ⊥
  · exfalso
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (hankA s D M0).mulVecLin hbot
    set B : Fin (D + 1) → Fin M0 → ℚ := fun i k => g (Pi.single k 1) i with hB
    have hBA : ∀ i j : Fin (D + 1), ∑ k : Fin M0, (s (k + j) : ℚ) * B i k = if i = j then 1 else 0 := by
      intro i j
      have e1 := LinearMap.congr_fun hg (Pi.single j 1)
      rw [LinearMap.comp_apply, LinearMap.id_apply] at e1
      have e2 : (hankA s D M0).mulVecLin (Pi.single j 1) = ∑ k : Fin M0, (s (k + j) : ℚ) • Pi.single k 1 := by
        ext k'
        simp [hankA, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
      rw [e2, map_sum] at e1
      have e3 := congr_fun e1 i
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e3
      rw [e3, Pi.single_apply]
    set δ : ℕ := ∏ i, ∏ k, (B i k).den with hδ
    have hden : ∀ i k, (B i k).den ∣ δ := fun i k =>
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans (Finset.dvd_prod_of_mem (fun i => ∏ k, (B i k).den)
        (Finset.mem_univ i))
    have hδpos : 0 < δ := Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => (B i k).den_pos
    set B' : Fin (D + 1) → Fin M0 → ℤ := fun i k => ((δ / (B i k).den : ℕ) : ℤ) * (B i k).num with hB'
    have hBA' : ∀ i j : Fin (D + 1), ∑ k : Fin M0, s (k + j) * B' i k = if i = j then (δ : ℤ) else 0 := by
      intro i j
      have : ((∑ k : Fin M0, s (k + j) * B' i k : ℤ) : ℚ) = ((if i = j then (δ : ℤ) else 0 : ℤ) : ℚ) := by
        push_cast
        simp only [hB', den_clear _ (hden i _)]
        rw [show (∑ k : Fin M0, (s (k + j) : ℚ) * ((δ : ℚ) * B i k)) = (δ : ℚ) * ∑ k : Fin M0, (s (k + j) : ℚ) * B i k by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hBA]
        split_ifs <;> simp
      exact_mod_cast this
    obtain ⟨c, hc⟩ := h δ
    set v : Fin (D + 1) → ZMod (l ^ δ) := Fin.lastCases (-1) (fun j => c j) with hv
    have hAv : ∀ k : ℕ, ∑ j : Fin (D + 1), (s (k + j) : ZMod (l ^ δ)) * v j = 0 := by
      intro k
      rw [Fin.sum_univ_castSucc]
      simp only [hv, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
      rw [hc k, mul_neg_one, ← sub_eq_add_neg, sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have key : ((δ : ℤ) : ZMod (l ^ δ)) * v (Fin.last D) = 0 := by
      have : ∑ j : Fin (D + 1), ((∑ k : Fin M0, s (k + j) * B' (Fin.last D) k : ℤ) : ZMod (l ^ δ)) * v j = 0 := by
        push_cast
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [show (∑ x : Fin (D + 1), (s ((k : ℕ) + (x : ℕ)) : ZMod (l ^ δ)) * (B' (Fin.last D) k : ZMod (l ^ δ)) * v x)
            = (B' (Fin.last D) k : ZMod (l ^ δ)) * ∑ j : Fin (D + 1), (s ((k : ℕ) + (j : ℕ)) : ZMod (l ^ δ)) * v j by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hAv k, mul_zero]
      rw [Finset.sum_eq_single (Fin.last D)] at this
      · rw [hBA', if_pos rfl] at this; exact this
      · intro j _ hj; rw [hBA', if_neg (Ne.symm hj)]; simp
      · simp
    simp only [hv, Fin.lastCases_last, mul_neg_one, neg_eq_zero, Int.cast_natCast] at key
    rw [ZMod.natCast_eq_zero_iff] at key
    exact absurd (Nat.le_of_dvd hδpos key) (not_le.2 (Nat.lt_pow_self (by omega)))
  · obtain ⟨μ, hμ, hμ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    set δ : ℕ := ∏ j, (μ j).den with hδ
    have hden : ∀ j, (μ j).den ∣ δ := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hδpos : 0 < δ := Finset.prod_pos fun j _ => (μ j).den_pos
    refine ⟨fun j => ((δ / (μ j).den : ℕ) : ℤ) * (μ j).num, ?_, ?_⟩
    · intro h0
      apply hμ0
      funext j
      have h2 : (((δ / (μ j).den : ℕ) : ℤ) * (μ j).num : ℤ) = 0 := congr_fun h0 j
      have h3 : ((((δ / (μ j).den : ℕ) : ℤ) * (μ j).num : ℤ) : ℚ) = 0 := by rw [h2]; simp
      rw [den_clear _ (hden j)] at h3
      simpa [hδpos.ne'] using h3
    · intro k
      have : ((∑ j : Fin (D + 1), ((δ / (μ j).den : ℕ) : ℤ) * (μ j).num * s (k + j) : ℤ) : ℚ) = 0 := by
        have e : ∀ j : Fin (D + 1), ((((δ / (μ j).den : ℕ) : ℤ) * (μ j).num * s (k + j) : ℤ) : ℚ) =
            (δ : ℚ) * μ j * (s (k + j) : ℚ) := fun j => by rw [Int.cast_mul, den_clear _ (hden j)]
        rw [Int.cast_sum]
        simp only [e]
        rw [show (∑ j : Fin (D + 1), (δ : ℚ) * μ j * (s (k + j) : ℚ)) =
            (δ : ℚ) * ∑ j : Fin (D + 1), (s (k + j) : ℚ) * μ j by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hall μ hμ k, mul_zero]
      exact_mod_cast this

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Loc =====
section

/-!
# S4-GOS-B, part Loc: local trace bounds from the different (Riemann-Hurwitz input F2)

For a Dedekind extension `A → B` (`B` the integral closure of `A` in `L`, `L / K` finite separable):
* `mul_mem_of_val_le`, `val_le_of_mul_mem`: `x · I ⊆ B` iff `v_Q(x) ≤ exp (ord_Q I)` for all `Q`;
* `mem_dual_one_iff`, `mem_dual_one_of_val`, `val_le_of_mem_dual_one`: the trace dual of `B` is `𝔇⁻¹`
  in valuation form (`d_Q = ordI Q (differentIdeal A B)`);
* **`val_trace_le`** (F2): if `v_Q(y) ≤ exp (e_Q n + d_Q)` for every `Q` over `P`, then `v_P(Tr y) ≤ exp n`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace RamanujanPetersson.GOS

section ValCrit

variable {B : Type*} (L : Type*) [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L]
  [IsFractionRing B L]

theorem mul_mem_of_val_le {I : Ideal B} {x : L}
    (hx : ∀ Q : HeightOneSpectrum B, Q.valuation L x ≤ exp (ordI Q I : ℤ)) {δ : B} (hδ : δ ∈ I) :
    x * algebraMap B L δ ∈ (algebraMap B L).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro Q
  rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : Q.intValuation δ ≤ exp (-(ordI Q I : ℤ)) := by
    by_cases hI : I = ⊥
    · subst hI; rw [Ideal.mem_bot.1 hδ, map_zero]; exact zero_le
    · rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact (le_ordI_iff Q hI _).1 le_rfl hδ
  calc Q.valuation L x * Q.intValuation δ ≤ exp (ordI Q I : ℤ) * exp (-(ordI Q I : ℤ)) :=
        mul_le_mul' (hx Q) h1
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

theorem val_le_of_mul_mem {I : Ideal B} (hI : I ≠ ⊥) {x : L}
    (hx : ∀ δ ∈ I, x * algebraMap B L δ ∈ (algebraMap B L).range) (Q : HeightOneSpectrum B) :
    Q.valuation L x ≤ exp (ordI Q I : ℤ) := by
  obtain ⟨δ, hδI, hδ⟩ : ∃ δ ∈ I, δ ∉ Q.asIdeal ^ (ordI Q I + 1) := by
    by_contra h
    push Not at h
    have := (le_ordI_iff Q hI (ordI Q I + 1)).2 h
    omega
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hδ (Submodule.zero_mem _)
  have ho : ordI Q (Ideal.span {δ}) ≤ ordI Q I := by
    by_contra h
    push Not at h
    exact hδ ((le_ordI_span_iff Q hδ0 _).1 (Nat.succ_le_of_lt h))
  obtain ⟨b, hb⟩ := hx δ hδI
  have h1 : Q.valuation L x * Q.valuation L (algebraMap B L δ) ≤ 1 := by
    rw [← map_mul, ← hb, HeightOneSpectrum.valuation_of_algebraMap]; exact Q.intValuation_le_one b
  rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq_exp_ordI Q hδ0] at h1
  calc Q.valuation L x
      = Q.valuation L x * exp (-(ordI Q (Ideal.span {δ}) : ℤ)) * exp (ordI Q (Ideal.span {δ}) : ℤ) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ 1 * exp (ordI Q (Ideal.span {δ}) : ℤ) := mul_le_mul' h1 le_rfl
    _ ≤ exp (ordI Q I : ℤ) := by rw [one_mul]; exact exp_le_exp.2 (by exact_mod_cast ho)

end ValCrit

section Dual

variable (A K : Type*) {L : Type*} (B : Type*)
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable [Module.Finite A B] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

include K L in
theorem differentIdeal_ne_bot' : differentIdeal A B ≠ ⊥ := by
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal A K L B]
  simp

theorem mem_dual_one_iff {x : L} :
    x ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) ↔
      ∀ δ ∈ differentIdeal A B, x * algebraMap B L δ ∈ (algebraMap B L).range := by
  have hD : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact differentIdeal_ne_bot' (L := L) A K B
  rw [← inv_inv (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)), ← coeIdeal_differentIdeal A K L B,
    FractionalIdeal.mem_inv_iff hD]
  constructor
  · intro h δ hδ
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff B⁰).1 (h _ (FractionalIdeal.mem_coeIdeal_of_mem B⁰ hδ))
    exact ⟨b, hb⟩
  · intro h y hy
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal B⁰).1 hy
    obtain ⟨b, hb⟩ := h δ hδ
    exact (FractionalIdeal.mem_one_iff B⁰).2 ⟨b, hb⟩

variable {A K B}

theorem mem_dual_one_of_val {x : L}
    (hx : ∀ Q : HeightOneSpectrum B, Q.valuation L x ≤ exp (ordI Q (differentIdeal A B) : ℤ)) :
    x ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) :=
  (mem_dual_one_iff A K B).2 fun _ hδ => mul_mem_of_val_le L hx hδ

theorem trace_mem_of_mem_dual_one {x : L} (hx : x ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)) :
    Algebra.trace K L x ∈ (algebraMap A K).range := by
  have h1 : (1 : L) ∈ (1 : FractionalIdeal B⁰ L) := (FractionalIdeal.mem_one_iff B⁰).2 ⟨1, map_one _⟩
  have := (FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0)).1 hx 1 h1
  simpa [Algebra.traceForm_apply] using this

end Dual

section Trace

variable {A K : Type*} {L : Type*} {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable [Module.Finite A B] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- **F2.** If `v_Q(y) ≤ exp (e_Q n + d_Q)` for every `Q` over `P`, then `v_P(Tr y) ≤ exp n`. -/
theorem val_trace_le (P : HeightOneSpectrum A) (n : ℤ) {y : L}
    (hy : ∀ Q : HeightOneSpectrum B, Q.asIdeal.LiesOver P.asIdeal →
      Q.valuation L y ≤ exp ((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n + ordI Q (differentIdeal A B))) :
    P.valuation K (Algebra.trace K L y) ≤ exp n := by
  classical
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  have := P.isMaximal
  obtain ⟨ϖ, hϖ⟩ := P.valuation_exists_uniformizer K
  set t : K := ϖ ^ n with ht_def
  have ht : P.valuation K t = exp (-n) := by
    rw [ht_def, map_zpow₀, hϖ, ← exp_zsmul, smul_neg, smul_eq_mul, mul_one]
  set y' : L := algebraMap K L t * y with hy'_def
  haveI := IsIntegralClosure.isLocalization A K L B
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B A⁰) y'
  obtain ⟨a, ha, has⟩ := Submonoid.mem_map.1 s.2
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hsa : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hPJ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hsa P.asIdeal
  set k := Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))
  have hJ0 : J ≠ ⊥ := by
    rintro rfl; rw [Ideal.mul_bot] at hspan; exact hsa hspan
  obtain ⟨s0, hs0J, hs0P⟩ : ∃ s0 ∈ J, s0 ∉ P.asIdeal := by
    by_contra h
    push Not at h
    have h2 : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl h
    rw [hPJ] at h2
    exact P.isPrime.ne_top (top_le_iff.1 h2)
  have hs00 : s0 ≠ 0 := by rintro rfl; exact hs0P (Submodule.zero_mem _)
  have hvs0 : P.valuation K (algebraMap A K s0) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (P.intValuation_le_one s0)
      (not_lt.1 (mt (HeightOneSpectrum.intValuation_lt_one_iff_mem P s0).1 hs0P))
  set c : K := algebraMap A K s0 * t with hc_def
  have hcv : P.valuation K c = exp (-n) := by rw [hc_def, map_mul, hvs0, ht, one_mul]
  have hxy : algebraMap K L c * y = algebraMap K L (algebraMap A K s0) * y' := by
    rw [hc_def, hy'_def, map_mul, mul_assoc]
  have hx : algebraMap K L c * y ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
    apply mem_dual_one_of_val
    intro Q
    by_cases hQ : Q.asIdeal.LiesOver P.asIdeal
    · have := hQ
      have hc : Q.valuation L (algebraMap K L c) =
          exp (-((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n)) := by
        rw [← HeightOneSpectrum.valuation_liesOver L P Q, hcv, ← exp_nsmul, nsmul_eq_mul, mul_neg]
      rw [map_mul, hc]
      calc exp (-((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n)) * Q.valuation L y
          ≤ exp (-((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n)) *
            exp ((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n + ordI Q (differentIdeal A B)) :=
            mul_le_mul' le_rfl (hy Q hQ)
        _ = exp (ordI Q (differentIdeal A B) : ℤ) := by rw [← exp_add]; congr 1; ring
    · set P' : HeightOneSpectrum A := Q.under A
      have hQP' : Q.asIdeal.LiesOver P'.asIdeal := ⟨rfl⟩
      have hne : ¬ P.asIdeal ^ k ≤ P'.asIdeal := by
        intro h
        have h1 : P.asIdeal ≤ P'.asIdeal := P'.isPrime.le_of_pow_le h
        exact hQ ⟨(P.isMaximal.eq_of_le P'.isPrime.ne_top h1).trans rfl⟩
      have hord : ordI P' J ≤ ordI P' (Ideal.span {s0}) :=
        (le_ordI_iff P' (by rwa [Ne, Ideal.span_singleton_eq_bot]) _).2
          (((Ideal.span_singleton_le_iff_mem _).2 hs0J).trans ((le_ordI_iff P' hJ0 _).1 le_rfl))
      have hordA : ordI P' (Ideal.span {a}) = ordI P' J := by
        rw [hspan, ordI_mul P' (pow_ne_zero _ P.ne_bot) hJ0, (ordI_eq_zero_iff P' (pow_ne_zero _ P.ne_bot)).2 hne,
          zero_add]
      have hle : P'.valuation K (algebraMap A K s0) ≤ P'.valuation K (algebraMap A K a) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
          intValuation_eq_exp_ordI P' hs00, intValuation_eq_exp_ordI P' ha0, hordA]
        exact exp_le_exp.2 (neg_le_neg (by exact_mod_cast hord))
      have hle' : Q.valuation L (algebraMap K L (algebraMap A K s0)) ≤
          Q.valuation L (algebraMap K L (algebraMap A K a)) := by
        rw [← HeightOneSpectrum.valuation_liesOver L P' Q, ← HeightOneSpectrum.valuation_liesOver L P' Q]
        exact pow_le_pow_left' hle _
      have hab : algebraMap K L (algebraMap A K a) * y' = algebraMap B L b := by
        rw [← hbs, ← has, mul_comm, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      rw [hxy, map_mul]
      calc Q.valuation L (algebraMap K L (algebraMap A K s0)) * Q.valuation L y'
          ≤ Q.valuation L (algebraMap K L (algebraMap A K a)) * Q.valuation L y' := mul_le_mul' hle' le_rfl
        _ = Q.valuation L (algebraMap B L b) := by rw [← map_mul, hab]
        _ ≤ 1 := by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact Q.intValuation_le_one b
        _ ≤ exp (ordI Q (differentIdeal A B) : ℤ) := by
          rw [← exp_zero]; exact exp_le_exp.2 (by positivity)
  obtain ⟨r, hr⟩ := trace_mem_of_mem_dual_one hx
  have hTr : Algebra.trace K L (algebraMap K L c * y) = c * Algebra.trace K L y := by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have h1 : P.valuation K (c * Algebra.trace K L y) ≤ 1 := by
    rw [← hTr, ← hr, HeightOneSpectrum.valuation_of_algebraMap]; exact P.intValuation_le_one r
  rw [map_mul, hcv] at h1
  calc P.valuation K (Algebra.trace K L y)
      = exp n * (exp (-n) * P.valuation K (Algebra.trace K L y)) := by
        rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    _ ≤ exp n * 1 := mul_le_mul' le_rfl h1
    _ = exp n := mul_one _

end Trace

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Loc2 =====
section

/-!
# S4-GOS-B, part Loc2: sharpness of the trace bound (F4) and residue approximation (R)

Same setting as `Def_RP_GOS_B_Loc` (`A → B` Dedekind, `B` integral closure of `A` in `L`, `L / K` separable).
* `exists_mul_mem_not_mem`: for `v_P(x) ≤ 1` there is `s ∈ A \ P` with `s x ∈ A`;
* `exists_sub_mul_val_le` (R): if `v_P(z) ≤ exp (n+1) = v_P(w)` then `v_P(z - c w) ≤ exp n` for some `c ∈ A`;
* **`exists_val_trace_eq`** (F4): for `Q0` over `P` there is `y` with `v_Q(y) ≤ exp (e_Q n + d_Q)` over `P`
  (one more at `Q0`) and `v_P(Tr y) = exp (n + 1)`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace RamanujanPetersson.GOS

section Resid

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

theorem exists_mul_mem_not_mem (P : HeightOneSpectrum A) {x : K} (hx : P.valuation K x ≤ 1) :
    ∃ s : A, s ∉ P.asIdeal ∧ algebraMap A K s * x ∈ (algebraMap A K).range := by
  classical
  have := P.isMaximal
  obtain ⟨a1, a2, ha2, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have ha20 : a2 ≠ 0 := nonZeroDivisors.ne_zero ha2
  have hsa : Ideal.span {a2} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hPJ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hsa P.asIdeal
  set k := Multiset.count P.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a2}))
  have hJ0 : J ≠ ⊥ := by
    rintro rfl; rw [Ideal.mul_bot] at hspan; exact hsa hspan
  obtain ⟨s0, hs0J, hs0P⟩ : ∃ s0 ∈ J, s0 ∉ P.asIdeal := by
    by_contra h
    push Not at h
    have h2 : P.asIdeal ⊔ J ≤ P.asIdeal := sup_le le_rfl h
    rw [hPJ] at h2
    exact P.isPrime.ne_top (top_le_iff.1 h2)
  have hs00 : s0 ≠ 0 := by rintro rfl; exact hs0P (Submodule.zero_mem _)
  have ha2K : algebraMap A K a2 ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]
  refine ⟨s0, hs0P, HeightOneSpectrum.mem_integers_of_valuation_le_one _ _ fun P' => ?_⟩
  by_cases hP : P' = P
  · subst hP
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
    exact mul_le_one' (P'.intValuation_le_one s0) hx
  · have hne : ¬ P.asIdeal ^ k ≤ P'.asIdeal := by
      intro h
      have h1 : P.asIdeal ≤ P'.asIdeal := P'.isPrime.le_of_pow_le h
      exact hP (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top h1).symm)
    have hord : ordI P' J ≤ ordI P' (Ideal.span {s0}) :=
      (le_ordI_iff P' (by rwa [Ne, Ideal.span_singleton_eq_bot]) _).2
        (((Ideal.span_singleton_le_iff_mem _).2 hs0J).trans ((le_ordI_iff P' hJ0 _).1 le_rfl))
    have hordA : ordI P' (Ideal.span {a2}) = ordI P' J := by
      rw [hspan, ordI_mul P' (pow_ne_zero _ P.ne_bot) hJ0,
        (ordI_eq_zero_iff P' (pow_ne_zero _ P.ne_bot)).2 hne, zero_add]
    have hle : P'.valuation K (algebraMap A K s0) ≤ P'.valuation K (algebraMap A K a2) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        intValuation_eq_exp_ordI P' hs00, intValuation_eq_exp_ordI P' ha20, hordA]
      exact exp_le_exp.2 (neg_le_neg (by exact_mod_cast hord))
    have hv2 : P'.valuation K (algebraMap A K a2) ≠ 0 := by rwa [Ne, map_eq_zero]
    rw [map_mul, map_div₀]
    calc P'.valuation K (algebraMap A K s0) *
          (P'.valuation K (algebraMap A K a1) / P'.valuation K (algebraMap A K a2))
        ≤ P'.valuation K (algebraMap A K a2) *
          (P'.valuation K (algebraMap A K a1) / P'.valuation K (algebraMap A K a2)) :=
          mul_le_mul' hle le_rfl
      _ = P'.valuation K (algebraMap A K a1) := mul_div_cancel₀ _ hv2
      _ ≤ 1 := by rw [HeightOneSpectrum.valuation_of_algebraMap]; exact P'.intValuation_le_one a1

/-- **R.** Residue approximation. -/
theorem exists_sub_mul_val_le (P : HeightOneSpectrum A) {z w : K} (n : ℤ)
    (hz : P.valuation K z ≤ exp (n + 1)) (hw : P.valuation K w = exp (n + 1)) :
    ∃ c : A, P.valuation K (z - algebraMap A K c * w) ≤ exp n := by
  have hw0 : w ≠ 0 := by rintro rfl; rw [map_zero] at hw; exact exp_ne_zero hw.symm
  have hx : P.valuation K (z / w) ≤ 1 := by
    rw [map_div₀, hw]
    calc P.valuation K z / exp (n + 1) ≤ exp (n + 1) / exp (n + 1) := by
          gcongr; exact zero_le
      _ = 1 := div_self (exp_ne_zero)
  obtain ⟨s, hsP, c', hc'⟩ := exists_mul_mem_not_mem P hx
  obtain ⟨s', i, hi, hsi⟩ := P.isMaximal.exists_inv hsP
  refine ⟨c' * s', ?_⟩
  have hsK : algebraMap A K s ≠ 0 := by
    intro h; rw [map_eq_zero_iff _ (IsFractionRing.injective A K)] at h; exact hsP (h ▸ Submodule.zero_mem _)
  have heq : z - algebraMap A K (c' * s') * w = (z / w) * algebraMap A K i * w := by
    have h1 : algebraMap A K i = 1 - algebraMap A K s' * algebraMap A K s := by
      rw [← map_mul, ← map_one (algebraMap A K), ← map_sub]; congr 1; rw [← hsi]; ring
    rw [h1, map_mul, hc']
    field_simp
  rw [heq, map_mul, map_mul, hw, HeightOneSpectrum.valuation_of_algebraMap]
  have hi1 : P.intValuation i ≤ exp (-1) := by
    have := (HeightOneSpectrum.intValuation_le_pow_iff_mem P i 1).2 (by rwa [pow_one])
    simpa using this
  calc P.valuation K (z / w) * P.intValuation i * exp (n + 1) ≤ 1 * exp (-1) * exp (n + 1) := by
        gcongr
    _ = exp n := by rw [one_mul, ← exp_add]; congr 1; ring

end Resid

section OrdLemmas

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

theorem ordI_self (Q : HeightOneSpectrum S) : ordI Q Q.asIdeal = 1 := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have h2 : Q.asIdeal ≤ Q.asIdeal ^ 2 := (le_ordI_iff Q Q.ne_bot 2).1 h
    have h3 : Q.asIdeal ^ 2 < Q.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti Q.asIdeal Q.ne_bot Q.isPrime.ne_top (by norm_num)
    rw [pow_one] at h3
    exact absurd h2 (not_le_of_gt h3)
  · exact (le_ordI_iff Q Q.ne_bot 1).2 (by rw [pow_one])

theorem ordI_of_ne {Q Q' : HeightOneSpectrum S} (h : Q' ≠ Q) : ordI Q Q'.asIdeal = 0 := by
  rw [ordI_eq_zero_iff Q Q'.ne_bot]
  intro hle
  exact h (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top hle))

theorem ordI_mul_asIdeal_self (Q : HeightOneSpectrum S) {J : Ideal S} (hJ : J ≠ ⊥) :
    ordI Q (J * Q.asIdeal) = ordI Q J + 1 := by
  rw [ordI_mul Q hJ Q.ne_bot, ordI_self]

theorem ordI_mul_asIdeal_of_ne {Q Q' : HeightOneSpectrum S} {J : Ideal S} (hJ : J ≠ ⊥) (h : Q' ≠ Q) :
    ordI Q (J * Q'.asIdeal) = ordI Q J := by
  rw [ordI_mul Q hJ Q'.ne_bot, ordI_of_ne h, add_zero]

end OrdLemmas

section ValOne

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- If `w ∉ A` but `w P ⊆ A`, then `v_P(w) = exp 1`. -/
theorem val_eq_exp_one_of_mul_mem (P : HeightOneSpectrum A) {w : K}
    (hw : ∀ p ∈ P.asIdeal, w * algebraMap A K p ∈ (algebraMap A K).range)
    (hw' : w ∉ (algebraMap A K).range) : P.valuation K w = exp 1 := by
  have hv := val_le_of_mul_mem K P.ne_bot hw
  have hgt : 1 < P.valuation K w := by
    by_contra h
    push Not at h
    apply hw'
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro P'
    by_cases hP : P' = P
    · subst hP; exact h
    · have := hv P'
      rwa [ordI_of_ne (Ne.symm hP), Nat.cast_zero, exp_zero] at this
  have h1 : P.valuation K w ≤ exp 1 := by
    have := hv P
    rwa [ordI_self, Nat.cast_one] at this
  have hw0 : P.valuation K w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  rw [← exp_log hw0] at hgt h1 ⊢
  rw [← exp_zero, exp_lt_exp] at hgt
  rw [exp_le_exp] at h1
  congr 1
  omega

end ValOne

section Sharp

variable {A K : Type*} {L : Type*} {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
variable [Module.Finite A B] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- An element of `(𝔇 Q0)⁻¹` whose trace is not integral. -/
theorem exists_trace_not_mem (Q0 : HeightOneSpectrum B) :
    ∃ x : L, (∀ δ ∈ differentIdeal A B * Q0.asIdeal, x * algebraMap B L δ ∈ (algebraMap B L).range) ∧
      Algebra.trace K L x ∉ (algebraMap A K).range := by
  classical
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot' (L := L) A K B
  have hI : differentIdeal A B * Q0.asIdeal ≠ ⊥ := mul_ne_zero hD Q0.ne_bot
  have hDf : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hD
  have hIf : ((differentIdeal A B * Q0.asIdeal : Ideal B) : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hI
  have hIle : ((differentIdeal A B * Q0.asIdeal : Ideal B) : FractionalIdeal B⁰ L) ≤
      ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal L).2 Ideal.mul_le_left
  have hle := FractionalIdeal.inv_anti_mono hIf hDf hIle
  have hne : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)⁻¹ ≠
      ((differentIdeal A B * Q0.asIdeal : Ideal B) : FractionalIdeal B⁰ L)⁻¹ := by
    intro h
    rw [inv_inj, FractionalIdeal.coeIdeal_inj] at h
    have h2 := congrArg (ordI Q0) h
    rw [ordI_mul_asIdeal_self Q0 hD] at h2
    omega
  obtain ⟨x, hxI, hxD⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have hdual : ((differentIdeal A B : Ideal B) : FractionalIdeal B⁰ L)⁻¹ =
      FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
    rw [coeIdeal_differentIdeal A K L B, inv_inv]
  rw [hdual, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0)] at hxD
  push Not at hxD
  obtain ⟨a, ha, hTr⟩ := hxD
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff B⁰).1 ha
  refine ⟨x * algebraMap B L b, fun δ hδ => ?_, by simpa [Algebra.traceForm_apply] using hTr⟩
  have h1 := (FractionalIdeal.mem_inv_iff hIf).1 hxI (algebraMap B L (b * δ))
    (FractionalIdeal.mem_coeIdeal_of_mem B⁰ (Ideal.mul_mem_left _ b hδ))
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff B⁰).1 h1
  exact ⟨c, by rw [hc, map_mul, mul_assoc]⟩

/-- **F4.** Sharpness of the trace bound: for `Q0` over `P` there is `y` with
`v_Q(y) ≤ exp (e_Q n + ord_Q (𝔇 Q0))` for every `Q` over `P` and `v_P(Tr y) = exp (n + 1)`. -/
theorem exists_val_trace_eq (P : HeightOneSpectrum A) (Q0 : HeightOneSpectrum B)
    (hQ0 : Q0.asIdeal.LiesOver P.asIdeal) (n : ℤ) :
    ∃ y : L, (∀ Q : HeightOneSpectrum B, Q.asIdeal.LiesOver P.asIdeal →
      Q.valuation L y ≤ exp ((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n +
        ordI Q (differentIdeal A B * Q0.asIdeal))) ∧
      P.valuation K (Algebra.trace K L y) = exp (n + 1) := by
  classical
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot' (L := L) A K B
  have hI : differentIdeal A B * Q0.asIdeal ≠ ⊥ := mul_ne_zero hD Q0.ne_bot
  obtain ⟨x, hx, hTr⟩ := exists_trace_not_mem (A := A) (K := K) (L := L) (B := B) Q0
  have hPw : ∀ p ∈ P.asIdeal, Algebra.trace K L x * algebraMap A K p ∈ (algebraMap A K).range := by
    intro p hp
    have := hQ0
    have hp' : algebraMap A B p ∈ Q0.asIdeal := (Ideal.mem_of_liesOver Q0.asIdeal P.asIdeal p).1 hp
    have hmem : algebraMap A L p * x ∈ FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
      rw [mem_dual_one_iff A K B]
      intro δ hδ
      have h3 := hx (δ * algebraMap A B p) (Ideal.mul_mem_mul hδ hp')
      convert h3 using 1
      rw [map_mul, ← IsScalarTower.algebraMap_apply A B L]
      ring
    obtain ⟨r, hr⟩ := trace_mem_of_mem_dual_one hmem
    refine ⟨r, ?_⟩
    rw [hr, IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
      mul_comm]
  have hw1 := val_eq_exp_one_of_mul_mem P hPw hTr
  obtain ⟨ϖ, hϖ⟩ := P.valuation_exists_uniformizer K
  set t : K := ϖ ^ (-n) with ht_def
  have ht : P.valuation K t = exp n := by
    rw [ht_def, map_zpow₀, hϖ, ← exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg]
  refine ⟨algebraMap K L t * x, fun Q hQ => ?_, ?_⟩
  · have := hQ
    have hc : Q.valuation L (algebraMap K L t) =
        exp ((P.asIdeal.ramificationIdx' Q.asIdeal : ℤ) * n) := by
      rw [← HeightOneSpectrum.valuation_liesOver L P Q, ht, ← exp_nsmul, nsmul_eq_mul]
    rw [map_mul, hc, exp_add]
    exact mul_le_mul' le_rfl (val_le_of_mul_mem L hI hx Q)
  · rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, map_mul, ht, hw1, ← exp_add]

end Sharp

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Chart =====
section

/-!
# S4-GOS-B, part Chart: chart-level inputs for `Cotrace` (approximation, fibres, valuations)

* `exists_approx` (B Dedekind, fraction field `L`): for finitely many `Q`, `α : HOS B → L`, `E`,
  there is `y` with `v_Q(α Q - y) ≤ exp (E Q)` for `Q ∈ s`;
* for `A → B` as in `Def_RP_GOS_B_Loc`: `algebraMap_injective'`, `exists_under_eq` (going up),
  `finite_under_eq` (finite fibres), `liesOver_iff_under_eq`, `valuation_algebraMap_under`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace RamanujanPetersson.GOS

section Approx

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L] [IsFractionRing B L]

/-- Approximation at finitely many places of a Dedekind domain. -/
theorem exists_approx (s : Finset (HeightOneSpectrum B)) (α : HeightOneSpectrum B → L)
    (E : HeightOneSpectrum B → ℤ) : ∃ y : L, ∀ Q ∈ s, Q.valuation L (α Q - y) ≤ exp (E Q) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples B⁰ s α
  choose! a ha using hb
  have hb0 : (b : B) ≠ 0 := nonZeroDivisors.ne_zero b.2
  set n : HeightOneSpectrum B → ℕ := fun Q => ((ordI Q (Ideal.span {(b : B)}) : ℤ) - E Q).toNat with hn
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun Q => Q.asIdeal) n
    (fun Q _ => Q.prime) (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h')) (fun Q => a Q)
  have hbL : algebraMap B L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).2 hb0
  refine ⟨algebraMap B L β / algebraMap B L b, fun Q hQ => ?_⟩
  have hαQ : α Q = algebraMap B L (a Q) / algebraMap B L b := by
    rw [ha Q hQ, Algebra.smul_def, mul_div_cancel_left₀ _ hbL]
  rw [hαQ, ← sub_div, ← map_sub, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq_exp_ordI Q hb0]
  have h1 : Q.intValuation (a Q - β) ≤ exp (-(n Q : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
    have := hβ Q hQ
    rw [← neg_sub]
    exact (Ideal.neg_mem_iff _).2 this
  calc Q.intValuation (a Q - β) / exp (-(ordI Q (Ideal.span {(b : B)}) : ℤ))
      ≤ exp (-(n Q : ℤ)) / exp (-(ordI Q (Ideal.span {(b : B)}) : ℤ)) := by
        gcongr; exact zero_le
    _ = exp ((ordI Q (Ideal.span {(b : B)}) : ℤ) - n Q) := by rw [← exp_sub]; congr 1; ring
    _ ≤ exp (E Q) := exp_le_exp.2 (by
        have := Int.self_le_toNat ((ordI Q (Ideal.span {(b : B)}) : ℤ) - E Q)
        simp only [hn] at this ⊢
        omega)

end Approx

section Fibre

variable (A : Type*) {K L : Type*} {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

omit [IsDedekindDomain A] [IsDedekindDomain B] [IsFractionRing B L] in
include K L in
theorem algebraMap_injective' : Function.Injective (algebraMap A B) := by
  intro x y h
  have h2 : algebraMap A L x = algebraMap A L y := by
    rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h2
  exact IsFractionRing.injective A K ((algebraMap K L).injective h2)

variable [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

omit [Module.IsTorsionFree A B] in
theorem liesOver_iff_under_eq (P : HeightOneSpectrum A) (Q : HeightOneSpectrum B) :
    Q.asIdeal.LiesOver P.asIdeal ↔ Q.under A = P := by
  constructor
  · intro h; exact HeightOneSpectrum.ext h.over.symm
  · rintro rfl; exact ⟨rfl⟩

omit [IsFractionRing B L] [Module.IsTorsionFree A B] in
include K L in
theorem exists_under_eq (P : HeightOneSpectrum A) : ∃ Q : HeightOneSpectrum B, Q.under A = P := by
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 (algebraMap_injective' A (K := K) (L := L))
  have := P.isMaximal
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := B) P.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply P.ne_bot
    rw [hQ.over]
    exact Ideal.comap_bot_of_injective _ (algebraMap_injective' A (K := K) (L := L))
  exact ⟨⟨Q, hQm.isPrime, hQ0⟩, (liesOver_iff_under_eq A P _).1 hQ⟩

theorem finite_under_eq (P : HeightOneSpectrum A) : {Q : HeightOneSpectrum B | Q.under A = P}.Finite := by
  have := P.isMaximal
  apply ((IsDedekindDomain.primesOver_finite P.asIdeal B).preimage
    (f := fun Q : HeightOneSpectrum B => Q.asIdeal)
    (fun Q _ Q' _ h => HeightOneSpectrum.ext h)).subset
  intro Q hQ
  exact ⟨Q.isPrime, (liesOver_iff_under_eq A P Q).2 hQ⟩

theorem valuation_algebraMap_under (Q : HeightOneSpectrum B) (c : K) :
    Q.valuation L (algebraMap K L c) =
      (Q.under A).valuation K c ^ (Q.under A).asIdeal.ramificationIdx' Q.asIdeal := by
  have : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩
  exact (HeightOneSpectrum.valuation_liesOver L (Q.under A) Q c).symm

end Fibre

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Inst =====
section

/-!
# S4-GOS-B, part Inst: the cotrace data of a two-chart extension

`ordDiv J`: the divisor `Q ↦ ord_Q J` of an ideal (`0` for `J = ⊥`).
`Cotrace.ofCharts`: for `Data` on `HOS A1 ⊕ HOS A2` (field `K`) and `HOS B1 ⊕ HOS B2` (field `L`) whose
valuations are the adic ones, and Dedekind charts `A_i → B_i` as in `Def_RP_GOS_B_Loc`, the `Cotrace` with
`pr = under`, `e = ramificationIdx'`, `d = ord (differentIdeal A_i B_i)`, `tr = Algebra.trace K L`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace RamanujanPetersson.GOS

section OrdDiv

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

theorem finite_ordI_ne_zero {J : Ideal S} (hJ : J ≠ ⊥) :
    {Q : HeightOneSpectrum S | ordI Q J ≠ 0}.Finite := by
  apply (Ideal.finite_factors hJ).subset
  intro Q hQ
  have h : J ≤ Q.asIdeal := by
    by_contra h'
    exact hQ ((ordI_eq_zero_iff Q hJ).2 h')
  exact Ideal.dvd_iff_le.2 h

open Classical in
/-- The divisor `Q ↦ ord_Q J` of an ideal (`0` for `J = ⊥`). -/
def ordDiv (J : Ideal S) : HeightOneSpectrum S →₀ ℤ :=
  if hJ : J = ⊥ then 0 else
    Finsupp.ofSupportFinite (fun Q => (ordI Q J : ℤ)) ((finite_ordI_ne_zero hJ).subset fun Q hQ => by
      simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hQ
      exact hQ)

theorem ordDiv_apply {J : Ideal S} (hJ : J ≠ ⊥) (Q : HeightOneSpectrum S) : ordDiv J Q = ordI Q J := by
  classical
  rw [ordDiv, dif_neg hJ]
  rfl

theorem ordDiv_nonneg (J : Ideal S) : 0 ≤ ordDiv J := by
  classical
  intro Q
  by_cases hJ : J = ⊥
  · subst hJ; simp [ordDiv]
  · rw [ordDiv_apply hJ]; exact Int.natCast_nonneg _

end OrdDiv

section Builder

variable {Fq K L : Type*} [Field Fq] [Field K] [Field L] [Algebra Fq K] [Algebra Fq L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {A1 B1 A2 B2 : Type*}
  [CommRing A1] [IsDedekindDomain A1] [CommRing B1] [IsDedekindDomain B1] [Algebra A1 B1]
  [Module.IsTorsionFree A1 B1] [Algebra A1 K] [IsFractionRing A1 K] [Algebra A1 L] [IsScalarTower A1 K L]
  [Algebra B1 L] [IsFractionRing B1 L] [IsScalarTower A1 B1 L] [Module.Finite A1 B1]
  [IsIntegralClosure B1 A1 L] [Algebra.IsIntegral A1 B1]
  [CommRing A2] [IsDedekindDomain A2] [CommRing B2] [IsDedekindDomain B2] [Algebra A2 B2]
  [Module.IsTorsionFree A2 B2] [Algebra A2 K] [IsFractionRing A2 K] [Algebra A2 L] [IsScalarTower A2 K L]
  [Algebra B2 L] [IsFractionRing B2 L] [IsScalarTower A2 B2 L] [Module.Finite A2 B2]
  [IsIntegralClosure B2 A2 L] [Algebra.IsIntegral A2 B2]

end Builder

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_FF =====
section

/-!
# S4-GOS-B, part FF: Riemann-Hurwitz for an extension of function fields over `Fq`

For function fields `K → L` over `Fq` (both with the `Fq[X] ⊆ RatFunc Fq` package, compatible towers):
the chart instances (`Rfin`, `Rinf`), the cotrace `ffCotrace`, the different divisor `diffDiv` and
**`riemannHurwitz`**: `2 g_L - 2 ℓ_L(0) = [L:K] (2 g_K - 2 ℓ_K(0)) + deg Diff(L/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

section FF

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]

include Fq in
theorem finiteDimensional_ff : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite (RatFunc Fq) K L

include Fq in
theorem isSeparable_ff : Algebra.IsSeparable K L :=
  Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) K L

end FF

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Gal =====
section

/-!
# S4-GOS-B, part Gal: the charts of a Galois extension of function fields

For function fields `K → L` over `Fq` and a finite group `G` with `IsGaloisGroup G K L`: the action of `G` on
the charts `Rfin Fq L`, `Rinf Fq L`, and `IsGaloisGroup G (Rfin Fq K) (Rfin Fq L)`, `IsGaloisGroup G (Rinf Fq K) (Rinf Fq L)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsDedekindDomain

namespace RamanujanPetersson.GOS

section Gal

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

include K in
theorem smulCommClass_poly_gal : SMulCommClass G Fq[X] L :=
  ⟨fun g p x => by
    rw [← algebraMap_smul K p x, ← algebraMap_smul K p (g • x), smul_comm]⟩

end Gal

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_TowH =====
section

/-!
# S4-GOS-B, part TowH: the tower identity for a subgroup

For `IsGaloisGroup G Fq(X) L` and `H ≤ G`, with `L^H = fixF Fq L G H`:
**`Σ_{h ∈ H} Φ(h) = |H| χ_c(L^H)`** (`sum_Phi_subgroup`), where `Φ = Phi Fq (RatFunc Fq) L G` is the global
character of `G` (`Phi_subgroup`: the character of `H` on `L / L^H` is its restriction).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

section TowH

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]

instance isScalarTower_poly_intF (E : IntermediateField (RatFunc Fq) L) : IsScalarTower Fq[X] E L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G (RatFunc Fq) L]
variable (H : Subgroup G)

/-- The fixed field `L^H`. -/
abbrev fixF : IntermediateField (RatFunc Fq) L := FixedPoints.intermediateField H

end TowH

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Inv =====
section

/-!
# S4-GOS-B, part Inv: `Φ` is invariant under powers prime to the order

* `i_pow_of_coprime`: for a ramification function `R`, `R.i (σ ^ c) = R.i σ` when `c` is prime to `ord σ`;
* `iQ_pow_of_coprime`: the same for `i_Q` on the inertia group `I_Q`;
* **`Phi_pow_of_coprime`**: `Φ(τ ^ c) = Φ(τ)` for `c` prime to `ord τ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

section RamPow

variable {H : Type*} [Group H] (R : Swan.RamFn H)

theorem i_le_i_pow (σ : H) (k : ℕ) : R.i σ ≤ R.i (σ ^ k) := by
  induction k with
  | zero => rw [pow_zero, R.i_one]; exact le_top
  | succ k ih =>
    rw [pow_succ]
    exact le_trans (le_min ih le_rfl) (R.le_mul _ _)

theorem i_pow_of_coprime (σ : H) {c : ℕ} (hc : Nat.Coprime c (orderOf σ)) : R.i (σ ^ c) = R.i σ := by
  obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hc
  refine le_antisymm ?_ (i_le_i_pow R σ c)
  calc R.i (σ ^ c) ≤ R.i ((σ ^ c) ^ d) := i_le_i_pow R _ d
    _ = R.i σ := by rw [hd]

end RamPow

theorem pow_mem_iff_of_coprime {H : Type*} [Group H] (Hs : Subgroup H) (σ : H) {c : ℕ}
    (hc : Nat.Coprime c (orderOf σ)) : σ ^ c ∈ Hs ↔ σ ∈ Hs := by
  refine ⟨fun h => ?_, fun h => pow_mem h c⟩
  obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hc
  rw [← hd]
  exact pow_mem h d

theorem pow_eq_one_iff_of_coprime {H : Type*} [Group H] (σ : H) {c : ℕ}
    (hc : Nat.Coprime c (orderOf σ)) : σ ^ c = 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hc
  rw [← hd, h, one_pow]

section IQ

variable (L : Type*) [Field L] {G : Type*} [Group G] [Finite G] [MulSemiringAction G L]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L]
  [MulSemiringAction G S] {R : Type*} [CommRing R] [Algebra R S] [IsGaloisGroup G R S]

end IQ

section Tow

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

end Tow

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Mob =====
section

/-!
# S4-GOS-B, part Mob: a class function on cyclic subgroups is determined by its subgroup sums

If `f : G → R` (`R` without `ℕ`-torsion) is invariant under `τ ↦ τ ^ c` for `c` prime to the order of `τ`, and
`Σ_{c < ord τ} f(τ ^ c) = 0` for every `τ` in a power-closed set `S` of elements of finite order, then
`f = 0` on `S` (`eq_zero_of_sum_pow`). This is the Möbius step: the character of the perfect complex and the
global character `Φ` have the same sums over every cyclic `p`-subgroup and are both rational, so they agree.
-/

set_option autoImplicit false

namespace RamanujanPetersson.GOS

section Mob

variable {G R : Type*} [Group G] [AddCommGroup R] [NoZeroSMulDivisors ℕ R]

theorem orderOf_pow_lt {τ : G} (hτ : IsOfFinOrder τ) {c : ℕ} (hc : ¬ Nat.Coprime c (orderOf τ)) :
    orderOf (τ ^ c) < orderOf τ := by
  rw [hτ.orderOf_pow]
  have hg : 1 < Nat.gcd (orderOf τ) c := by
    have h0 : Nat.gcd (orderOf τ) c ≠ 0 := Nat.gcd_ne_zero_left hτ.orderOf_pos.ne'
    have h1 : Nat.gcd (orderOf τ) c ≠ 1 := by
      rw [Nat.gcd_comm]; exact hc
    omega
  exact Nat.div_lt_self hτ.orderOf_pos hg

/-- **Möbius step on cyclic subgroups.** -/
theorem eq_zero_of_sum_pow (S : Set G) (hS : ∀ τ ∈ S, ∀ c : ℕ, τ ^ c ∈ S) (hfin : ∀ τ ∈ S, IsOfFinOrder τ)
    (f : G → R) (hsum : ∀ τ ∈ S, ∑ c ∈ Finset.range (orderOf τ), f (τ ^ c) = 0)
    (hinv : ∀ τ ∈ S, ∀ c : ℕ, Nat.Coprime c (orderOf τ) → f (τ ^ c) = f τ) :
    ∀ τ ∈ S, f τ = 0 := by
  intro τ
  induction hm : orderOf τ using Nat.strong_induction_on generalizing τ with
  | _ m ih =>
  intro hτ
  have hpos : 0 < m := hm ▸ (hfin τ hτ).orderOf_pos
  have hterm : ∀ c ∈ Finset.range m, f (τ ^ c) = if Nat.Coprime m c then f τ else 0 := by
    intro c _
    split_ifs with hcop
    · exact hinv τ hτ c (by rw [hm]; exact hcop.symm)
    · have hlt : orderOf (τ ^ c) < m := by
        rw [← hm]
        exact orderOf_pow_lt (hfin τ hτ) (by rw [hm]; exact fun h => hcop h.symm)
      exact ih _ hlt (τ ^ c) rfl (hS τ hτ c)
  have hs := hsum τ hτ
  rw [hm, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    ← Nat.totient] at hs
  rcases smul_eq_zero.1 hs with h | h
  · exact absurd h (Nat.totient_pos.2 hpos).ne'
  · exact h

end Mob

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Rat =====
section

/-!
# S4-GOS-B, part Rat: an integral class function with the subgroup sums of `Φ` and Fermat congruences is `Φ`

* `eq_zero_of_large_prime_dvd`: an integer divisible by arbitrarily large primes is `0`;
* `pow_eq_of_prime_congr` (Dirichlet): if `r(σ ^ l) ≡ r(σ) mod l` for all primes `l > N₀`, then
  `r(σ ^ c) = r(σ)` for every `c` prime to `ord σ`;
* `sum_zpowers_eq_sum_range`: `Σ_{h ∈ ⟨τ⟩} g h = Σ_{c < ord τ} g (τ ^ c)`;
* **`eq_Phi_of_congr`**: `r : G → ℤ` with `r(σ ^ l) ≡ r(σ) mod l` (large primes `l`) and
  `Σ_{h ∈ ⟨τ⟩} r h = |⟨τ⟩| χ_c(L^⟨τ⟩)` for all `τ` is the global character `Φ` (finite places unramified).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsDedekindDomain Classical

namespace RamanujanPetersson.GOS

section Gen

theorem eq_zero_of_large_prime_dvd (a : ℤ) (h : ∀ B : ℕ, ∃ p > B, p.Prime ∧ (p : ℤ) ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨p, hp, -, hdvd⟩ := h a.natAbs
  have h1 : p ∣ a.natAbs := by
    rw [← Int.natAbs_dvd_natAbs] at hdvd
    simpa using hdvd
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 ha) h1
  omega

variable {G : Type*} [Group G] [Finite G]

theorem pow_eq_of_prime_congr (r : G → ℤ) (N0 : ℕ)
    (h1 : ∀ σ : G, ∀ l : ℕ, l.Prime → N0 < l → ((r (σ ^ l) : ZMod l) = (r σ : ZMod l)))
    (σ : G) {c : ℕ} (hc : Nat.Coprime c (orderOf σ)) : r (σ ^ c) = r σ := by
  have hm : 0 < orderOf σ := orderOf_pos σ
  haveI : NeZero (orderOf σ) := ⟨hm.ne'⟩
  have hu : IsUnit (c : ZMod (orderOf σ)) := by
    rw [← ZMod.coe_unitOfCoprime c hc]
    exact Units.isUnit _
  have key := eq_zero_of_large_prime_dvd (r σ - r (σ ^ c)) fun B => by
    obtain ⟨p, hpB, hp, hpc⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (B + N0)
    refine ⟨p, by omega, hp, ?_⟩
    have hpow : σ ^ p = σ ^ c := pow_eq_pow_iff_modEq.2 ((ZMod.natCast_eq_natCast_iff _ _ _).1 hpc)
    have := h1 σ p hp (by omega)
    rw [hpow] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this
  omega

theorem sum_zpowers_eq_sum_range {R : Type*} [AddCommMonoid R] [Fintype G] (g : G → R) (τ : G) :
    ∑ h : Subgroup.zpowers τ, g h = ∑ c ∈ Finset.range (orderOf τ), g (τ ^ c) := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => g (τ ^ c))]
  exact (Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite τ)) _ _
    (fun c => by rw [finEquivZPowers_apply])).symm

end Gen

section Ass

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
  [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
  [Algebra.IsSeparable (RatFunc Fq) L]
variable (G : Type*) [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G (RatFunc Fq) L]

end Ass

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Fer =====
section

/-!
# S4-GOS-B, part Fer: Fermat congruence for characters over `𝔽_l`

* `trace_pow_prime`: `Tr(f ^ l) = Tr(f)` for an endomorphism of a finite free `ZMod l`-module;
* **`chi_pow_prime`**: the character `σ ↦ Σ_{i ≤ N} (-1)^i Tr(ρ_i σ)` of a family of representations over `ZMod l`
  satisfies `χ(σ ^ l) = χ(σ)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.GOS

section Fer

variable {l : ℕ} [Fact l.Prime]

theorem toMatrix_pow_end {M : Type*} [AddCommGroup M] [Module (ZMod l) M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι (ZMod l) M) (f : M →ₗ[ZMod l] M) (n : ℕ) :
    LinearMap.toMatrix b b (f ^ n) = (LinearMap.toMatrix b b f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearMap.toMatrix_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]

theorem trace_pow_prime {M : Type*} [AddCommGroup M] [Module (ZMod l) M] [Module.Free (ZMod l) M]
    [Module.Finite (ZMod l) M] (f : M →ₗ[ZMod l] M) :
    LinearMap.trace (ZMod l) M (f ^ l) = LinearMap.trace (ZMod l) M f := by
  let b := Module.Free.chooseBasis (ZMod l) M
  rw [LinearMap.trace_eq_matrix_trace (ZMod l) b, LinearMap.trace_eq_matrix_trace (ZMod l) b,
    toMatrix_pow_end b, ZMod.trace_pow_card, ZMod.pow_card]

/-- **Fermat congruence for characters**: `χ(σ ^ l) = χ(σ)` over `ZMod l`. -/
theorem chi_pow_prime {G : Type*} [Group G] {P : ℕ → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module (ZMod l) (P i)] [∀ i, Module.Free (ZMod l) (P i)] [∀ i, Module.Finite (ZMod l) (P i)]
    (ρ : ∀ i, Representation (ZMod l) G (P i)) (N : ℕ) (σ : G) :
    ∑ i ∈ Finset.range (N + 1), (-1 : ZMod l) ^ i * LinearMap.trace (ZMod l) (P i) (ρ i (σ ^ l)) =
      ∑ i ∈ Finset.range (N + 1), (-1 : ZMod l) ^ i * LinearMap.trace (ZMod l) (P i) (ρ i σ) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, trace_pow_prime]

end Fer

end RamanujanPetersson.GOS

end

end

-- ===== S4.Def_RP_GOS_B_Sub =====
section

/-!
# S4-GOS-B, part Sub: subgroup sums of the point counts (O6b, group theory)

* `ptSet`, `ptFu`: the point data chosen in `ptSeq` (the `𝔽_{q^m}`-points of `U` in `K̄`, normalized Frobenius elements).
* `ptSeq_eq_sum`: `ptSeq γ m = Σ_{u} #{b ∈ Gf | b⁻¹ π(F_u) b = γ}` (`sum_card_conj_eq`).
* `card_mem_eq_sum`: `Σ_{h ∈ H'} #{b | b⁻¹ X b = h} = #{b | b⁻¹ X b ∈ H'}`.
* **`sum_ptSeq_subgroup`**: `Σ_{h ∈ H'} ptSeq h m = Σ_u #{b ∈ Gf | b⁻¹ π(F_u) b ∈ H'}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

open Representation Lefschetz

/-- `Σ_{h ∈ H'} #{b | b⁻¹ X b = h} = #{b | b⁻¹ X b ∈ H'}`. -/
theorem card_mem_eq_sum {G : Type} [Group G] [Finite G] (H' : Subgroup G) [Fintype H'] (X : G) :
    ∑ h : H', Nat.card {b : G // b⁻¹ * X * b = h} = Nat.card {b : G // b⁻¹ * X * b ∈ H'} := by
  have hf : ∀ h : H', Finite {b : G // b⁻¹ * X * b = h} := fun _ => inferInstance
  rw [← Nat.card_sigma]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.2.1, by rw [x.2.2]; exact x.1.2⟩
      invFun := fun b => ⟨⟨_, b.2⟩, ⟨b.1, rfl⟩⟩
      left_inv := ?_
      right_inv := fun b => rfl }
  rintro ⟨⟨h, hh⟩, ⟨b, hb⟩⟩
  obtain rfl : b⁻¹ * X * b = h := hb
  rfl

section Sub

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end Sub

end

end RamanujanPetersson.GOS


end

-- ===== S4.Def_RP_GOS_B_Shf =====
section

/-!
# S4-GOS-B, part Shf: integer linear recurrences through the shift operator (O6d, algebra)

* `shiftE R`: the shift `s ↦ (k ↦ s (k + 1))` on `ℕ → R`; `aeval_shiftE_apply`:
  `aeval (shiftE R) P s k = Σ_{j ≤ deg P} P_j s (k + j)`.
* closure: `aeval_add_of`, `aeval_sub_of`, `aeval_prod_sum` (a product annihilates a sum);
  annihilators: `aeval_X_sub_C_geom` (`c^k`), `aeval_X_pow_sub_one` (`n`-periodic), `aeval_prod_powsum`
  (power sums of a multiset); `aeval_int_of_complex` (descent from `ℂ` to `ℤ`).
* `dil d a m = [d ∣ m] d a(m/d)`; `aeval_expand_dil_eq_zero`: `P(X)` kills `a` ⟹ `P(X^d)` kills `dil d a`.
* **`exists_rec_weil`**: for `a k = 1 + Q^k - Σ_{α ∈ c} α^k` with `Π α = Q^g` and `Π (X - α) ∈ ℤ[X]`, the sequence
  `dil d a - Σ_i [n_i ∣ m] n_i` satisfies an integer recurrence with leading coefficient `± Q^(g+1)`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.GOS

noncomputable section

section Shift

variable (R : Type) [CommRing R]

/-- The shift `s ↦ (k ↦ s (k + 1))` on sequences. -/
def shiftE : Module.End R (ℕ → R) where
  toFun s k := s (k + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {R}

theorem shiftE_pow_apply (j : ℕ) (s : ℕ → R) (k : ℕ) : (shiftE R ^ j) s k = s (k + j) := by
  induction j generalizing s with
  | zero => rw [pow_zero, Module.End.one_apply, add_zero]
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    show s (k + j + 1) = s (k + (j + 1))
    rw [add_assoc]

theorem aeval_shiftE_apply (P : R[X]) (s : ℕ → R) (k : ℕ) :
    aeval (shiftE R) P s k = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * s (k + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shiftE_pow_apply, smul_eq_mul]

theorem aeval_mul_eq_zero (P Q : R[X]) {s : ℕ → R} (h : aeval (shiftE R) Q s = 0) :
    aeval (shiftE R) (P * Q) s = 0 := by
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem aeval_add_of (P Q : R[X]) {s t : ℕ → R} (hs : aeval (shiftE R) P s = 0)
    (ht : aeval (shiftE R) Q t = 0) : aeval (shiftE R) (P * Q) (s + t) = 0 := by
  have h1 : aeval (shiftE R) (P * Q) s = 0 := by rw [mul_comm]; exact aeval_mul_eq_zero Q P hs
  rw [LinearMap.map_add, h1, aeval_mul_eq_zero P Q ht, add_zero]

theorem aeval_sub_of (P Q : R[X]) {s t : ℕ → R} (hs : aeval (shiftE R) P s = 0)
    (ht : aeval (shiftE R) Q t = 0) : aeval (shiftE R) (P * Q) (s - t) = 0 := by
  have h1 : aeval (shiftE R) (P * Q) s = 0 := by rw [mul_comm]; exact aeval_mul_eq_zero Q P hs
  rw [LinearMap.map_sub, h1, aeval_mul_eq_zero P Q ht, sub_zero]

theorem aeval_prod_sum {ι : Type} (S : Finset ι) (P : ι → R[X]) (f : ι → ℕ → R) :
    (∀ i ∈ S, aeval (shiftE R) (P i) (f i) = 0) → aeval (shiftE R) (∏ i ∈ S, P i) (∑ i ∈ S, f i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => intro _; rw [Finset.sum_empty, map_zero]
  | insert i S hi ih =>
    intro h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact aeval_add_of _ _ (h i (Finset.mem_insert_self i S))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem aeval_X_sub_C_geom (c : R) : aeval (shiftE R) (X - C c) (fun k => c ^ k) = 0 := by
  funext k
  rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  show c ^ (k + 1) - c * c ^ k = 0
  ring

theorem aeval_X_pow_sub_one {n : ℕ} {s : ℕ → R} (hs : ∀ k, s (k + n) = s k) :
    aeval (shiftE R) (X ^ n - 1 : R[X]) s = 0 := by
  funext k
  rw [map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Pi.sub_apply, shiftE_pow_apply,
    Module.End.one_apply, hs, sub_self, Pi.zero_apply]

theorem aeval_prod_powsum (c : Multiset R) :
    aeval (shiftE R) (c.map fun r => X - C r).prod (fun k => (c.map (· ^ k)).sum) = 0 := by
  induction c using Multiset.induction_on with
  | empty =>
    funext k
    simp
  | cons r c ih =>
    have h : (fun k => ((r ::ₘ c).map (· ^ k)).sum) = (fun k => r ^ k) + (fun k => (c.map (· ^ k)).sum) := by
      funext k
      simp
    rw [Multiset.map_cons, Multiset.prod_cons, h]
    exact aeval_add_of _ _ (aeval_X_sub_C_geom r) ih

theorem aeval_int_of_complex (P : ℤ[X]) (s : ℕ → ℤ)
    (h : aeval (shiftE ℂ) (P.map (Int.castRingHom ℂ)) (fun k => (s k : ℂ)) = 0) : aeval (shiftE ℤ) P s = 0 := by
  funext k
  have hk := congr_fun h k
  rw [aeval_shiftE_apply, natDegree_map_eq_of_injective (RingHom.injective_int _), Pi.zero_apply] at hk
  simp only [coeff_map, eq_intCast] at hk
  rw [aeval_shiftE_apply, Pi.zero_apply]
  exact_mod_cast hk

end Shift

section Dil

variable {R : Type} [CommRing R]

/-- The dilation `m ↦ [d ∣ m] d a(m/d)`. -/
def dil (d : ℕ) (a : ℕ → R) (m : ℕ) : R := if d ∣ m then (d : R) * a (m / d) else 0

theorem dil_add (d : ℕ) (a b : ℕ → R) : dil d (a + b) = dil d a + dil d b := by
  funext m
  simp only [dil, Pi.add_apply]
  split_ifs <;> ring

theorem dil_smul (d : ℕ) (c : R) (a : ℕ → R) : dil d (c • a) = c • dil d a := by
  funext m
  simp only [dil, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem dil_zero (d : ℕ) : dil d (0 : ℕ → R) = 0 := by
  funext m
  simp [dil]

theorem shiftE_pow_dil {d : ℕ} (hd : 0 < d) (a : ℕ → R) : (shiftE R ^ d) (dil d a) = dil d (shiftE R a) := by
  funext m
  rw [shiftE_pow_apply]
  unfold dil
  by_cases h : d ∣ m
  · rw [if_pos ((Nat.dvd_add_right h).2 (dvd_refl d)), if_pos h, Nat.add_div_right m hd]
    rfl
  · rw [if_neg (fun h' => h (Nat.dvd_add_self_right.1 h')), if_neg h]

theorem pow_shiftE_pow_dil {d : ℕ} (hd : 0 < d) (n : ℕ) (a : ℕ → R) :
    ((shiftE R ^ d) ^ n) (dil d a) = dil d ((shiftE R ^ n) a) := by
  induction n generalizing a with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, shiftE_pow_dil hd, ih, pow_succ, Module.End.mul_apply]

end Dil

end

end RamanujanPetersson.GOS


end


