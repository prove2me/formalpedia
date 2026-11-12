-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterOrbitFree
-- name    : OddOrder_GroupTheory_RepresentationTheory_CenterOrbitFree
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:44.104486+00:00
-- url     : https://prove2.me/theorems/b4ca514d-38c4-438a-bc9d-6207a7305347
-- title:
--   A coprime fixed-point-free automorphism fixes only the trivial conjugacy class
-- statement:
--   For the kernel-FPF count ($\dagger$) of Peterfalvi (9.1) (step 3d.2): a Frobenius-complement element $e$ acting by conjugation on the kernel $U$ fixes only the trivial conjugacy class, i.e. $\langle e\rangle$ acts freely on the nontrivial classes. The group-theoretic crux is `map_eq_self_imp_eq_trivial_of_fpf`: if $\beta$ generates a cyclic group of order coprime to $|G|$ and acts without nonidentity fixed points, then any $\beta$-fixed conjugacy class is trivial. Via the Brauer equality the action is also free on the nontrivial simples.
--
--   The main declaration: `gamma_free_off_trivial_simple` (3d.3c: a coprime Frobenius complement acts freely on the nontrivial simples).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CenterOrbitFree.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CenterOrbitFree.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterSimplesOrbit
import Definitions.Def_OddOrder_GroupTheory_FreeActionOrbitCount
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03

open OddOrder.Isaacs.Ch04 (glauberman_fixed_point_exists IsCompatibleMulAction)

open OddOrder.GroupTheory.CenterClassSum

open OddOrder.GroupTheory.CenterSimplesOrbit (simplesAction exists_fixed_simple
  card_simples_eq_card_classes card_orbits_classes_eq_card_orbits_simples_comp)

open OddOrder.GroupTheory.FreeActionOrbitCount (card_orbits_eq_of_free_off_unique_fixed
  dvd_card_sub_one_of_free_off_unique_fixed orbit_trivial_or_free_of_card_orbits)

open MulAction

namespace OddOrder.GroupTheory.CenterOrbitFree

variable {G : Type*} [Group G] [Finite G]

/-- **A coprime fixed-point-free automorphism fixes only the trivial conjugacy class.**
If `β : MulAut G` generates a cyclic group of order coprime to `|G|` (`hCop`) and acts without
nonidentity fixed points (`hFPF : β x = x → x = 1`), then any `β`-fixed conjugacy class `C`
(`hC : β • C = C`) is the trivial class `mk 1`.

Proof: the cyclic group `A = ⟨β⟩` acts on `C` realised as the transitive `G`-conjugation set
`Ω = {y // mk y = C}`, compatibly with conjugation (`β(g y g⁻¹) = β g · β y · (β g)⁻¹`).  Glauberman
(Isaacs 3.24(a)) yields a `β`-fixed element `y ∈ C`; `β y = y` and `hFPF` give `y = 1`, so
`C = mk y = mk 1`. -/
theorem map_eq_self_imp_eq_trivial_of_fpf (β : MulAut G)
    (hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers β)) (Nat.card G))
    (hFPF : ∀ x : G, β x = x → x = 1)
    {C : ConjClasses G} (hC : β • C = C) :
    C = ConjClasses.mk 1 := by
  classical
  -- The acting cyclic group `A = ⟨β⟩` and its inclusion `φ` into `MulAut G`.
  let φ : ↥(Subgroup.zpowers β) →* MulAut G := (Subgroup.zpowers β).subtype
  -- Every element of `⟨β⟩` fixes `C`: the stabiliser is a subgroup containing `β`.
  have hAfix : ∀ a : ↥(Subgroup.zpowers β), (φ a) • C = C := fun a =>
    MulAction.mem_stabilizer_iff.mp
      (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hC) a.2)
  -- `Ω` := the class `C` as a subtype, nonempty (it has a representative).
  obtain ⟨x₀, hx₀⟩ := ConjClasses.mk_surjective C
  let Ω := {y : G // ConjClasses.mk y = C}
  have : Nonempty Ω := ⟨⟨x₀, hx₀⟩⟩
  -- `G` acts on `Ω` by conjugation (class-preserving).
  let mulG : MulAction G Ω := {
    smul := fun g y => ⟨g * y.1 * g⁻¹,
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)).trans y.2⟩
    one_smul := fun y => Subtype.ext (by change (1 : G) * y.1 * (1 : G)⁻¹ = y.1; group)
    mul_smul := fun g g' y =>
      Subtype.ext (by change (g * g') * y.1 * (g * g')⁻¹ = g * (g' * y.1 * g'⁻¹) * g⁻¹; group) }
  -- `A = ⟨β⟩` acts on `Ω` via `φ` (well-defined since every `a ∈ ⟨β⟩` fixes `C`).
  let mulA : MulAction (↥(Subgroup.zpowers β)) Ω := {
    smul := fun a y => ⟨(φ a) y.1, by rw [← mulAut_smul_mk, y.2, hAfix a]⟩
    one_smul := fun y => Subtype.ext (by change (φ 1) y.1 = y.1; simp)
    mul_smul := fun a b y =>
      Subtype.ext (by change (φ (a * b)) y.1 = (φ a) ((φ b) y.1); simp [map_mul]) }
  -- Conjugation and the `φ`-action are compatible.
  have hCompat : IsCompatibleMulAction φ Ω := by
    intro a g y
    apply Subtype.ext
    change (φ a) (g * y.1 * g⁻¹) = (φ a g) * ((φ a) y.1) * (φ a g)⁻¹
    rw [map_mul, map_mul, map_inv]
  -- `G` acts transitively on `Ω` (any two representatives of `C` are conjugate).
  have hG_trans : MulAction.IsPretransitive G Ω := by
    refine ⟨fun y z => ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (y.2.trans z.2.symm))
    exact ⟨c, Subtype.ext hc⟩
  -- `⟨β⟩` is commutative, hence solvable (so Glauberman's solvability hypothesis holds).
  have : Group.IsSolvable (↥(Subgroup.zpowers β)) :=
    Group.isSolvable_of_comm fun a b => mul_comm' a b
  -- Glauberman 3.24(a): a `⟨β⟩`-fixed element of `Ω` exists.
  obtain ⟨ω₀, hω₀⟩ := glauberman_fixed_point_exists (G := G) (A := ↥(Subgroup.zpowers β)) (φ := φ)
    hCop (Or.inl inferInstance) (Ω := Ω) hCompat hG_trans
  -- It is `β`-fixed, hence trivial by `hFPF`; so `C = mk 1`.
  have hβfix : β ω₀.1 = ω₀.1 := Subtype.ext_iff.mp (hω₀ ⟨β, Subgroup.mem_zpowers β⟩)
  rw [← ω₀.2, hFPF ω₀.1 hβfix]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **3d.3c: a coprime Frobenius complement acts freely on the nontrivial simples.**
Let the kernel `G` be finite with splitting `φ : Z(k[G]) ≃ₐ[k] (Fin N → k)`, and let a finite group
`Γ` (the complement) act through `ψ : Γ →* MulAut G` so that every nonidentity `ψ γ` is
fixed-point-free on `G` (`hfpf`) with `⟨ψ γ⟩` coprime to `|G|` (`hcop`).  Then on the simples
`Fin N` (acted on through `simplesAction φ ∘ ψ`, agreement `hsi`) there is a **unique** `Γ`-fixed
point — the trivial simple `i₀` — and `Γ` acts **freely** off it (every other orbit has size `|Γ|`).

Proof: on the conjugacy classes (agreement `hcl`), `mk 1` is fixed and, by
`map_eq_self_imp_eq_trivial_of_fpf` (3d.2), is the *only* fixed class, with trivial stabilisers
elsewhere — so `Γ` is free off `mk 1`.  The orbit count `1 + (#classes − 1)/|Γ|` and divisibility
`|Γ| ∣ #classes − 1` carry over to the simples by the orbit-count Brauer equality (3d.1) and
`N = #classes` (N=Ncl); `orbit_trivial_or_free_of_card_orbits` (3d.3a) then forces the simples
action to be free off a single fixed point, identified as `i₀` by `exists_fixed_simple` (3d.3b). -/
theorem gamma_free_off_trivial_simple
    {k : Type*} [Field k] {N : ℕ}
    (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))
    {Γ : Type*} [Group Γ] [Finite Γ] (ψ : Γ →* MulAut G)
    [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [MulAction Γ (ConjClasses G)] [MulAction Γ (Fin N)]
    (hcl : ∀ (γ : Γ) (C : ConjClasses G), γ • C = ψ γ • C)
    (hsi : ∀ (γ : Γ) (i : Fin N), γ • i = simplesAction φ (ψ γ) i)
    (hd : 1 < Nat.card Γ)
    (hcop : ∀ γ : Γ, γ ≠ 1 → Nat.Coprime (Nat.card ↥(Subgroup.zpowers (ψ γ))) (Nat.card G))
    (hfpf : ∀ γ : Γ, γ ≠ 1 → ∀ x : G, ψ γ x = x → x = 1) :
    ∃ i₀ : Fin N, i₀ ∈ fixedPoints Γ (Fin N) ∧
      (∀ i : Fin N, i ∈ fixedPoints Γ (Fin N) → i = i₀) ∧
      (∀ i : Fin N, i ∉ fixedPoints Γ (Fin N) → Nat.card (orbit Γ i) = Nat.card Γ) := by
  classical
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ : Γ, γ ≠ 1 :=
    haveI : Nontrivial Γ := Finite.one_lt_card_iff_nontrivial.mp hd
    exists_ne 1
  -- CLASS SIDE: `Γ` is free off the trivial class `mk 1`.
  have hx₀ : (ConjClasses.mk 1 : ConjClasses G) ∈ fixedPoints Γ (ConjClasses G) :=
    mem_fixedPoints.mpr fun γ => by rw [hcl, mulAut_smul_mk, map_one]
  have huniqC : ∀ C : ConjClasses G, C ∈ fixedPoints Γ (ConjClasses G) → C = ConjClasses.mk 1 :=
    fun C hC => map_eq_self_imp_eq_trivial_of_fpf (ψ γ₀) (hcop γ₀ hγ₀) (hfpf γ₀ hγ₀)
      (by rw [← hcl]; exact mem_fixedPoints.mp hC γ₀)
  have hfreeC : ∀ C : ConjClasses G, C ∉ fixedPoints Γ (ConjClasses G) →
      Nat.card (orbit Γ C) = Nat.card Γ := by
    intro C hC
    have hstab : stabilizer Γ C = ⊥ := by
      rw [eq_bot_iff]
      intro γ hγ
      by_contra hγ1
      have hγne : γ ≠ 1 := fun h => hγ1 (Subgroup.mem_bot.mpr h)
      have hCmk : C = ConjClasses.mk 1 :=
        map_eq_self_imp_eq_trivial_of_fpf (ψ γ) (hcop γ hγne) (hfpf γ hγne)
          (by rw [← hcl]; exact mem_stabilizer_iff.mp hγ)
      rw [hCmk] at hC; exact hC hx₀
    calc Nat.card (orbit Γ C)
        = Nat.card (Γ ⧸ stabilizer Γ C) := Nat.card_congr (orbitEquivQuotientStabilizer Γ C)
      _ = Nat.card (Γ ⧸ (⊥ : Subgroup Γ)) := by rw [hstab]
      _ = Nat.card Γ := Nat.card_congr QuotientGroup.quotientBot.toEquiv
  -- carry the orbit count and divisibility from classes to simples.
  have horbC := card_orbits_eq_of_free_off_unique_fixed (ConjClasses.mk 1) hx₀ huniqC hfreeC
  have hdvdC := dvd_card_sub_one_of_free_off_unique_fixed (ConjClasses.mk 1) hx₀ huniqC hfreeC
  have hBr := card_orbits_classes_eq_card_orbits_simples_comp φ ψ hcl hsi
  have hNcl : Nat.card (Fin N) = Nat.card (ConjClasses G) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact card_simples_eq_card_classes φ
  have horbS : Nat.card (orbitRel.Quotient Γ (Fin N))
      = 1 + (Nat.card (Fin N) - 1) / Nat.card Γ := by rw [← hBr, horbC, hNcl]
  have hdvdS : Nat.card Γ ∣ Nat.card (Fin N) - 1 := by rw [hNcl]; exact hdvdC
  have : Nonempty (Fin N) := by
    have hpos : 0 < Nat.card (Fin N) := by
      rw [hNcl]; have : Nonempty (ConjClasses G) := ⟨ConjClasses.mk 1⟩; exact Nat.card_pos
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hpos
    exact Fin.pos_iff_nonempty.mp hpos
  -- 3d.3a: every simples orbit has size `1` or `|Γ|`, with at most one fixed point.
  obtain ⟨hsize, hatmost⟩ := orbit_trivial_or_free_of_card_orbits hd horbS hdvdS
  -- 3d.3b: the trivial simple `i₀` is `Γ`-fixed.
  obtain ⟨i₀, hi₀⟩ := exists_fixed_simple φ
  have hi₀fix : i₀ ∈ fixedPoints Γ (Fin N) :=
    mem_fixedPoints.mpr fun γ => by rw [hsi]; exact hi₀ (ψ γ)
  refine ⟨i₀, hi₀fix, fun i hi => hatmost i i₀ hi hi₀fix, fun i hi => ?_⟩
  rcases hsize i with h1 | hdd
  · have : Fintype (orbit Γ i) := Fintype.ofFinite _
    exact absurd (mem_fixedPoints_iff_card_orbit_eq_one.mpr
      (by rw [← Nat.card_eq_fintype_card]; exact h1)) hi
  · exact hdd

end OddOrder.GroupTheory.CenterOrbitFree


