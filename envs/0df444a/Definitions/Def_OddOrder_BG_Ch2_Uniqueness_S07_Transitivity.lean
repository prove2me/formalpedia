-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
-- name    : OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:12:00.415385+00:00
-- url     : https://prove2.me/theorems/ca10680e-b495-49b0-9336-6757aec07caf
-- title:
--   BG §7: transitivity (tail)
-- statement:
--   The final part of the Bender–Glauberman §7 transitivity development. The bundle consists of lemmas only.
--
--   The bundle also proves 22 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Hypothesis75

namespace OddOrder.BG.Ch2.S07

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06 (actionFixedBy mem_actionFixedBy nontrivialActionFixedByClosure
  nontrivialActionFixedByClosure_le_iff)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Reduction for Hypothesis 7.1(2)** (mmd L2273 "it suffices to show that `Y ⊆ O_{π'}(X)`"):
for a fixed proper `X ⊇ A`, the equality `⟨ℋ_X(A;π)⟩ = O_π(X)` is equivalent to showing every
member of `ℋ_X(A;π)` is contained in `O_π(X)`. The reverse inclusion is automatic because
`O_π(X) = opiCoreInG π X` is itself an `A`-invariant `π`-subgroup of `X`
(`opiCoreInG_le` + `le_normalizer_opiCoreInG` with `A ≤ X` + `isPiSubgroup_opiCoreInG`).
Used by both branches of Proposition 7.5. -/
theorem generated_eq_of_forall_le_opiCoreInG [Finite G]
    {A X : Subgroup G} {π : Set ℕ} (hAX : A ≤ X)
    (hY : ∀ Y ∈ hInvariant X A π, Y ≤ opiCoreInG π X) :
    sSup (hInvariant X A π) = opiCoreInG π X := by
  refine le_antisymm (sSup_le hY) (le_sSup ?_)
  exact ⟨opiCoreInG_le π X, hAX.trans (le_normalizer_opiCoreInG π X),
    isPiSubgroup_opiCoreInG π X⟩

/-- **`oPiCore` is natural under a group isomorphism**: `(O_π G₁).map φ = O_π G₂` for
`φ : G₁ ≃* G₂` (apply `oPiCore.map_le_of_surjective` to `φ` and to `φ.symm`). General lemma;
could be promoted to `Ch03`. Used by `opiCoreInG_eq_map_subgroupOf`. -/
private theorem oPiCore_map_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (π : Set ℕ) (φ : G₁ ≃* G₂) :
    (Ch03.oPiCore π G₁).map φ.toMonoidHom = Ch03.oPiCore π G₂ := by
  refine le_antisymm (Ch03.oPiCore.map_le_of_surjective π φ.toMonoidHom φ.surjective) ?_
  intro h hh
  exact ⟨φ.symm h,
    Ch03.oPiCore.map_le_of_surjective π φ.symm.toMonoidHom φ.symm.surjective ⟨h, hh, rfl⟩, by simp⟩

/-- **`opiCoreInG` transport to an intermediate subgroup**: for `K ≤ X`,
`O_π(K) = O_π(K.subgroupOf X)` mapped from `↥X` back to `G`. Lets one apply a result proved
inside `↥X` (e.g. Proposition 1.15(b) with ambient group `↥X`) to the ambient realization
`opiCoreInG π K`. General lemma; could be promoted to `SubgroupInAmbient`. -/
private theorem opiCoreInG_eq_map_subgroupOf [Finite G] {π : Set ℕ} {X K : Subgroup G}
    (hKX : K ≤ X) :
    opiCoreInG π K = (opiCoreInG π (K.subgroupOf X)).map X.subtype := by
  have hcomp : X.subtype.comp (K.subgroupOf X).subtype
      = K.subtype.comp (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  calc opiCoreInG π K
      = ((Ch03.oPiCore π ↥(K.subgroupOf X)).map
            (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom).map K.subtype := by
        rw [oPiCore_map_mulEquiv]; rfl
    _ = (Ch03.oPiCore π ↥(K.subgroupOf X)).map
            (K.subtype.comp (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(K.subgroupOf X)).map (X.subtype.comp (K.subgroupOf X).subtype) := by
        rw [hcomp]
    _ = (opiCoreInG π (K.subgroupOf X)).map X.subtype := by
        rw [← Subgroup.map_map]; rfl

/-- **Relativized BG Proposition 1.15(b)**: for a finite solvable subgroup `X ≤ G` and a
`p`-subgroup `R ≤ X`, `O_{p'}(C_X(R)) ≤ O_{p'}(X)` (both realized in the ambient `G`). Obtained
from the absolute Prop 1.15(b) (`oPiPrimeCore_centralizer_le_oPiPrimeCore`) inside the group `↥X`,
transported back to `G` via `opiCoreInG_eq_map_subgroupOf`. Here `C_X(R) = C_G(R) ⊓ X`. This is
the cross-group bridge for Proposition 7.5's general case (and is reusable in §8–§16). -/
theorem opiCoreInG_centralizer_inf_le_opiCoreInG [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hXsolv : Group.IsSolvable ↥X) {R : Subgroup G} (hRX : R ≤ X)
        (hRp : IsPGroup p R) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G) ⊓ X)
      ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  have := hXsolv
  have hR'p : IsPGroup p (R.subgroupOf X) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv]; exact hn)
  have hbridge : (Subgroup.centralizer (R : Set G) ⊓ X).subgroupOf X
      = Subgroup.centralizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hc, -⟩ m hm
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
      exact Subtype.ext (hc (m : G) hm)
    · intro hc
      refine ⟨?_, x.2⟩
      intro r hr
      exact congrArg Subtype.val
        (hc ⟨r, hRX hr⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hr))
  have habs := OddOrder.BG.Ch1.S01.oPiPrimeCore_centralizer_le_oPiPrimeCore (G := ↥X) hR'p
  calc opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G) ⊓ X)
      = (opiCoreInG ({p} : Set ℕ)ᶜ
          ((Subgroup.centralizer (R : Set G) ⊓ X).subgroupOf X)).map X.subtype :=
        opiCoreInG_eq_map_subgroupOf inf_le_right
    _ = (opiCoreInG ({p} : Set ℕ)ᶜ
          (Subgroup.centralizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X))).map X.subtype := by
        rw [hbridge]
    _ ≤ (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥X).map X.subtype := Subgroup.map_mono habs
    _ = opiCoreInG ({p} : Set ℕ)ᶜ X := rfl

/-- **Bar-quotient bridge** for Proposition 7.5's special case: the image of `O_{π',π}(G')` under
the quotient `mk' : G' → G'/O_{π'}(G')` is exactly `O_π(G'/O_{π'}(G'))` — i.e.
`O_p(X̄) = mk(O_{p',p}(X))`.
Immediate from `oPiPrimePiCore` being defined as `comap (mk' O_{π'}) (O_π of the quotient)` plus
`map_comap_eq_self_of_surjective`. With Theorem 6.1 (`thmA4b`: `A ≤ O_{p',p}(X)`) this gives
`Ā ≤ O_p(X̄)`. -/
private theorem oPiPrimePiCore_map_mk'_eq {G' : Type*} [Group G'] (π : Set ℕ) :
    (Ch03.oPiPrimePiCore π G').map (QuotientGroup.mk' (Ch03.oPiCore {p | p ∉ π} G'))
      = Ch03.oPiCore π (G' ⧸ Ch03.oPiCore {p | p ∉ π} G') := by
  rw [Ch03.oPiPrimePiCore]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- **Step 6 of Prop 7.5's special case** (`C_{O_p(X̄)}(Ā) ⊆ Ā`): with `N = O_{p'}(G')` and
`mk : G' → G'/N`, if `c ∈ O_p(G'/N)` commutes with `mk a` for every `a ∈ A`, then `c ∈ mk(A)`.
Clean route avoiding an explicit Sylow iso: `O_p(X̄) ⊆ mk(P)` (image of the Sylow `P` is Sylow,
and `O_p ≤` every Sylow), so `c = mk s` with `s ∈ P`; then for `a ∈ A`, `[a,s] ∈ N ⊓ P = ⊥`
(it lies in `N` since `mk` kills it, and in `P` since `a, s ∈ P`), so `s ∈ C_P(A) ⊆ A`. -/
private theorem mem_map_mk'_of_mem_oPiCore_quotient_of_commute
    {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    (P : Sylow p G') {A : Subgroup G'} (hAP : A ≤ (P : Subgroup G'))
    (hCPA : Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') ≤ A)
    {c : G' ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ G'}
    (hc : c ∈ Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ G'))
    (hcomm : ∀ a ∈ A, QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a * c
        = c * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a) :
    c ∈ A.map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) :=
    QuotientGroup.mk'_surjective _
  -- `N := O_{p'}(G')` is a `p'`-group, so `P ⊓ N = ⊥`.
  have hN_cop : Nat.Coprime (Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hPN : (P : Subgroup G') ⊓ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' = ⊥ :=
    OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime P.2 hN_cop
  -- `O_p(X̄) ⊆ mk(P)`: the image of the Sylow `P` is Sylow, and `O_p ≤` every Sylow.
  have hc_inP :
      c ∈ (P : Subgroup G').map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G')) := by
    have hle := OddOrder.Isaacs.Ch01.opCore_le (P.mapSurjective hsurj)
    rw [Sylow.coe_mapSurjective, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore] at hle
    exact hle hc
  obtain ⟨s, hsP, hsc⟩ := Subgroup.mem_map.mp hc_inP
  -- `s ∈ C_P(A)`: for `a ∈ A`, `[a,s] ∈ N ⊓ P = ⊥`.
  have hs_cent : s ∈ Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') := by
    refine Subgroup.mem_inf.mpr ⟨?_, hsP⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmkcomm : QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a
          * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') s
        = QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') s
          * QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G') a := by
      rw [hsc]; exact hcomm a ha
    have hin_N : a * s * a⁻¹ * s⁻¹ ∈ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' := by
      rw [← QuotientGroup.ker_mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ G'), MonoidHom.mem_ker,
        map_mul, map_mul, map_mul, map_inv, map_inv, hmkcomm]
      group
    have hin_P : a * s * a⁻¹ * s⁻¹ ∈ (P : Subgroup G') :=
      (P : Subgroup G').mul_mem ((P : Subgroup G').mul_mem
        ((P : Subgroup G').mul_mem (hAP ha) hsP) ((P : Subgroup G').inv_mem (hAP ha)))
        ((P : Subgroup G').inv_mem hsP)
    have h1 : a * s * a⁻¹ * s⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hPN ▸ Subgroup.mem_inf.mpr ⟨hin_P, hin_N⟩)
    have h2 : a * s * a⁻¹ = s := mul_inv_eq_one.mp h1
    calc a * s = a * s * a⁻¹ * a := by group
      _ = s * a := by rw [h2]
  rw [← hsc]
  exact Subgroup.mem_map_of_mem _ (hCPA hs_cent)

/-- **Abstract special case of BG Proposition 7.5** (mmd L2275-2285), `b`-independent and reusable:
if `G'` is finite solvable of odd order, `P` is a Sylow `p`-subgroup, `A ≤ P` is abelian and normal
in `P` with `C_P(A) ⊆ A`, and `Y` is an `A`-invariant `p'`-subgroup, then `Y ≤ O_{p'}(G')`.

Proof (in the bar-quotient `X̄ = G'/O_{p'}(G')`): Theorem 6.1 puts `Ā ≤ O_p(X̄)`; the commutator
`[Ā,Ȳ] ≤ O_p(X̄) ⊓ Ȳ = 1` so `Ā` centralizes `Ȳ`; step 6
(`mem_map_mk'_of_mem_oPiCore_quotient_of_commute`) gives `C_{O_p(X̄)}(Ā) ⊆ Ā`; Proposition 1.10 then
makes `Ȳ` centralize `O_p(X̄)`, and Proposition 1.15(a) forces `Ȳ ≤ O_p(X̄)`, whence `Ȳ = 1`. -/
private theorem specialCase
    {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G'] [Group.IsSolvable G']
    (hp2 : p ≠ 2) (hodd : Odd (Nat.card G')) (P : Sylow p G')
    {A : Subgroup G'} (hAP : A ≤ (P : Subgroup G')) [IsMulCommutative A]
    (hAnormP : (P : Subgroup G') ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G') ⊓ (P : Subgroup G') ≤ A)
    {Y : Subgroup G'} (hYnorm : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y) :
    Y ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' := by
  classical
  set N : Subgroup G' := Ch03.oPiCore ({p} : Set ℕ)ᶜ G' with hN
  set mk := QuotientGroup.mk' N with hmkdef
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective N
  have hker : mk.ker = N := QuotientGroup.ker_mk' N
  set Q : Subgroup (G' ⧸ N) := Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ N) with hQ
  have hQnorm : Q.Normal := by rw [hQ]; infer_instance
  set Ybar : Subgroup (G' ⧸ N) := Y.map mk with hYbar
  set Abar : Subgroup (G' ⧸ N) := A.map mk with hAbar
  -- `Q = O_p(X̄)` is a `p`-group; `Ȳ` is a `p'`-group; hence `Q ⊓ Ȳ = ⊥`.
  have hQ_pg : IsPGroup p ↥Q := by
    rw [hQ, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p _
  have hYbar_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Ybar := by
    intro q hq
    have hdvd : Nat.card ↥Ybar ∣ Nat.card ↥Y := by rw [hYbar]; exact Subgroup.card_map_dvd _ _
    exact hYpi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
  have hYbar_cop : Nat.Coprime (Nat.card ↥Ybar) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      exact hYbar_pi q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hQYbot : Q ⊓ Ybar = ⊥ := OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQ_pg hYbar_cop
  -- Theorem 6.1 (`thmA4b`) ⟹ `A ≤ O_{p',p}(G')` ⟹ `Ā ≤ Q`.
  have hThm61 : A ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) G' :=
    OddOrder.BG.AppA.thmA4b hp2 ‹Group.IsSolvable G'› hodd P hAP hAnormP
  have hAbar_le_Q : Abar ≤ Q := by rw [hAbar]; exact Subgroup.map_le_iff_le_comap.mpr hThm61
  -- `[Ā,Ȳ] = 1`: each commutator lies in `Q ⊓ Ȳ = ⊥`.
  have hcommute : ∀ a' ∈ Abar, ∀ y' ∈ Ybar, a' * y' * a'⁻¹ * y'⁻¹ = 1 := by
    intro a' ha' y' hy'
    have hin_Q : a' * y' * a'⁻¹ * y'⁻¹ ∈ Q := by
      have ha'Q : a' ∈ Q := hAbar_le_Q ha'
      have hconj : y' * a'⁻¹ * y'⁻¹ ∈ Q := hQnorm.conj_mem a'⁻¹ (Q.inv_mem ha'Q) y'
      have heq : a' * y' * a'⁻¹ * y'⁻¹ = a' * (y' * a'⁻¹ * y'⁻¹) := by group
      rw [heq]; exact Q.mul_mem ha'Q hconj
    have hin_Y : a' * y' * a'⁻¹ * y'⁻¹ ∈ Ybar := by
      rw [hAbar, Subgroup.mem_map] at ha'
      rw [hYbar, Subgroup.mem_map] at hy'
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨y, hy, rfl⟩ := hy'
      have hY : a * y * a⁻¹ * y⁻¹ ∈ Y :=
        Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hYnorm ha) y).mp hy) (Y.inv_mem hy)
      have heq : mk a * mk y * (mk a)⁻¹ * (mk y)⁻¹ = mk (a * y * a⁻¹ * y⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [hYbar, heq]
      exact Subgroup.mem_map_of_mem mk hY
    exact Subgroup.mem_bot.mp (hQYbot ▸ Subgroup.mem_inf.mpr ⟨hin_Q, hin_Y⟩)
  -- conjugation action of `Ȳ` on `Q`.
  have hYbar_norm : Ybar ≤ Subgroup.normalizer Q := by
    intro y _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hQnorm.conj_mem z hz y
    · intro hz
      have h := hQnorm.conj_mem _ hz y⁻¹
      have heq : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
      rwa [heq] at h
  set φ : ↥Ybar →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hYbar_norm) with hφ
  have hφcoe : ∀ (a : ↥Ybar) (g : ↥Q),
      ((φ a) g : G' ⧸ N) = (a : G' ⧸ N) * (g : G' ⧸ N) * (a : G' ⧸ N)⁻¹ := by
    intro a g; rw [hφ]; rfl
  -- `Ā ≤ C_Q(Ȳ)`: `Ā` (inside `Q`) is fixed by `Ȳ`.
  have hAbar_le_fix : Abar.subgroupOf Q ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    have hc := hcommute (g : G' ⧸ N) hg (a : G' ⧸ N) a.2
    have h3 : (g : G' ⧸ N) * (a : G' ⧸ N) * (g : G' ⧸ N)⁻¹ = (a : G' ⧸ N) := mul_inv_eq_one.mp hc
    have h4 : (g : G' ⧸ N) * (a : G' ⧸ N) = (a : G' ⧸ N) * (g : G' ⧸ N) := by
      calc (g : G' ⧸ N) * (a : G' ⧸ N)
          = ((g : G' ⧸ N) * (a : G' ⧸ N) * (g : G' ⧸ N)⁻¹) * (g : G' ⧸ N) := by group
        _ = (a : G' ⧸ N) * (g : G' ⧸ N) := by rw [h3]
    calc (a : G' ⧸ N) * (g : G' ⧸ N) * (a : G' ⧸ N)⁻¹
        = (g : G' ⧸ N) * (a : G' ⧸ N) * (a : G' ⧸ N)⁻¹ := by rw [← h4]
      _ = (g : G' ⧸ N) := by group
  -- `C_Q(C_Q(Ȳ)) ⊆ C_Q(Ȳ)` for Proposition 1.10, using step 6.
  have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
      ≤ Subgroup.fixedPointsOfMulAut φ := by
    refine le_trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAbar_le_fix)) ?_
    refine le_trans ?_ hAbar_le_fix
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    refine mem_map_mk'_of_mem_oPiCore_quotient_of_commute P hAP hCPA (c := (c : G' ⧸ N)) c.2 ?_
    intro a ha
    have hmkaAbar : mk a ∈ Abar := by rw [hAbar]; exact Subgroup.mem_map_of_mem mk ha
    have hmkaQ : mk a ∈ Q := hAbar_le_Q hmkaAbar
    have hmem : (⟨mk a, hmkaQ⟩ : ↥Q) ∈ Abar.subgroupOf Q := by
      rw [Subgroup.mem_subgroupOf]; exact hmkaAbar
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨mk a, hmkaQ⟩ hmem)
  have : Group.IsNilpotent ↥Q := hQ_pg.isNilpotent
  have hcop : Nat.Coprime (Nat.card ↥Ybar) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQ_pg.exists_card_eq
    rw [hn]; exact hYbar_cop.pow_right n
  have htrivφ := OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥Ybar) (G := ↥Q) (φ := φ) hcop hCC
  -- `Ȳ` centralizes `Q`, so `Ȳ ≤ C_X̄(Q) ≤ Q` (Prop 1.15(a)), hence `Ȳ ≤ Q ⊓ Ȳ = ⊥`.
  have hYbar_cent : Ybar ≤ Subgroup.centralizer (Q : Set (G' ⧸ N)) := by
    intro yb hyb
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := htrivφ ⟨yb, hyb⟩ ⟨q, hq⟩
    have hco := congrArg Subtype.val h
    rw [hφcoe] at hco
    have : yb * q * yb⁻¹ = q := hco
    calc q * yb = (yb * q * yb⁻¹) * yb := by rw [this]
      _ = yb * q := by group
  have h115a : Subgroup.centralizer (Q : Set (G' ⧸ N)) ≤ Q := by
    have hbot : Ch03.oPiCore ({q | q ∉ ({p} : Set ℕ)}) (G' ⧸ N) = ⊥ := by
      have := Ch03.oPiCore_quotient_self_eq_bot (G := G') ({p} : Set ℕ)ᶜ
      exact this
    have := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G' ⧸ N) hbot
    rw [← hQ] at this
    exact this
  have hYbar_le_Q : Ybar ≤ Q := le_trans hYbar_cent h115a
  have hYbar_bot : Ybar = ⊥ := le_bot_iff.mp (hQYbot ▸ le_inf hYbar_le_Q le_rfl)
  -- `Y.map mk = ⊥` ⟹ `Y ≤ ker mk = N`.
  have hYmap_bot : Y.map mk = ⊥ := by rw [← hYbar]; exact hYbar_bot
  rw [Subgroup.map_eq_bot_iff, hker] at hYmap_bot
  exact hYmap_bot

/-- **Per-`b` bridge for Prop 7.5's general case**: if `W ≤ X` lies in `O_{p'}(C_G(b))` for a
`p`-element `b ∈ X`, then `W ≤ O_{p'}(X)`. Combines `le_opiCoreInG_of_normal_of_isPiSubgroup`
(`O_{p'}(C_G(b)) ⊓ C_X(b) ≤ O_{p'}(C_X(b))`) with the relativized Proposition 1.15(b)
(`O_{p'}(C_X(b)) ≤ O_{p'}(X)`). -/
private theorem le_opiCoreInG_of_le_opiCoreInG_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hXsolv : Group.IsSolvable ↥X) {b : G} (hbp : IsPGroup p (Subgroup.zpowers b))
    (hbX : b ∈ X) {W : Subgroup G} (hWX : W ≤ X)
    (hW_le : W ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G))) :
    W ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set H := C ⊓ X with hH
  have hW_cent : W ≤ C := hW_le.trans (opiCoreInG_le _ _)
  have hWH : W ≤ H := le_inf hW_cent hWX
  -- `O_{p'}(C) ⊓ H ≤ O_{p'}(H)` via the normal-`p'`-subgroup bridge.
  have hstep : opiCoreInG ({p} : Set ℕ)ᶜ C ⊓ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
    refine le_opiCoreInG_of_normal_of_isPiSubgroup inf_le_right ?_ ?_
    · constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgC : (g : G) ∈ Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ C) :=
        le_normalizer_opiCoreInG _ _ (Subgroup.mem_inf.mp g.2).1
      refine ⟨(Subgroup.mem_normalizer_iff.mp hgC _).mp hn.1, ?_⟩
      exact H.mul_mem (H.mul_mem g.2 hn.2) (H.inv_mem g.2)
    · intro r hr
      refine isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ C r ?_
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩
  -- `O_{p'}(H) = O_{p'}(C_X(b)) ≤ O_{p'}(X)` via the relativized Proposition 1.15(b).
  have hrel : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
    have heqcent : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = C := by
      rw [hC]
      refine le_antisymm (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr (Subgroup.mem_zpowers b)))) ?_
      · intro g hg
        rw [Subgroup.mem_centralizer_iff] at hg ⊢
        intro z hz
        rw [SetLike.mem_coe] at hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hcom : Commute b g := hg b (Set.mem_singleton b)
        exact hcom.zpow_left k
    have hrel := opiCoreInG_centralizer_inf_le_opiCoreInG hXsolv (Subgroup.zpowers_le.mpr hbX) hbp
    rwa [heqcent, ← hH] at hrel
  exact (le_inf hW_le hWH).trans (hstep.trans hrel)

/-- **General case of BG Proposition 7.5** (mmd L2299-2307): given a noncyclic abelian `B ≤ A`
of `p`-elements that normalizes the `A`-invariant `p'`-subgroup `Y ≤ X` coprimely, if each
`C_Y(b) ⊆ O_{p'}(C_G(b))` (`b ∈ B^#`, the special-case input `hspec`), then `Y ≤ O_{p'}(X)`.
Proof: Proposition 1.16 gives `Y = ⟨C_Y(b) | b ∈ B^#⟩` (`nontrivialActionFixedByClosure = ⊤`),
and `le_opiCoreInG_of_le_opiCoreInG_centralizer` sends each `C_Y(b)` into `O_{p'}(X)`. -/
private theorem coreClaimGeneral
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hXsolv : Group.IsSolvable ↥X) {A : Subgroup G} (hAX : A ≤ X)
    {B : Subgroup G} (hBA : B ≤ A) [IsMulCommutative ↥B] (hB_nc : ¬ IsCyclic ↥B)
    (hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b))
    {Y : Subgroup G} (hYX : Y ≤ X) (hAY : A ≤ Subgroup.normalizer Y)
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y))
    (hspec : ∀ b ∈ B, b ≠ (1 : G) →
      Y ⊓ Subgroup.centralizer ({b} : Set G)
        ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G))) :
    Y ≤ opiCoreInG ({p} : Set ℕ)ᶜ X := by
  classical
  have hBY : B ≤ Subgroup.normalizer Y := hBA.trans hAY
  have hY_inv : Ch03.IsAInvariant (conjAction B) Y := isAInvariant_conjAction_iff.mpr hBY
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hY_inv.restrict hcop hB_nc
  have hle : nontrivialActionFixedByClosure hY_inv.restrict
      ≤ (opiCoreInG ({p} : Set ℕ)ᶜ X ⊓ Y).subgroupOf Y := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb_ne
    rw [actionFixedBy_conjAction_restrict]
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    have hb_ne' : (b : G) ≠ 1 := fun h => hb_ne (Subtype.ext h)
    have hbX : (b : G) ∈ X := hAX (hBA b.2)
    have hW_le_X : Y ⊓ Subgroup.centralizer ({(b : G)} : Set G) ≤ opiCoreInG ({p} : Set ℕ)ᶜ X :=
      le_opiCoreInG_of_le_opiCoreInG_centralizer hXsolv (hBp (b : G) b.2) hbX
        (le_trans inf_le_left hYX) (hspec (b : G) b.2 hb_ne')
    exact Subgroup.mem_inf.mpr ⟨hW_le_X hz, (Subgroup.mem_inf.mp hz).1⟩
  rw [htop, top_le_iff, Subgroup.subgroupOf_eq_top] at hle
  exact le_trans hle inf_le_left

/-- **Sylow-of-subgroup**: a Sylow `p`-subgroup `P` of `G` contained in `K ≤ G` restricts to a
Sylow `p`-subgroup of `↥K` (with carrier `P.subgroupOf K`): `P.subgroupOf K` is a `p`-group, and
`p ∤ (P.subgroupOf K).index` since it divides `P.index` (`relIndex_dvd_index_of_le`). Used for
`b ∈ Z(P)`: `P` is a Sylow of `C_G(b)`. -/
private theorem sylow_subgroupOf_of_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (P : Sylow p G) {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ∃ Q : Sylow p ↥K, (Q : Subgroup ↥K) = (P : Subgroup G).subgroupOf K := by
  have hpg : IsPGroup p ↥((P : Subgroup G).subgroupOf K) := by
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]; exact hn)
  have hidx : ¬ p ∣ ((P : Subgroup G).subgroupOf K).index := fun h =>
    P.not_dvd_index (dvd_trans h (Subgroup.relIndex_dvd_index_of_le hPK))
  exact ⟨hpg.toSylow hidx, hpg.toSylow_coe hidx⟩

/-- **`hspec` for `b ∈ Z(P)`** (special case 1, mmd L2275-2285 packaged for the general case): if
`b ∈ Z(P)` (so `P ≤ C_G(b)`), then any `A`-invariant `p'`-subgroup `W` of `C_G(b)` lies in
`O_{p'}(C_G(b))`. Proof: `P` is a Sylow `p`-subgroup of `K := C_G(b)` (`sylow_subgroupOf_of_le`),
`A.subgroupOf K` is `SCN` in it (transported from `A ⊴ P`, `C_P(A) ⊆ A`), so `specialCase` at `↥K`
gives `W.subgroupOf K ≤ O_{p'}(↥K)`, which maps back to `W ≤ O_{p'}(C_G(b))`. -/
private theorem le_opiCoreInG_centralizer_of_mem_centralizer_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (hp2 : p ≠ 2) (P : Sylow p G) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G))
    [hAcomm : IsMulCommutative A] (hAnormP : (P : Subgroup G) ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A)
    {b : G} (hb_ne : b ≠ 1) (hbP : (P : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G))
    {W : Subgroup G} (hWcent : W ≤ Subgroup.centralizer ({b} : Set G))
    (hAW : A ≤ Subgroup.normalizer W) (hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W) :
    W ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G)) := by
  classical
  set K : Subgroup G := Subgroup.centralizer ({b} : Set G) with hK
  have hKsolv : Group.IsSolvable ↥K :=
    hG.isSolvable_of_lt_top K (by rw [hK]; exact centralizer_singleton_lt_top hG hb_ne)
  have hodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hAK : A ≤ K := le_trans hAP (by rw [hK]; exact hbP)
  have hWK : W ≤ K := by rw [hK]; exact hWcent
  obtain ⟨Q, hQeq⟩ := sylow_subgroupOf_of_le P hbP
  -- `A.subgroupOf K` is abelian, contained in `Q`, normalized by `Q`, with `C_Q(A) ⊆ A`.
  have : IsMulCommutative ↥(A.subgroupOf K) := by
    refine ⟨⟨fun a c => Subtype.ext (Subtype.ext ?_)⟩⟩
    have := (isMulCommutative_iff_of_setLike.mp hAcomm)
    exact this _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp c.2)
  have hAQ : A.subgroupOf K ≤ (Q : Subgroup ↥K) := by
    rw [hQeq]; intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢; exact hAP hx
  have hQnorm : (Q : Subgroup ↥K) ≤ Subgroup.normalizer (A.subgroupOf K) := by
    rw [hQeq]; intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    have hqP : (q : G) ∈ Subgroup.normalizer A := hAnormP hq
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hqP (z : G)
  have hCQA : Subgroup.centralizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊓ (Q : Subgroup ↥K)
      ≤ A.subgroupOf K := by
    rw [hQeq]
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    have hqP : (q : G) ∈ (P : Subgroup G) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hq).2
    have hqC : (q : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haK : a ∈ K := hAK ha
      have hmem : (⟨a, haK⟩ : ↥K) ∈ A.subgroupOf K := by rw [Subgroup.mem_subgroupOf]; exact ha
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).1 ⟨a, haK⟩ hmem
      exact congrArg Subtype.val this
    exact hCPA (Subgroup.mem_inf.mpr ⟨hqC, hqP⟩)
  -- `W.subgroupOf K` is `A`-invariant and a `p'`-subgroup.
  have hWnorm : A.subgroupOf K ≤ Subgroup.normalizer (W.subgroupOf K) := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    have haW : (a : G) ∈ Subgroup.normalizer W := hAW ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp haW (z : G)
  have hWpi' : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (W.subgroupOf K) := by
    intro r hr
    refine hWpi r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at hr
  -- specialCase at `↥K`, then transport back.
  have hW' := specialCase hp2 hodd Q hAQ hQnorm hCQA hWnorm hWpi'
  rw [hK]
  calc W = (W.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hWK).symm
    _ ≤ (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥K).map K.subtype := Subgroup.map_mono hW'
    _ = opiCoreInG ({p} : Set ℕ)ᶜ K := rfl

/-- **SCN unpacked into ambient form**: if `A.subgroupOf P` is `SCN` in `↥P` (with `A ≤ P`), then
`A` is abelian, `P ≤ N_G(A)`, and `C_G(A) ⊓ P ≤ A` — exactly the hypotheses `specialCase` /
`le_opiCoreInG_centralizer_of_mem_centralizer_sylow` require. Transports normality/self-centralizing
from `↥P` to `G`. -/
private theorem scn_ambient {p : ℕ} {G : Type*} [Group G] {P : Sylow p G} {A : Subgroup G}
    (hAP : A ≤ (P : Subgroup G)) (h : IsSCN (A.subgroupOf (P : Subgroup G))) :
    IsMulCommutative A ∧ (P : Subgroup G) ≤ Subgroup.normalizer A ∧
      Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A := by
  have hAcomm : IsMulCommutative A :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp h.isMulCommutative
        (⟨a, hAP ha⟩ : ↥(P : Subgroup G)) (Subgroup.mem_subgroupOf.mpr ha)
        ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  refine ⟨hAcomm, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have := h.isNormal.conj_mem ⟨a, hAP ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨g, hg⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    · intro ha
      have hga : g * a * g⁻¹ ∈ A := ha
      have := h.isNormal.conj_mem ⟨g * a * g⁻¹, hAP hga⟩ (Subgroup.mem_subgroupOf.mpr hga)
        ⟨g, hg⟩⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      have heq : ((⟨g, hg⟩⁻¹ * ⟨g * a * g⁻¹, hAP hga⟩ * (⟨g, hg⟩⁻¹)⁻¹ : ↥(P : Subgroup G)) : G)
          = a := by simp [Subgroup.coe_mul]; group
      rwa [heq] at this
  · intro x hx
    have hmem : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : ↥(P : Subgroup G))
        ∈ Subgroup.centralizer ((A.subgroupOf (P : Subgroup G) : Subgroup ↥(P : Subgroup G))
          : Set ↥(P : Subgroup G)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 (a : G) ha)
    rw [h.selfCentralizing] at hmem
    rwa [Subgroup.mem_subgroupOf] at hmem

/-- **Coprime decomposition reduction** (for special case 2): if `z` normalizes `W` coprimely and
both `C_W(z) = W ⊓ C_G(z)` and `⁅⟨z⟩, W⁆` lie in `L`, then `W ≤ L`. From the coprime decomposition
`W = C_W(z)·⁅W,z⁆` (`fixedPoints_sup_actionCommutator_eq_top`): the `fixedPoints` summand is
`C_W(z)` and the `actionCommutator` summand is `⁅⟨z⟩, W⁆`, both `≤ L`. -/
private theorem le_of_centralizer_inf_le_of_commutator_le {G : Type*} [Group G] [Finite G]
    {z : G} {W : Subgroup G} (hzW : z ∈ Subgroup.normalizer W)
    (hcop : Nat.Coprime (orderOf z) (Nat.card ↥W)) {L : Subgroup G}
    (hcent : W ⊓ Subgroup.centralizer ({z} : Set G) ≤ L)
    (hcomm : ⁅Subgroup.zpowers z, W⁆ ≤ L) :
    W ≤ L := by
  classical
  have hzpW : Subgroup.zpowers z ≤ Subgroup.normalizer W := Subgroup.zpowers_le.mpr hzW
  have hW_inv : Ch03.IsAInvariant (conjAction (Subgroup.zpowers z)) W :=
    isAInvariant_conjAction_iff.mpr hzpW
  have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers z)) (Nat.card ↥W) := by
    rw [Nat.card_zpowers]; exact hcop
  have htop := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
    (φ := hW_inv.restrict) hCop' (Or.inl inferInstance)
  rw [← Subgroup.subgroupOf_eq_top, eq_top_iff, ← htop, sup_le_iff]
  refine ⟨?_, ?_⟩
  · -- `fixedPoints ≤ L.subgroupOf W`: a fixed point centralizes `z`.
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hcent (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hval := congrArg Subtype.val
      (Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨z, Subgroup.mem_zpowers z⟩)
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `actionCommutator ≤ L.subgroupOf W`: each generator is a `⁅z, w⁆`.
    rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a g
    rw [Subgroup.mem_subgroupOf]
    have hgen : (((hW_inv.restrict a) g * g⁻¹ : ↥W) : G)
        = (a : G) * (g : G) * (a : G)⁻¹ * (g : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Ch03.IsAInvariant.restrict_apply_val]
      simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [hgen]
    exact hcomm (Subgroup.commutator_mem_commutator a.2 g.2)

/-- **Commutator part of special case 2**: if `z ∈ O_{p',p}(H)` normalizes a `p'`-subgroup `W`,
then `⁅⟨z⟩, W⁆ ≤ O_{p'}(H)`. Proof: `⁅⟨z⟩,W⁆ ≤ W` (z normalizes W) and `≤ O_{p',p}(H)`
(z ∈ O_{p',p} ⊴ H), so `⁅⟨z⟩,W⁆ ≤ W ⊓ O_{p',p}(H)`, a `p'`-subgroup whose image in
`H/O_{p'}(H) = O_p(quotient)` (via `oPiPrimePiCore_map_mk'_eq`) is a `p'`-subgroup of a `p`-group,
hence trivial — so it lies in `ker = O_{p'}(H)`. -/
private theorem commutator_zpowers_le_oPiCore {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] {z : H} (hz : z ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H)
    {W : Subgroup H} (hzW : z ∈ Subgroup.normalizer W)
    (hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W) :
    ⁅Subgroup.zpowers z, W⁆ ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ H := by
  have hOnorm : (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).Normal := inferInstance
  have hsubW : ⁅Subgroup.zpowers z, W⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : a * b * a⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.zpowers_le.mpr hzW) ha) b).mp hb
    simpa [commutatorElement_def, mul_assoc] using W.mul_mem hab (W.inv_mem hb)
  have hsubO : ⁅Subgroup.zpowers z, W⁆ ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) H := by
    rw [Subgroup.commutator_le]
    intro a ha b _
    have haO : a ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).zpow_mem hz k
    have hconj : b * a⁻¹ * b⁻¹ ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) H :=
      hOnorm.conj_mem a⁻¹ ((Ch03.oPiPrimePiCore ({p} : Set ℕ) H).inv_mem haO) b
    simpa [commutatorElement_def, mul_assoc] using
      (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).mul_mem haO hconj
  -- `⁅⟨z⟩,W⁆ ≤ W ⊓ O_{p',p}(H)`; its mk'-image is a `p'`-subgroup of the `p`-group `O_p(H/O_{p'})`.
  refine (le_inf hsubW hsubO).trans ?_
  have hbridge : (Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
        (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))
      = Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H) :=
    oPiPrimePiCore_map_mk'_eq ({p} : Set ℕ)
  have hle : (W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
        (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))
      ≤ Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H) :=
    hbridge ▸ Subgroup.map_mono inf_le_right
  have hT_pg : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) (H ⧸ Ch03.oPiCore ({p} : Set ℕ)ᶜ H)) := by
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p _
  have hM_cop : Nat.Coprime (Nat.card ↥((W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
      (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H)))) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      have hdvd : Nat.card ↥((W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
            (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H))) ∣ Nat.card ↥W :=
        (Subgroup.card_map_dvd _ _).trans (Subgroup.card_dvd_of_le inf_le_left)
      exact hWpi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hbot : (W ⊓ Ch03.oPiPrimePiCore ({p} : Set ℕ) H).map
      (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ)ᶜ H)) = ⊥ := by
    have hinf := OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hT_pg hM_cop
    rwa [inf_eq_right.mpr hle] at hinf
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

/-- **Orbit-stabilizer crux for Proposition 7.5, special case 2**: if `b ≠ 1` lies in a subgroup
`B ≤ P` of order `p²` invariant under `P`-conjugation (`B ⊴ P`), then `|P : C_P(b)| ≤ p`, i.e.
`|P| ≤ p · |C_P(b)|`. The `P`-conjugacy orbit of `b` lies in `B ∖ {1}` (so `< p²` elements) and its
size divides `|P|`, hence is a power of `p` below `p²`, so `≤ p`; orbit-stabilizer
(`|P| = |orbit| · |stabilizer|`, `stabilizer = C_P(b)`) converts this into the index bound. -/
private theorem card_le_prime_mul_card_centralizer_inf {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] {P : Sylow p G} {B : Subgroup G} (hBP : B ≤ (P : Subgroup G))
    (hBcard : Nat.card ↥B = p ^ 2) (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {b : G} (hb_ne : b ≠ 1) (hbP : b ∈ (P : Subgroup G)) (hbB : b ∈ B) :
    Nat.card ↥(P : Subgroup G)
      ≤ p * Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) := by
  classical
  set R : Type _ := ↥(P : Subgroup G) with hRdef
  set bhat : R := ⟨b, hbP⟩ with hbhat
  set Bsub : Subgroup R := B.subgroupOf (P : Subgroup G) with hBsub
  have : Finite (ConjAct R) := inferInstanceAs (Finite R)
  have hBsub_card : Nat.card ↥Bsub = p ^ 2 := by
    rw [hBsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hBcard]
  have horb_sub : MulAction.orbit (ConjAct R) bhat ⊆ (Bsub : Set R) := by
    rintro _ ⟨c, rfl⟩
    change (c • bhat) ∈ (Bsub : Set R)
    rw [SetLike.mem_coe, hBsub, Subgroup.mem_subgroupOf, ConjAct.smul_def]
    change (ConjAct.ofConjAct c : R).val * b * ((ConjAct.ofConjAct c : R).val)⁻¹ ∈ B
    exact hBnorm _ (ConjAct.ofConjAct c).2 b hbB
  have hone_not : (1 : R) ∉ MulAction.orbit (ConjAct R) bhat := by
    rintro ⟨c, hc⟩
    rw [show (fun m : ConjAct R => m • bhat) c = c • bhat from rfl, ConjAct.smul_def] at hc
    have hb1 : bhat = 1 := by
      have h2 : ConjAct.ofConjAct c * bhat = ConjAct.ofConjAct c * 1 := by
        rw [mul_one]; exact mul_inv_eq_one.mp hc
      exact mul_left_cancel h2
    exact hb_ne (congrArg (Subtype.val : R → G) hb1)
  have hBsub_ncard : (Bsub : Set R).ncard = p ^ 2 := by
    rw [← Nat.card_coe_set_eq]; exact hBsub_card
  have hlt : Nat.card (MulAction.orbit (ConjAct R) bhat) < p ^ 2 := by
    calc Nat.card (MulAction.orbit (ConjAct R) bhat)
        = (MulAction.orbit (ConjAct R) bhat).ncard := Nat.card_coe_set_eq _
      _ < (Bsub : Set R).ncard :=
          Set.ncard_lt_ncard ⟨horb_sub, fun h => hone_not (h Bsub.one_mem)⟩ (Set.toFinite _)
      _ = p ^ 2 := hBsub_ncard
  have hdvd : Nat.card (MulAction.orbit (ConjAct R) bhat) ∣ Nat.card R := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct R) bhat),
      Nat.card_congr (ConjAct.toConjAct (G := R)).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  rw [← hRdef] at hk
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hk ▸ hdvd)
  have horb_le : Nat.card (MulAction.orbit (ConjAct R) bhat) ≤ p := by
    rw [hj] at hlt ⊢
    have hj1 : j ≤ 1 := by
      by_contra h
      push Not at h
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le h))
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hj1
      _ = p := pow_one p
  -- Orbit-stabilizer: `|P| = |orbit| · |stab|`, with `stab = C_R(bhat)` injecting into
  -- `C_G(b) ⊓ P`.
  set stab : Subgroup (ConjAct R) := MulAction.stabilizer (ConjAct R) bhat with hstabdef
  have hPeq : Nat.card R = Nat.card (MulAction.orbit (ConjAct R) bhat) * Nat.card ↥stab := by
    have hidx : stab.index = Nat.card (MulAction.orbit (ConjAct R) bhat) := by
      rw [hstabdef, MulAction.index_stabilizer, Nat.card_coe_set_eq]
    have hmul : stab.index * Nat.card ↥stab = Nat.card (ConjAct R) := Subgroup.index_mul_card stab
    rw [hidx] at hmul
    rw [Nat.card_congr (ConjAct.toConjAct (G := R)).toEquiv]
    exact hmul.symm
  -- `|stab| ≤ |C_G(b) ⊓ P|` via `c ↦ (ofConjAct c).val`.
  have hmem : ∀ c : ↥stab, ((ConjAct.ofConjAct (c : ConjAct R) : R) : G)
      ∈ Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G) := by
    rintro ⟨c, hc⟩
    rw [hstabdef, MulAction.mem_stabilizer_iff, ConjAct.smul_def] at hc
    refine Subgroup.mem_inf.mpr ⟨?_, (ConjAct.ofConjAct c : R).2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
    have hcomm : (ConjAct.ofConjAct c : R) * bhat = bhat * (ConjAct.ofConjAct c : R) := by
      rw [mul_inv_eq_iff_eq_mul] at hc; exact hc
    have hval : ((ConjAct.ofConjAct c : R) : G) * b = b * ((ConjAct.ofConjAct c : R) : G) := by
      have h := congrArg (Subtype.val : R → G) hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hbhat] at h
      exact h
    exact hval.symm
  have hstab_le : Nat.card ↥stab
      ≤ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) ?_
    intro c₁ c₂ h
    have hv : ((ConjAct.ofConjAct (c₁ : ConjAct R) : R) : G)
        = ((ConjAct.ofConjAct (c₂ : ConjAct R) : R) : G) := by
      have := Subtype.ext_iff.mp h
      simpa using this
    exact Subtype.ext (ConjAct.ofConjAct.injective (Subtype.ext hv))
  calc Nat.card ↥(P : Subgroup G) = Nat.card R := rfl
    _ = Nat.card (MulAction.orbit (ConjAct R) bhat) * Nat.card ↥stab := hPeq
    _ ≤ p * Nat.card ↥stab := Nat.mul_le_mul_right _ horb_le
    _ ≤ p * Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G)) :=
        Nat.mul_le_mul_left _ hstab_le

/-- For a nontrivial `p`-group `A`, `π(A) = {p}` (so `(π(A))ᶜ = {p}ᶜ`). Used to align
`hInvariant`/`opiCoreInG (primesOf A)ᶜ` with the single-prime lemmas of §1. -/
private theorem primesOf_eq_singleton [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAp : IsPGroup p A) (hAne : A ≠ ⊥) : primesOf A = ({p} : Set ℕ) := by
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hAne (Subgroup.card_eq_one.mp hn)
  ext q
  simp only [primesOf, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- **`z ∈ O_{p',p}(C_G(b))` for special case 2** (mmd L2289-2293): given `B ⊴ P` of order `p²`
containing `b ≠ 1`, and `z` central in `P` with `z ∈ C_G(b)`, the element `z` lies in
`O_{p',p}(C_G(b))`. Proof: `P₁ = C_P(b)` extends to a Sylow `P₂` of `C_G(b)`; the orbit bound
`card_le_prime_mul_card_centralizer_inf` plus `|P₂| ≤ |P|` give `|P₂ : P₁| ≤ p`, so `P₁ ⊴ P₂`. Then
`Z(P₁) = C(P₁) ⊓ P₁` is abelian, normal in `P₂`, contains `z`, so Theorem 6.1 (`thmA4b`) places it
in `O_{p',p}(C_G(b))`. -/
private theorem mem_oPiPrimePiCore_centralizer_of_central {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (hp2 : p ≠ 2) (P : Sylow p G)
    {B : Subgroup G} (hBP : B ≤ (P : Subgroup G)) (hBcard : Nat.card ↥B = p ^ 2)
    (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {z : G} (hzP : z ∈ (P : Subgroup G))
    (hz_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    {b : G} (hbB : b ∈ B) (hb_ne : b ≠ 1) (hzCb : z ∈ Subgroup.centralizer ({b} : Set G)) :
    (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G)))
      ∈ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥(Subgroup.centralizer ({b} : Set G)) := by
  classical
  set K : Subgroup G := Subgroup.centralizer ({b} : Set G) with hK
  have hKsolv : Group.IsSolvable ↥K :=
    hG.isSolvable_of_lt_top K (by rw [hK]; exact centralizer_singleton_lt_top hG hb_ne)
  have hodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hbP : b ∈ (P : Subgroup G) := hBP hbB
  -- `P₁ = C_P(b)` inside `K`, extended to a Sylow `P₂` of `K`.
  set P₁ : Subgroup ↥K := (P : Subgroup G).subgroupOf K with hP₁def
  have hP₁pg : IsPGroup p ↥P₁ := P.isPGroup'.comap_subtype
  obtain ⟨P₂, hP₁₂⟩ := hP₁pg.exists_le_sylow
  -- `|P₂| ≤ |P|`.
  have hcardP₂_le : Nat.card ↥(P₂ : Subgroup ↥K) ≤ Nat.card ↥(P : Subgroup G) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp P₂.isPGroup'
    have hdvdG : Nat.card ↥(P₂ : Subgroup ↥K) ∣ Nat.card G := by
      have h1 : Nat.card ↥((P₂ : Subgroup ↥K).map K.subtype) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      have h2 : Nat.card ↥((P₂ : Subgroup ↥K).map K.subtype) = Nat.card ↥(P₂ : Subgroup ↥K) :=
        Subgroup.card_map_of_injective Subtype.coe_injective
      rwa [h2] at h1
    have hdvdP : Nat.card ↥(P₂ : Subgroup ↥K) ∣ Nat.card ↥(P : Subgroup G) := by
      rw [ha] at hdvdG ⊢
      exact P.pow_dvd_card_of_pow_dvd_card hdvdG
    exact Nat.le_of_dvd Nat.card_pos hdvdP
  -- `|P| ≤ p · |P₁|` (orbit bound), via `|P₁| = |C_G(b) ⊓ P|`.
  have hcardP₁ : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ (P : Subgroup G))
      = Nat.card ↥P₁ := by
    rw [hP₁def, hK, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv, inf_comm]
  have hbound : Nat.card ↥(P : Subgroup G) ≤ p * Nat.card ↥P₁ := by
    rw [← hcardP₁]
    exact card_le_prime_mul_card_centralizer_inf hBP hBcard hBnorm hb_ne hbP hbB
  -- `|P₂ : P₁| ≤ p`.
  have hidx_le : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ≤ p := by
    have hmul : Nat.card ↥(P₁.subgroupOf (P₂ : Subgroup ↥K))
        * (P₁.subgroupOf (P₂ : Subgroup ↥K)).index = Nat.card ↥(P₂ : Subgroup ↥K) :=
      Subgroup.card_mul_index _
    have hsub : Nat.card ↥(P₁.subgroupOf (P₂ : Subgroup ↥K)) = Nat.card ↥P₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁₂).toEquiv
    rw [hsub] at hmul
    have hpos : 0 < Nat.card ↥P₁ := Nat.card_pos
    have hle : Nat.card ↥P₁ * (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ≤ Nat.card ↥P₁ * p := by
      rw [hmul, mul_comm (Nat.card ↥P₁) p]
      exact le_trans hcardP₂_le hbound
    exact Nat.le_of_mul_le_mul_left hle hpos
  -- `P₁ ⊴ P₂`.
  have hP₁₂normal : (P₁.subgroupOf (P₂ : Subgroup ↥K)).Normal := by
    obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp P₂.isPGroup'
    have hidx_dvd : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ∣ p ^ c :=
      hc ▸ Subgroup.index_dvd_card _
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hidx_dvd
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, pow_zero] at hj
      exact Subgroup.normal_of_index_eq_one hj
    · have hj1 : j = 1 := by
        by_contra h
        have hj2 : 2 ≤ j := by omega
        have hple : p ^ 2 ≤ p :=
          le_trans (Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hj2) (hj ▸ hidx_le)
        nlinarith [(Fact.out : p.Prime).two_le, hple]
      have hc_ne : c ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hc
        have hdvd1 : (P₁.subgroupOf (P₂ : Subgroup ↥K)).index ∣ 1 := hc ▸ Subgroup.index_dvd_card _
        rw [hj, hj1, pow_one, Nat.dvd_one] at hdvd1
        exact (Fact.out : p.Prime).one_lt.ne' hdvd1
      have hmin : (Nat.card ↥(P₂ : Subgroup ↥K)).minFac = p := by
        rw [hc, (Fact.out : p.Prime).pow_minFac hc_ne]
      refine Subgroup.normal_of_index_eq_minFac_card ?_
      rw [hj, hj1, pow_one, hmin]
  have hP₂_norm_P₁ : (P₂ : Subgroup ↥K) ≤ Subgroup.normalizer P₁ :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP₁₂).mp hP₁₂normal
  -- `A' = Z(P₁) = C(P₁) ⊓ P₁`: abelian, ≤ P₂, normal in P₂, contains `z`.
  set A' : Subgroup ↥K := Subgroup.centralizer (P₁ : Set ↥K) ⊓ P₁ with hA'def
  have hA'comm : IsMulCommutative ↥A' :=
    IsMulCommutative.of_setLike_mul_comm fun a ha c hc =>
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).1 c
        (SetLike.mem_coe.mpr (Subgroup.mem_inf.mp hc).2)).symm
  have hA'_le_P₂ : A' ≤ (P₂ : Subgroup ↥K) := le_trans inf_le_right hP₁₂
  have hconj_pres : ∀ g ∈ (P₂ : Subgroup ↥K), ∀ x ∈ A', g * x * g⁻¹ ∈ A' := by
    intro g hg x hx
    obtain ⟨hxc, hxP₁⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwP₁ : w ∈ P₁ := hw
      have hg'norm : g⁻¹ ∈ Subgroup.normalizer P₁ := inv_mem (hP₂_norm_P₁ hg)
      have hv : g⁻¹ * w * g ∈ P₁ := by
        have := (Subgroup.mem_normalizer_iff.mp hg'norm w).mp hwP₁
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc (g⁻¹ * w * g) (SetLike.mem_coe.mpr hv)
      calc w * (g * x * g⁻¹)
          = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * w := by group
    · exact (Subgroup.mem_normalizer_iff.mp (hP₂_norm_P₁ hg) x).mp hxP₁
  have hA'_norm : (P₂ : Subgroup ↥K) ≤ Subgroup.normalizer A' := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hconj_pres g hg x hx
    · intro hx
      have h2 := hconj_pres g⁻¹ ((P₂ : Subgroup ↥K).inv_mem hg) _ hx
      have heq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [heq] at h2
  have hzK : z ∈ K := by rw [hK]; exact hzCb
  have hzA' : (⟨z, hzK⟩ : ↥K) ∈ A' := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwP₁ : w ∈ P₁ := hw
      rw [hP₁def, Subgroup.mem_subgroupOf] at hwP₁
      have hcomm : ((w : ↥K) : G) * z = z * ((w : ↥K) : G) :=
        (Subgroup.mem_centralizer_iff.mp (hz_cent hwP₁) z rfl).symm
      exact Subtype.ext hcomm
    · rw [hP₁def, Subgroup.mem_subgroupOf]; exact hzP
  -- Theorem 6.1: `Z(P₁) ⊆ O_{p',p}(C_G(b))`.
  have hThm61 : A' ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥K :=
    OddOrder.BG.AppA.thmA4b hp2 hKsolv hodd P₂ hA'_le_P₂ hA'_norm
  exact hThm61 hzA'

/-- **`hspec` for special case 2** (mmd L2287-2297): for `b ∈ B^#`, with a `p`-central element `z`
of order `p`, the `A`-invariant `p'`-subgroup `W = Y ⊓ C_G(b)` lies in `O_{p'}(C_G(b))`. The coprime
decomposition `W = C_W(z)·⁅⟨z⟩,W⁆` (`le_of_centralizer_inf_le_of_commutator_le`) splits the goal:
`C_W(z)` lands in `O_{p'}(C_G(b))` by special case 1 at `z` plus the per-`b` bridge, and `⁅⟨z⟩,W⁆`
by `commutator_zpowers_le_oPiCore` (its `z ∈ O_{p',p}(C_G(b))` input is the crux above). -/
private theorem centralizer_inf_le_opiCoreInG_of_central
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    (hp2 : p ≠ 2) (P : Sylow p G) {A : Subgroup G} (hAcomm : IsMulCommutative A)
    (hAP : A ≤ (P : Subgroup G)) (hAnormP : (P : Subgroup G) ≤ Subgroup.normalizer A)
    (hCPA : Subgroup.centralizer (A : Set G) ⊓ (P : Subgroup G) ≤ A)
    {B : Subgroup G} (hBA : B ≤ A) (hBP : B ≤ (P : Subgroup G)) (hBcard : Nat.card ↥B = p ^ 2)
    (hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    {z : G} (hzA : z ∈ A) (hzP : z ∈ (P : Subgroup G))
    (hz_cent : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) (hz_ord : orderOf z = p)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y)
    {b : G} (hbB : b ∈ B) (hb_ne : b ≠ 1) :
    Y ⊓ Subgroup.centralizer ({b} : Set G)
      ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({b} : Set G)) := by
  classical
  have := hAcomm
  set W : Subgroup G := Y ⊓ Subgroup.centralizer ({b} : Set G) with hWdef
  have hWY : W ≤ Y := inf_le_left
  have hWCb : W ≤ Subgroup.centralizer ({b} : Set G) := inf_le_right
  have hbA : b ∈ A := hBA hbB
  have hz_ne : z ≠ 1 := by
    rintro rfl; rw [orderOf_one] at hz_ord; exact (Fact.out : p.Prime).one_lt.ne hz_ord
  have hz_pg : IsPGroup p (Subgroup.zpowers z) := (P.isPGroup').to_le (Subgroup.zpowers_le.mpr hzP)
  -- `z` commutes with `b` (both in abelian `A`).
  have hzCb : z ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨b, hbA⟩ ⟨z, hzA⟩)
  -- `z ∈ N_G(W)`: it normalizes both `Y` (`z ∈ A`) and `C_G(b)` (`z ∈ C_G(b)`).
  have hzNW : z ∈ Subgroup.normalizer W := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hWdef, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (hAY hzA) x,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hzCb) x]
  have hWpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ W := fun q hq =>
    hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hWY) Nat.card_pos.ne' hq)
  refine le_of_centralizer_inf_le_of_commutator_le hzNW ?_ ?_ ?_
  · -- coprimality.
    rw [hz_ord]
    refine (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hdvd => ?_)
    exact hYpi p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hdvd.trans (Subgroup.card_dvd_of_le hWY), Nat.card_pos.ne'⟩) rfl
  · -- `C_W(z) ≤ O_{p'}(C_G(b))`: special case 1 at `z`, then the per-`b` bridge.
    have hCYz : Y ⊓ Subgroup.centralizer ({z} : Set G)
        ≤ opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer ({z} : Set G)) := by
      refine le_opiCoreInG_centralizer_of_mem_centralizer_sylow hG hp2 P hAP hAnormP hCPA hz_ne
        hz_cent inf_le_right ?_ ?_
      · intro a ha
        have haCz : a ∈ Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]; rintro y hy; rw [Set.mem_singleton_iff] at hy; subst y
          exact congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨z, hzA⟩ ⟨a, ha⟩)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hAY ha) x,
          Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer haCz) x]
      · intro q hq
        exact hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left)
          Nat.card_pos.ne' hq)
    have hWz_le : W ⊓ Subgroup.centralizer ({z} : Set G)
        ≤ Y ⊓ Subgroup.centralizer ({z} : Set G) := by
      rw [hWdef]; exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    exact le_opiCoreInG_of_le_opiCoreInG_centralizer
      (hG.isSolvable_of_lt_top _ (centralizer_singleton_lt_top hG hb_ne)) hz_pg hzCb
      (le_trans inf_le_left hWCb) (le_trans hWz_le hCYz)
  · -- `⁅⟨z⟩,W⁆ ≤ O_{p'}(C_G(b))`: `commutator_zpowers_le_oPiCore` in `↥(C_G(b))`, transported back.
    have hzO := mem_oPiPrimePiCore_centralizer_of_central hG hp2 P hBP hBcard hBnorm hzP hz_cent
      hbB hb_ne hzCb
    have hzW_H : (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G)))
        ∈ Subgroup.normalizer (W.subgroupOf (Subgroup.centralizer ({b} : Set G))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hzNW (x : G)
    have hWpi_H : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ
        (W.subgroupOf (Subgroup.centralizer ({b} : Set G))) := by
      intro q hq
      refine hWpi q ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWCb).toEquiv] at hq
    have hcomm_H := commutator_zpowers_le_oPiCore hzO hzW_H hWpi_H
    have hmapeq : (⁅Subgroup.zpowers (⟨z, hzCb⟩ : ↥(Subgroup.centralizer ({b} : Set G))),
          W.subgroupOf (Subgroup.centralizer ({b} : Set G))⁆).map
          (Subgroup.centralizer ({b} : Set G)).subtype = ⁅Subgroup.zpowers z, W⁆ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hWCb]
      rfl
    rw [← hmapeq]
    exact Subgroup.map_mono hcomm_H

/-- **Core claim of BG Proposition 7.5, case (2)** (mmd L2273-2307): for `A ∈ SCN₂(P)`, every
`A`-invariant `p'`-subgroup `Y ≤ X` (of a proper subgroup `X ⊇ A`) lies in `O_{p'}(X)`. Proof:
build `B ∈ E_p²(A)` with `B ⊴ P` (cyclic/noncyclic `Z(P)` split via G 2.6.4), then feed the
special-case inputs (`b ∈ Z(P)` via `le_opiCoreInG_centralizer_of_mem_centralizer_sylow`; general
`b ∈ B^#` via the coprime decomposition) to `coreClaimGeneral`. -/
private theorem coreClaim_scn2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    {P : Sylow p G} (hAP : A ≤ (P : Subgroup G))
    (hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))
    {X : Subgroup G} (hAX : A ≤ X) (hXlt : X < ⊤)
    {Y : Subgroup G} (hYX : Y ≤ X) (hAY : A ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup (primesOf A)ᶜ Y) :
    Y ≤ opiCoreInG (primesOf A)ᶜ X := by
  classical
  -- `A ≠ ⊥` from `pRank (A.subgroupOf P) ≥ 2`, then `π(A) = {p}`.
  have hAne : A ≠ ⊥ := by
    intro hAbot
    obtain ⟨B, _, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (p := p) (by norm_num) hAscn2.le_pRank
    have hp2 : p ^ 2 ≤ Nat.card ↥B := Nat.pow_le_of_le_log Nat.card_pos.ne' hBlog
    have hBdvd : Nat.card ↥B ∣ Nat.card ↥(A.subgroupOf (P : Subgroup G)) :=
      Subgroup.card_subgroup_dvd_card B
    have hcard1 : Nat.card ↥(A.subgroupOf (P : Subgroup G)) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAbot, Subgroup.card_bot]
    rw [hcard1, Nat.dvd_one] at hBdvd
    rw [hBdvd] at hp2
    nlinarith [hp2, (Fact.out : p.Prime).two_le]
  have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hAne
  rw [hπ] at hYpi ⊢
  -- SCN ambient facts and solvability of `X` (a proper subgroup of a minimal simple group).
  obtain ⟨_, hAnormP, hCPA⟩ := scn_ambient hAP hAscn2.isSCN
  have hXsolv : Group.IsSolvable ↥X := hG.isSolvable_of_lt_top X hXlt
  -- `p` is odd (it divides `|G|`, which is odd).
  have hpA : p ∣ Nat.card ↥A := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [pow_zero] at hn; exact absurd (Subgroup.card_eq_one.mp hn) hAne
    · rw [hn]; exact dvd_pow_self p hn0.ne'
  have hp_odd : Odd p := hG.odd.of_dvd_nat (hpA.trans (Subgroup.card_subgroup_dvd_card A))
  have hp2 : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hp_odd; omega
  -- `Z(P)` inside `G`: elements of `P` that centralize `P`. `Z(P) ≤ A` (SCN), each is central in
  -- `P`.
  set ZP : Subgroup G :=
    Subgroup.centralizer ((P : Subgroup G) : Set G) ⊓ (P : Subgroup G) with hZPdef
  have hZP_le_A : ZP ≤ A := by
    intro x hx
    rw [hZPdef, Subgroup.mem_inf] at hx
    exact hCPA (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP) hx.1, hx.2⟩)
  have hZP_cent : ∀ b ∈ ZP, (P : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro b hb y hy
    rw [hZPdef, Subgroup.mem_inf] at hb
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
    exact (Subgroup.mem_centralizer_iff.mp hb.1 y hy).symm
  have hZP_le_P : ZP ≤ (P : Subgroup G) := by rw [hZPdef]; exact inf_le_right
  have hZP_pg : IsPGroup p ↥ZP := (P.isPGroup').to_le hZP_le_P
  by_cases hZPcyc : IsCyclic ↥ZP
  · -- **cyclic `Z(P)`**: `B = ⟨z⟩ × Ω₁(Z(P))` via Isaacs Lemma 1.23; `b ∈ B^#` uses special case 2.
    -- A `p`-central element `z` of order `p` (Cauchy on the nontrivial `p`-group `Z(P) = ZP`).
    have hPnt : Nontrivial ↥(P : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot => hAne (le_bot_iff.mp (hAP.trans_eq hbot))
    have hZc : Nontrivial (Subgroup.center ↥(P : Subgroup G)) :=
      IsPGroup.center_nontrivial P.isPGroup'
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥(P : Subgroup G))
    have hz₀_mem : ((w : ↥(P : Subgroup G)) : G) ∈ ZP := by
      rw [hZPdef, Subgroup.mem_inf]
      refine ⟨?_, (w : ↥(P : Subgroup G)).2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg (Subtype.val : ↥(P : Subgroup G) → G)
        (Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩)
    have hZP_nt : Nontrivial ↥ZP :=
      (Subgroup.nontrivial_iff_exists_ne_one ZP).mpr
        ⟨_, hz₀_mem, fun hval => hw1 (Subtype.ext (Subtype.ext hval))⟩
    have hp_dvd_ZP : p ∣ Nat.card ↥ZP := by
      obtain ⟨n, hn0, hn⟩ := hZP_pg.nontrivial_iff_card.mp hZP_nt
      rw [hn]; exact dvd_pow_self p hn0.ne'
    obtain ⟨zsub, hz_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_ZP
    set z : G := (zsub : G) with hzdef
    have hzZP : z ∈ ZP := SetLike.coe_mem zsub
    have hzA : z ∈ A := hZP_le_A hzZP
    have hzP : z ∈ (P : Subgroup G) := hZP_le_P hzZP
    have hz_centP : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := hZP_cent z hzZP
    have hz_ord' : orderOf z = p := by
      rw [hzdef, ← hz_ord]; exact orderOf_injective ZP.subtype ZP.subtype_injective zsub
    -- `A` is abelian (set form), `Ω₁(A)` and its normality in `P`.
    have hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨x, hx⟩ ⟨y, hy⟩)
    set Om : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set with hOmdef
    have hOm_le_A : Om ≤ A := OddOrder.GroupTheory.omega1OfAbelian_le
    have hOm_le_P : Om ≤ (P : Subgroup G) := hOm_le_A.trans hAP
    have hz_mem_Om : z ∈ Om := by
      rw [hOmdef, OddOrder.GroupTheory.mem_omega1OfAbelian]
      exact ⟨hzA, by rw [← hz_ord']; exact pow_orderOf_eq_one z⟩
    -- `|Ω₁(A)| ≥ p²` from `pRank A ≥ 2`.
    have hpRankA : 2 ≤ pRank A p := le_trans hAscn2.le_pRank
      (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hAP).injective)
    have hp2_dvd_Om : p ^ 2 ∣ Nat.card ↥Om := by
      rw [hOmdef]
      exact OddOrder.GroupTheory.pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankA
    -- `⟨z⟩ ⊴ P` and `Ω₁(A) ⊴ P` (both restricted to `↥P`).
    have hZ₁_le_P : Subgroup.zpowers z ≤ (P : Subgroup G) := Subgroup.zpowers_le.mpr hzP
    have hP_norm_Z : (P : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers z) := by
      intro g hg
      have hc : Commute g z := (Subgroup.mem_centralizer_iff.mp (hz_centP hg) z rfl).symm
      have hfix : ∀ y ∈ Subgroup.zpowers z, g * y * g⁻¹ = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [(hc.zpow_right k).eq]; group
      have hfix' : ∀ y ∈ Subgroup.zpowers z, g⁻¹ * y * g = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [(hc.inv_left.zpow_right k).eq]; group
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; rw [hfix x hx]; exact hx
      · intro hx
        have h1 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := hfix' _ hx
        have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
        rw [h2] at h1; rw [h1]; exact hx
    have hP_norm_Om : (P : Subgroup G) ≤ Subgroup.normalizer Om := by
      intro g hg
      have hgN : g ∈ Subgroup.normalizer A := hAnormP hg
      have hconjp : ∀ y : G, (g * y * g⁻¹) ^ p = g * y ^ p * g⁻¹ := fun y => by
        simp
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hOmdef, OddOrder.GroupTheory.mem_omega1OfAbelian]
      constructor
      · rintro ⟨hxA, hxp⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp hxA, by rw [hconjp x, hxp]; group⟩
      · rintro ⟨hxA, hxp⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mpr hxA, ?_⟩
        have hgx : g * x ^ p * g⁻¹ = 1 := by rw [← hconjp x]; exact hxp
        calc x ^ p = g⁻¹ * (g * x ^ p * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hgx]
          _ = 1 := by group
    -- Isaacs Lemma 1.23 inside `↥P`: a normal `L` with `⟨z⟩ < L ≤ Ω₁(A)`, `|⟨z⟩ : L| = p`.
    set Npp : Subgroup ↥(P : Subgroup G) := (Subgroup.zpowers z).subgroupOf (P : Subgroup G)
      with hNppdef
    set Mpp : Subgroup ↥(P : Subgroup G) := Om.subgroupOf (P : Subgroup G) with hMppdef
    have hNpp_normal : Npp.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZ₁_le_P).mpr hP_norm_Z
    have hMpp_normal : Mpp.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOm_le_P).mpr hP_norm_Om
    have hNcard : Nat.card ↥Npp = p := by
      rw [hNppdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₁_le_P).toEquiv,
        Nat.card_zpowers, hz_ord']
    have hNleM : Npp ≤ Mpp :=
      Subgroup.comap_mono (Subgroup.zpowers_le.mpr hz_mem_Om)
    have hMcard_ge : p ^ 2 ≤ Nat.card ↥Mpp := by
      rw [hMppdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOm_le_P).toEquiv]
      exact Nat.le_of_dvd Nat.card_pos hp2_dvd_Om
    have hNM : Npp < Mpp := by
      refine lt_of_le_of_ne hNleM (fun heq => ?_)
      rw [heq] at hNcard; rw [hNcard] at hMcard_ge
      nlinarith [(Fact.out : p.Prime).two_le, hMcard_ge]
    obtain ⟨Lpp, hLpp_normal, hN_lt_L, hL_le_M, hrelidx⟩ :=
      OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime P.isPGroup' hNM
    set B : Subgroup G := Lpp.map (P : Subgroup G).subtype with hBdef
    have hB_le_Om : B ≤ Om := by
      rw [hBdef]
      calc Lpp.map (P : Subgroup G).subtype ≤ Mpp.map (P : Subgroup G).subtype :=
            Subgroup.map_mono hL_le_M
        _ = Om := by rw [hMppdef, Subgroup.map_subgroupOf_eq_of_le hOm_le_P]
    have hBA : B ≤ A := hB_le_Om.trans hOm_le_A
    have hBP : B ≤ (P : Subgroup G) := hB_le_Om.trans hOm_le_P
    have hBcard : Nat.card ↥B = p ^ 2 := by
      rw [hBdef, Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective]
      have hmul : Nat.card ↥(Npp.subgroupOf Lpp) * (Npp.subgroupOf Lpp).index = Nat.card ↥Lpp :=
        Subgroup.card_mul_index _
      have hNsub : Nat.card ↥(Npp.subgroupOf Lpp) = Nat.card ↥Npp :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_lt_L.le).toEquiv
      have hidx_p : (Npp.subgroupOf Lpp).index = p := hrelidx
      rw [hNsub, hNcard, hidx_p] at hmul
      rw [← hmul]; ring
    have hBnorm : ∀ g ∈ (P : Subgroup G), ∀ x ∈ B, g * x * g⁻¹ ∈ B := by
      intro g hg x hx
      rw [hBdef, Subgroup.mem_map] at hx
      obtain ⟨xhat, hxhatL, rfl⟩ := hx
      rw [hBdef, Subgroup.mem_map]
      exact ⟨⟨g, hg⟩ * xhat * ⟨g, hg⟩⁻¹, hLpp_normal.conj_mem xhat hxhatL ⟨g, hg⟩, by
        simp [Subgroup.coe_mul]⟩
    -- `B` is elementary abelian of order `p²`, hence noncyclic.
    have hB_elem : B.IsElementaryAbelian p := by
      refine ⟨fun x y => Subtype.ext (hAcomm_set _ (hBA x.2) _ (hBA y.2)), fun x => Subtype.ext ?_⟩
      exact OddOrder.GroupTheory.pow_eq_one_of_mem_omega1OfAbelian (hB_le_Om x.2)
    have hBcomm : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_elem.1
    have hB_nc : ¬ IsCyclic ↥B := hB_elem.not_isCyclic_of_card_prime_sq Fact.out hBcard
    have hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b) := fun b hb =>
      (P.isPGroup').to_le (Subgroup.zpowers_le.mpr (hBP hb))
    have hpY : ¬ p ∣ Nat.card ↥Y := fun hdvd =>
      hYpi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩) rfl
    have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y) := by
      rw [hBcard]; exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpY).pow_left 2
    -- General case: feed special case 2 for each `b ∈ B^#`.
    refine coreClaimGeneral hXsolv hAX hBA hB_nc hBp hYX hAY hcop ?_
    intro b hb hb_ne
    exact centralizer_inf_le_opiCoreInG_of_central hG hp2 P hAab hAP hAnormP hCPA hBA hBP hBcard
      hBnorm hzA hzP hz_centP hz_ord' hAY hYpi hb hb_ne
  · -- **noncyclic `Z(P)`**: an `E_{p²} ⊆ Z(P) ⊆ A` of central elements; every `b ∈ B^#` lies in
    -- `Z(P)`, so special case 1 (`le_opiCoreInG_centralizer_of_mem_centralizer_sylow`) applies.
    obtain ⟨E, hE_elem, hE_card⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        hZP_pg hp_odd hZPcyc
    set B : Subgroup G := E.map ZP.subtype with hBdef
    have hB_le_ZP : B ≤ ZP := by rw [hBdef]; exact Subgroup.map_subtype_le E
    have hBA : B ≤ A := hB_le_ZP.trans hZP_le_A
    have hB_elem : B.IsElementaryAbelian p := by
      rw [hBdef]; exact hE_elem.map ZP.subtype_injective
    have hBcard : Nat.card ↥B = p ^ 2 := by
      rw [hBdef, (Nat.card_congr
        (Subgroup.equivMapOfInjective E ZP.subtype ZP.subtype_injective).toEquiv).symm]
      exact hE_card
    have hBcomm : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_elem.1
    have hB_nc : ¬ IsCyclic ↥B := hB_elem.not_isCyclic_of_card_prime_sq Fact.out hBcard
    have hBp : ∀ b ∈ B, IsPGroup p (Subgroup.zpowers b) := fun b hb =>
      (P.isPGroup').to_le (Subgroup.zpowers_le.mpr (hZP_le_P (hB_le_ZP hb)))
    have hpY : ¬ p ∣ Nat.card ↥Y := fun hdvd =>
      hYpi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩) rfl
    have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y) := by
      rw [hBcard]; exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpY).pow_left 2
    refine coreClaimGeneral hXsolv hAX hBA hB_nc hBp hYX hAY hcop ?_
    intro b hb hb_ne
    have hbA : b ∈ A := hBA hb
    have hA_le_Cb : A ≤ Subgroup.centralizer ({b} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      rintro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨b, hbA⟩ ⟨a, ha⟩)
    refine le_opiCoreInG_centralizer_of_mem_centralizer_sylow hG hp2 P hAP hAnormP hCPA hb_ne
      (hZP_cent b (hB_le_ZP hb)) inf_le_right ?_ ?_
    · -- `A ≤ N_G(Y ⊓ C_G(b))`: `A` normalizes both `Y` and `C_G(b)` (since `A ≤ C_G(b)`).
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hAY ha) x,
        Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hA_le_Cb ha)) x]
    · -- `Y ⊓ C_G(b)` is a `p'`-subgroup (its order divides `|Y|`).
      intro q hq
      exact hYpi q (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hq)

/-- **BG Proposition 7.5, case (2)** (SCN₂ branch, mmd L2263-2309): if `A ∈ SCN₂(P)` for a Sylow
`p`-subgroup `P`, then `A` satisfies Hypothesis 7.1. Separated from the `p`-length-one branch
(`hypothesis71_of_scn2_or_pLengthOne` case 1, which awaits Theorem 6.7) so that the Thompson
Transitivity Theorem (7.6) depends only on this `sorry`-free statement. -/
theorem hypothesis71_of_scn2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G))) :
    Hypothesis71 A := by
  -- `A ≠ ⊥`: `pRank (A.subgroupOf P) ≥ 2` forces an elementary abelian subgroup of order `≥ p²`.
  have hAne : A ≠ ⊥ := by
    intro hAbot
    obtain ⟨B, _, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (p := p) (by norm_num) hAscn2.le_pRank
    have hp2 : p ^ 2 ≤ Nat.card ↥B := Nat.pow_le_of_le_log Nat.card_pos.ne' hBlog
    have hBdvd : Nat.card ↥B ∣ Nat.card ↥(A.subgroupOf (P : Subgroup G)) :=
      Subgroup.card_subgroup_dvd_card B
    have hcard1 : Nat.card ↥(A.subgroupOf (P : Subgroup G)) = 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAbot, Subgroup.card_bot]
    rw [hcard1, Nat.dvd_one] at hBdvd
    rw [hBdvd] at hp2
    nlinarith [hp2, (Fact.out : p.Prime).two_le]
  -- `A < ⊤`: `A ≤ P` and a Sylow `p`-subgroup of a (non-solvable) minimal simple group is proper.
  have hAproper : A < ⊤ := by
    have hP_lt : (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hPtop
      have hGp : IsPGroup p G :=
        (hPtop ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      have : Group.IsNilpotent G := hGp.isNilpotent
      exact hG.notSolvable inferInstance
    exact lt_of_le_of_lt hAP hP_lt
  refine ⟨hAne, hAproper, ?_⟩
  intro X hAX hXlt
  refine generated_eq_of_forall_le_opiCoreInG hAX ?_
  intro Y hY
  rw [mem_hInvariant] at hY
  exact coreClaim_scn2 hG hAab hAp hAP hAscn2 hAX hXlt hY.1 hY.2.1 hY.2.2

/-- **BG Proposition 7.5** (mmd L2252): `p ∈ π(G)`, `A` abelian `p`-部分群で、
(1) `A = {x ∈ C_G(A) : x^p = 1}` かつ `G` の全真部分群が `p`-length one、または
(2) ある Sylow `p`-部分群 `P` で `A ∈ SCN₂(P)`、
のいずれかなら `A` は Hypothesis 7.1 を満たす。case (1) は `A = Ω₁(C_G(A))` から `A` が `↥X` 内で
包含極大 elementary abelian になることを使い Theorem 6.7 を適用; case (2) は `hypothesis71_of_scn2`
へ委譲。 -/
theorem hypothesis71_of_scn2_or_pLengthOne [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (A : Subgroup G) (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        (∀ M : Subgroup G, M < ⊤ → Ch1.hasPLengthOne p M)) ∨
      (∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
        IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)))) :
    Hypothesis71 A := by
  rcases hcase with hcase1 | hcase2
  · -- **case (1)**: `A = Ω₁(C_G(A))` and every proper subgroup is `p`-length one. Each
    -- `Y ∈ ℋ_X(A;p')` lands in `O_{p'}(X)` by **Theorem 6.7** (applied inside `↥X`), using that
    -- `A = {x ∈ C_G(A) : x^p = 1}` makes `A` maximal-by-inclusion elementary abelian in `↥X`.
    classical
    obtain ⟨hAeq, hplM⟩ := hcase1
    -- `x ∈ A ↔ x ∈ C_G(A) ∧ x^p = 1` (membership unfolding of `hAeq`).
    have hAmem : ∀ x : G, x ∈ A ↔
        (x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1) := fun x => by
      simpa using Set.ext_iff.mp hAeq x
    -- `p` is odd (it divides `|G|`, which is odd).
    have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_mem
    have hp_odd : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hp_odd_prop; omega
    -- `A` is elementary abelian: abelian (`hAab`) of exponent `p` (`hAmem`).
    have hAelem : A.IsElementaryAbelian p := by
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · exact isMulCommutative_iff.mp hAab x y
      · exact Subtype.ext (by
          rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
          exact ((hAmem (x : G)).mp x.2).2)
    -- `A` is maximal-by-inclusion elementary abelian in `G`: any elementary abelian `F ⊇ A`
    -- collapses to `A`, since every `f ∈ F` is `p`-torsion and (being in the abelian `F ⊇ A`)
    -- centralizes `A`, hence lies in `A` by `hAmem`.
    have hAmax : OddOrder.GroupTheory.IsMaximalElementaryAbelian p A := by
      refine ⟨hAelem, fun F hF hAF => le_antisymm ?_ hAF⟩
      intro f hf
      refine (hAmem f).mpr ⟨?_, ?_⟩
      · -- `f ∈ C_G(A)`: `f` and any `a ∈ A` both lie in the abelian `F`.
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have := hF.1 ⟨a, hAF ha⟩ ⟨f, hf⟩
        exact congrArg Subtype.val this
      · -- `f ^ p = 1`: `F` has exponent `p`.
        have := hF.2 ⟨f, hf⟩
        have := congrArg Subtype.val this
        rwa [SubmonoidClass.coe_pow, Subgroup.coe_one] at this
    -- `A ≠ ⊥`: otherwise `C_G(A) = ⊤`, so a Cauchy element of order `p` would satisfy `hAmem`
    -- and land in `A = ⊥`, forcing it to be trivial.
    have hAne : A ≠ ⊥ := by
      intro hAbot
      have hCtop : Subgroup.centralizer (A : Set G) = ⊤ := by
        rw [Subgroup.centralizer_eq_top_iff_subset, hAbot]
        intro x hx
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
        rw [hx]
        exact Subgroup.one_mem _
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hp_mem
      rw [orderOf_eq_prime_iff] at hg
      have hgA : g ∈ A := (hAmem g).mpr ⟨hCtop ▸ Subgroup.mem_top g, hg.1⟩
      rw [hAbot, Subgroup.mem_bot] at hgA
      exact hg.2 hgA
    -- `A < ⊤`: otherwise `G` is a `p`-group, hence nilpotent and solvable, contradicting `hG`.
    have hAproper : A < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hAtop
      have hGp : IsPGroup p G :=
        (hAtop ▸ hAp : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      have : Group.IsNilpotent G := hGp.isNilpotent
      exact hG.notSolvable inferInstance
    refine ⟨hAne, hAproper, ?_⟩
    intro X hAX hXlt
    have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hAne
    refine generated_eq_of_forall_le_opiCoreInG hAX ?_
    intro Y hY
    obtain ⟨hYX, hAnormY, hYpi⟩ := mem_hInvariant.mp hY
    have hXsolv : Group.IsSolvable ↥X := hG.isSolvable_of_lt_top X hXlt
    -- **Translate to `↥X`** and apply Theorem 6.7 with `E := A.subgroupOf X`,
    -- `L := Y.subgroupOf X`. `A.subgroupOf X` is maximal-by-inclusion elementary abelian
    -- in `↥X` (lift of `hAmax`).
    have hEXmax :
        OddOrder.GroupTheory.IsMaximalElementaryAbelian p (A.subgroupOf X) := by
      refine ⟨?_, fun Fbar hFbar hsub => ?_⟩
      · -- elementary abelian, transported along `A.subgroupOf X ≃* A`.
        exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hAX).symm hAelem
      · -- maximality: push `Fbar` down to `F := Fbar.map X.subtype ≤ G`, which is elementary
        -- abelian and contains `A`; by `hAmax`, `F = A`, so `Fbar = A.subgroupOf X`.
        set F : Subgroup G := Fbar.map X.subtype with hFdef
        have hF_elem : F.IsElementaryAbelian p := hFbar.map X.subtype_injective
        have hAF : A ≤ F := by
          have hmap : (A.subgroupOf X).map X.subtype ≤ Fbar.map X.subtype :=
            Subgroup.map_mono hsub
          rwa [Subgroup.map_subgroupOf_eq_of_le hAX] at hmap
        have hFA : F = A := hAmax.2 F hF_elem hAF
        -- `Fbar = (Fbar.map X.subtype).comap X.subtype = A.comap X.subtype = A.subgroupOf X`.
        calc Fbar = (Fbar.map X.subtype).comap X.subtype :=
              (Subgroup.comap_map_eq_self_of_injective X.subtype_injective Fbar).symm
          _ = A.comap X.subtype := by rw [← hFdef, hFA]
          _ = A.subgroupOf X := rfl
    -- `Y.subgroupOf X` is a `p'`-group (its order equals `|Y|`, a `p'`-number).
    have hLp' : ¬ p ∣ Nat.card (Y.subgroupOf X) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv]
      intro hdvd
      have hpmem : p ∈ (Nat.card ↥Y).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
      have : p ∈ (primesOf A)ᶜ := hYpi p hpmem
      rw [hπ] at this
      exact this rfl
    -- `A.subgroupOf X` normalizes `Y.subgroupOf X` (lift of `hAnormY`).
    have hELY : A.subgroupOf X ≤ Subgroup.normalizer (Y.subgroupOf X) := by
      intro a ha
      rw [Subgroup.mem_subgroupOf] at ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      have hcoe : ((a * y * a⁻¹ : ↥X) : G) = (a : G) * (y : G) * (a : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      exact Subgroup.mem_normalizer_iff.mp (hAnormY ha) (y : G)
    have hpl1X : OddOrder.BG.Ch1.hasPLengthOne p ↥X := hplM X hXlt
    have key := OddOrder.BG.Ch1.S06.le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian
      (G := ↥X) hp_odd hEXmax hLp' hELY hpl1X
    -- `key : Y.subgroupOf X ≤ O_{p'}(↥X)`. Map back to `G` and rewrite `(primesOf A)ᶜ = {q ∉ {p}}`.
    have hYeq : Y = (Y.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hYX).symm
    have hcompl : (primesOf A)ᶜ = {q | q ∉ ({p} : Set ℕ)} := by rw [hπ]; rfl
    rw [hcompl, opiCoreInG, hYeq]
    exact Subgroup.map_mono key
  · -- **case (2)**: delegate to the `sorry`-free SCN₂ branch.
    obtain ⟨P, hAP, hAscn2⟩ := hcase2
    exact hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2

/-- **BG Theorem 7.6** (Thompson Transitivity Theorem, mmd L2311): `p ∈ π(G)`,
`A ∈ SCN₃(p)`, `q ∈ p'` ⇒ `O_{p'}(C_G(A))` は `ℋ_G*(A;q)` 上推移的に作用する。
§8–§16 で最頻出。証明は Prop 7.5(2) + Thm 7.2。 -/
theorem thompsonTransitivity [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (_hp_mem : p ∣ Nat.card G)
    {A : Subgroup G} (hA : A ∈ scn3Global p G) {q : ℕ} [Fact q.Prime] (hq : q ≠ p) :
    ConjTransitiveOn (opiCoreInG {p}ᶜ (Subgroup.centralizer (A : Set G)))
      (hInvariantStar ⊤ A {q}) := by
  obtain ⟨P, hAP, hAscn3⟩ := hA
  have hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) := IsSCN_n.mono (by norm_num) hAscn3
  have hAab : IsMulCommutative A := (scn_ambient hAP hAscn2.isSCN).1
  have hAp : IsPGroup p ↥A := (P.isPGroup').to_le hAP
  -- `A` satisfies Hypothesis 7.1 (Proposition 7.5, SCN₂ branch).
  have hHyp : Hypothesis71 A := hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2
  -- `π(A) = {p}`, so `q ∈ (π A)ᶜ` and `kSubgroup A = O_{p'}(C_G(A))`.
  have hπ : primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton hAp hHyp.ne_bot
  have hq' : q ∈ (primesOf A)ᶜ := by rw [hπ]; simpa using hq
  -- `3 ≤ rank ↥(Z(A))`: `A` is abelian, so `Z(A) = ⊤`, and `pRank (A.subgroupOf P) ≥ 3`.
  have hrank : 3 ≤ rank ↥(Subgroup.center ↥A) := by
    have h3 : (3 : ℕ) ≤ pRank ↥A p :=
      le_trans hAscn3.le_pRank
        (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hAP).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hAP).injective)
    have hcenter : Subgroup.center (↥A) = ⊤ := by
      rw [Subgroup.center_eq_top_iff]; exact hAab
    rw [hcenter]
    exact le_trans (le_trans h3 (pRank_le_rank p))
      (rank_le_of_injective (f := (Subgroup.topEquiv (G := ↥A)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := ↥A)).symm.injective)
  -- Theorem 7.2, then rewrite `kSubgroup A = O_{p'}(C_G(A))`.
  have htrans := transitive_of_three_le_rank_center hG hHyp hq' hrank
  rw [← hπ]
  exact htrans

end OddOrder.BG.Ch2.S07


