-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_YsetConjugation
-- name    : OddOrder_Peterfalvi_S08_YsetConjugation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:20:44.463539+00:00
-- url     : https://prove2.me/theorems/0b45e251-99d8-4519-b5cc-ce9ae671e23a
-- title:
--   Peterfalvi §8: filtration and $Y$-set conjugation
-- statement:
--   The $S(A)$, $X$, and $Y$ filtration API and the $Y$-set conjugation/coherence construction in Peterfalvi §8.
--
--   Main definitions: `SsubFiltration` (Peterfalvi (6.1) filtration $S(A)$ in the (6.8) setup), `Xset` (the (6.8) set $X=S-S(Z)$ for a normal $Z\subseteq Z(H)$), `Yset` (the (6.8) set $Y=S(H')$ with $H'=[H,H]$), `centralCommutator` (the case (A) central subgroup $Z=Z(H)\cap H'$, shown normal in $L$) and `coherentYset_of_pairwiseNonconj` (coherence of $Y=S(H')$ from finite orbit representatives of nontrivial linear characters).
--
--   The bundle also proves 42 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_YsetConjugation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_YsetConjugation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetConjugation_InducedFamilies

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Peterfalvi (6.1) filtration `S(A)`** in the (6.8) setup: the members `Ind_H^L θ` of `S`
(`θ ∈ Irr H`, `θ ≠ 1_H`) whose source `θ` has `A` (as a subgroup of `H`) inside its kernel.
`S(1) = S`, and the (6.8) sets are `X = S − S(Z)` and `Y = S(H')`. -/
def SsubFiltration (_hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥H,
    θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
    (A.subgroupOf H : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
    φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ)}

/-- The (6.8) set `X = S − S(Z)` (the (6.6) `X`-set) for a normal `Z ⊆ Z(H)`. -/
def Xset (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  hyp.S \ hyp.SsubFiltration Z

/-- The (6.8) set `Y = S(H')` (`H' = [H,H]`), the equal-degree family handled by T6. -/
def Yset (hyp : SibleyDadeHypothesis G L H) : Set (ClassFunction ↥L ℂ) :=
  hyp.SsubFiltration ⁅H, H⁆

/-- **(6.8) case (A) central subgroup `Z = Z(H) ∩ H′`** (Peterfalvi (6.8), p.34: *"Set
`Z = Z(H) ∩ H′` in case (A)"*).  This is the **correct** `(6.6)` `Z` for the `X = S − S(Z)`
coherence step: it is **central in `H`** (so [Is] Cor 2.30 `exists_degree_sq_le_index` bounds
`θ(1)² ≤ |H:Z|`, making the per-step degree field fillable) and contained in `H′ = ⁅H,H⁆`.

The earlier capstone route mis-instantiated the `(6.6)` producer at `Z = ⁅H,H⁆`, which is **not**
central for class `≥ 3` `p`-groups (e.g. `UT(4,p)`), so its degree field `θχ² ≤ qtot ≤ |H:⁅H,H⁆|`
was unsatisfiable.  See `notes/peterfalvi/s08_6_8_blocker_central_Z.md`. -/
def centralCommutator (_hyp : SibleyDadeHypothesis G L H) : Subgroup ↥L :=
  (Subgroup.center ↥H).map H.subtype ⊓ ⁅H, H⁆

theorem centralCommutator_le_commutator (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ ⁅H, H⁆ := by
  simp only [centralCommutator]; exact inf_le_right

theorem centralCommutator_le (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator ≤ H := by
  have := hyp.H_normal
  exact le_trans hyp.centralCommutator_le_commutator (Subgroup.commutator_le_left H H)

/-- `Z = Z(H) ∩ H′` is central in `H`: its trace `Z.subgroupOf H` lies in `Z(↥H)`.  This is the
hypothesis [Is] Cor 2.30 / `IsIrreducibleCharacter.exists_degree_sq_le_index` needs to bound
`θ(1)² ≤ |H : Z|` for the `(6.6)` per-step degree field. -/
theorem centralCommutator_subgroupOf_le_center (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H ≤ Subgroup.center ↥H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  simp only [centralCommutator] at hx
  have hx2 : (x : ↥L) ∈ (Subgroup.center ↥H).map H.subtype := (Subgroup.mem_inf.mp hx).1
  rw [Subgroup.mem_map] at hx2
  obtain ⟨z, hz, hzx⟩ := hx2
  have hzx' : z = x := Subtype.ext (by simpa using hzx)
  rwa [← hzx']

/-- `Z = Z(H) ∩ H′` is normal in `L`: `(center ↥H).map H.subtype` is normal (characteristic in the
normal `H`, via `normal_of_characteristic_of_normal`) and `⁅H,H⁆` is normal, so their inf is. -/
instance centralCommutator_normal (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.Normal := by
  have := hyp.H_normal
  have : (⁅H, H⁆ : Subgroup ↥L).Normal := Subgroup.commutator_normal H H
  simp only [centralCommutator]
  infer_instance

/-- `Z = Z(H) ∩ H′` traced into `H` is `Z(↥H) ⊓ commutator ↥H`. -/
theorem centralCommutator_subgroupOf_eq (hyp : SibleyDadeHypothesis G L H) :
    hyp.centralCommutator.subgroupOf H
      = Subgroup.center ↥H ⊓ _root_.commutator ↥H := by
  have h1 : hyp.centralCommutator.subgroupOf H
      = ((Subgroup.center ↥H).map H.subtype).subgroupOf H
        ⊓ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H := by
    rw [centralCommutator]; exact Subgroup.comap_inf _ _ _
  rw [h1, commutator_subgroupOf_self]
  congr 1
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- `Z = Z(H) ∩ H′ ≠ 1` when `H` is non-abelian: a non-trivial nilpotent group has
`Z(H) ∩ H′ ≠ 1` (`isNilpotent_normal_inf_center_ne_bot` with `N = H′`). -/
theorem centralCommutator_ne_bot (hyp : SibleyDadeHypothesis G L H)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) : hyp.centralCommutator ≠ ⊥ := by
  have := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hkey : Subgroup.center ↥H ⊓ _root_.commutator ↥H ≠ ⊥ := by
    rw [inf_comm]
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  intro hbot
  apply hkey
  rw [← hyp.centralCommutator_subgroupOf_eq, hbot, Subgroup.bot_subgroupOf]

/-- **(c2)+math-(A) fixed-point-freeness on `Zc = Z(H) ∩ H'`** (Peterfalvi (6.8), case (A) in the
CertainType branch, i.e. `Z(H) ⊓ W₂ = 1`).  `W₁` acts fixed-point-freely on `Zc`: for `w ∈ W₁^#`,
`C_L(w) ⊓ Zc = 1`.  Indeed `C_L(w) ⊓ H = W₂` (`cert.centralizer_W2`) and `Zc ≤ H ⊓ Z(H).map`, so
`C_L(w) ⊓ Zc ≤ W₂ ⊓ (Z(H)).map = 1` (the lifted math-(A) hypothesis).  This is the `hZfpf` input
that `isIrreducibleCharacter_of_mem_Xset_caseA` (and the CB3 FPF generalization) needs at `Z = Zc`,
the (c2) analogue of the Frobenius fixed-point-free property. -/
theorem centralizer_inf_centralCommutator_eq_bot_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {w : ↥L} (hw : w ∈ hyp.W1) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator = ⊥ := by
  have := hyp.H_normal
  have hle : cert.W2 ≤ H := cert.W2_le_K.trans_eq hK
  -- `C_L(w) ⊓ H = W₂`
  have hCW2 : Subgroup.centralizer ({w} : Set ↥L) ⊓ H = cert.W2 := by
    have h := cert.centralizer_W2 w (hW1.symm ▸ hw) hw1
    rwa [hK] at h
  -- lift the math-(A) hypothesis from `↥H` to `↥L`: `(Z(H)).map ⊓ W₂ = ⊥`
  have hAmap : (Subgroup.center ↥H).map H.subtype ⊓ cert.W2 = ⊥ := by
    have h1 := congrArg (Subgroup.map H.subtype) hA
    rwa [Subgroup.map_inf _ _ H.subtype H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at h1
  have hccZ : hyp.centralCommutator ≤ (Subgroup.center ↥H).map H.subtype := by
    simp only [centralCommutator]; exact inf_le_left
  rw [← le_bot_iff]
  calc Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator
      ≤ (Subgroup.centralizer ({w} : Set ↥L) ⊓ H) ⊓ (Subgroup.center ↥H).map H.subtype :=
        le_inf (le_inf inf_le_left (inf_le_right.trans hyp.centralCommutator_le))
          (inf_le_right.trans hccZ)
    _ = cert.W2 ⊓ (Subgroup.center ↥H).map H.subtype := by rw [hCW2]
    _ = ⊥ := by rw [inf_comm]; exact hAmap

/-- **(6.7)-wiring step (c): the centralizer in `↥L` of a nontrivial `z ∈ Z = Z(H) ∩ H′` is `H`.**
`z ∈ Z(H)` gives `H ≤ C_L(z)`; `z ∈ H^#` with `L` Frobenius (kernel `H`) gives `C_L(z) ≤ H`
(`centralizer_kernel_le`). Hence `|C_L(z)| = |H|` is **constant on `Z^#`** — the
`|C_L(·)|`-constancy
input of Peterfalvi (6.7). -/
theorem centralizer_centralCommutator_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set ↥L) = H := by
  apply le_antisymm
  · exact hF.centralizer_kernel_le z (hyp.centralCommutator_le hz) hz1
  · intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzH : (z : ↥L) ∈ H := hyp.centralCommutator_le hz
    have hzc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H :=
      hyp.centralCommutator_subgroupOf_le_center (Subgroup.mem_subgroupOf.mpr hz)
    have hcomm := (Subgroup.mem_center_iff.mp hzc) ⟨h, hh⟩
    have hcoe := congrArg (H.subtype) hcomm
    simpa using hcoe

/-- **(6.7)-wiring step (c), case (A) / c2 form: `C_↥L(z) = H` for `z ∈ Zc^#`.**  The (c2) analogue
of `centralizer_centralCommutator_eq` (which used `hF.centralizer_kernel_le`).  `H ≤ C_L(z)` since
`z ∈ Z(H)`; for `C_L(z) ≤ H`, decompose `g ∈ C_L(z)` via the complement `L = H ⋊ W₁`
(`cert.isComplement`, `cert.K = H`) as `g = k·w` (`k ∈ H`, `w ∈ W₁`): `k` centralizes `z` (central),
so `w = k⁻¹g` centralizes `z`; if `w ≠ 1` then `z ∈ C_L(w) ⊓ Zc = ⊥`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`, the math-(A) FPF), contradicting `z ≠ 1`,
so
`w = 1` and `g = k ∈ H`.  Gives the `|C_L(·)|`-constancy on `Zc^#` of Peterfalvi (6.7) without
Frobenius. -/
theorem centralizer_centralCommutator_eq_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set ↥L) = H := by
  have := hyp.H_normal
  have hzH : (z : ↥L) ∈ H := hyp.centralCommutator_le hz
  have hzc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H :=
    hyp.centralCommutator_subgroupOf_le_center (Subgroup.mem_subgroupOf.mpr hz)
  apply le_antisymm
  · -- `C_L(z) ≤ H`
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg  -- `hg : g * z = z * g`
    -- `g = k·w` via the complement `L = H ⋊ W₁`
    obtain ⟨⟨⟨k, hk⟩, ⟨w, hw⟩⟩, hkw, -⟩ := Subgroup.IsComplement.existsUnique cert.isComplement g
    simp only at hkw  -- `hkw : k * w = g`
    rw [hK] at hk
    rw [hW1] at hw
    -- `k` centralizes `z` (central in `H`)
    have hkz : k * z = z * k := by
      have h := (Subgroup.mem_center_iff.mp hzc) ⟨k, hk⟩
      have hcoe := congrArg (H.subtype) h
      simpa using hcoe
    -- `w` centralizes `z`
    have hwz : w * z = z * w := by
      have h1 : k * (w * z) = k * (z * w) := by
        calc k * (w * z) = (k * w) * z := by rw [mul_assoc]
          _ = g * z := by rw [hkw]
          _ = z * g := hg
          _ = z * (k * w) := by rw [← hkw]
          _ = (z * k) * w := by rw [mul_assoc]
          _ = (k * z) * w := by rw [← hkz]
          _ = k * (z * w) := by rw [mul_assoc]
      exact mul_left_cancel h1
    by_cases hw1 : w = 1
    · rw [hw1, mul_one] at hkw
      rw [← hkw]; exact hk
    · exfalso
      have hzC : z ∈ Subgroup.centralizer ({w} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact hwz.symm
      have hmem : z ∈ Subgroup.centralizer ({w} : Set ↥L) ⊓ hyp.centralCommutator := ⟨hzC, hz⟩
      rw [hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA hw hw1,
        Subgroup.mem_bot] at hmem
      exact hz1 hmem
  · -- `H ≤ C_L(z)` (`z ∈ Z(H)`)
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (Subgroup.mem_center_iff.mp hzc) ⟨h, hh⟩
    have hcoe := congrArg (H.subtype) hcomm
    simpa using hcoe

/-- **(6.7)-wiring step (c′): the ambient-`G` form `(L:Subgroup G) ⊓ C_G(↑w) = H.map L.subtype`.**
Realizes `centralizer_centralCommutator_eq` (`C_↥L(w) = H`) in `G`: an element `g ∈ L` centralizes
`↑w` iff (as an element of `↥L`) it centralizes `w`, iff it lies in `H = C_↥L(w)`.  Hence
`|N_G(Ĥ) ⊓ C_G(w)| = |C_L(w)| = |Ĥ|` is **constant on `Z^#`** (`N_G(Ĥ) = L`), the centralizer-card
clause of Peterfalvi (6.7)'s `hconst`. -/
theorem inf_centralizer_centralCommutator_map (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {w : ↥L} (hw : w ∈ hyp.centralCommutator) (hw1 : w ≠ 1) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = H.map L.subtype := by
  have hCH := hyp.centralizer_centralCommutator_eq hF hw hw1
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · intro hg
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff] at hcH
    refine ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (L.subtype) hcH
    simpa using this

/-- **(6.7)-wiring step (c′), case (A) / c2 form: `(L:Subgroup G) ⊓ C_G(↑w) = H.map L.subtype`.**
The
(c2) analogue of `inf_centralizer_centralCommutator_map`, supplying the centralizer-card constancy
clause of Peterfalvi (6.7)'s `hconst` from the case-(A) `C_↥L(w) = H`
(`centralizer_centralCommutator_eq_c2_caseA`).  The subgroup manipulation is identical to the
Frobenius form. -/
theorem inf_centralizer_centralCommutator_map_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {w : ↥L} (hw : w ∈ hyp.centralCommutator) (hw1 : w ≠ 1) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = H.map L.subtype := by
  have := hyp.H_normal
  have hCH := hyp.centralizer_centralCommutator_eq_c2_caseA hK hW1 hA hw hw1
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hgc)
  · intro hg
    obtain ⟨c, hcH, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hCH, Subgroup.mem_centralizer_singleton_iff] at hcH
    refine ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (L.subtype) hcH
    simpa using this

/-- **(6.8.3) case-(A) fixed-point-free bound** `|Z| ≥ 2|W₁| + 1` (hence `|Z| − 1 ≥ 2|W₁|`).
`W₁` acts fixed-point-freely on `H` (`hF.toFrobeniusAction`), and `Z.subgroupOf H = Z(↥H) ⊓ H′` is
characteristic, so the action restricts fixed-point-freely to it (`IsFrobeniusAction.subgroup`);
`card_modEq_one` gives `|Z| ≡ 1 (mod |W₁|)`, and as `|Z|, |W₁|` are odd and `|Z| > 1`
(`H` non-abelian), `two_mul_add_one_le_of_odd_dvd` yields `2|W₁| + 1 ≤ |Z|`. -/
theorem centralCommutator_card_subgroupOf_lower (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    2 * Nat.card hyp.W1 + 1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
  classical
  let : H.Normal := hyp.H_normal
  let actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hFrobH : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1 ↥H := hF.toFrobeniusAction
  have hMeq : hyp.centralCommutator.subgroupOf H = Subgroup.center ↥H ⊓ _root_.commutator ↥H :=
    hyp.centralCommutator_subgroupOf_eq
  have hcprod : ∀ (K : Subgroup ↥H) [K.Characteristic] (a : ↥hyp.W1) (m : ↥H),
      m ∈ K → a • m ∈ K := by
    intro K _ a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic›
      (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ K := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hinv : ∀ a : ↥hyp.W1, ∀ m ∈ hyp.centralCommutator.subgroupOf H,
      a • m ∈ hyp.centralCommutator.subgroupOf H := by
    intro a m hm
    rw [hMeq, Subgroup.mem_inf] at hm ⊢
    exact ⟨hcprod (Subgroup.center ↥H) a m hm.1, hcprod (_root_.commutator ↥H) a m hm.2⟩
  let instM : MulDistribMulAction ↥hyp.W1 ↥(hyp.centralCommutator.subgroupOf H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hinv
  have hFrobM : @OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1
      ↥(hyp.centralCommutator.subgroupOf H) _ _ instM := hFrobH.subgroup _ hinv
  have : Fintype ↥hyp.W1 := Fintype.ofFinite _
  have : Fintype ↥(hyp.centralCommutator.subgroupOf H) := Fintype.ofFinite _
  have hMmod : Nat.card ↥(hyp.centralCommutator.subgroupOf H) ≡ 1 [MOD Nat.card hyp.W1] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobM.card_modEq_one
  have hMne : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    rw [hMeq, inf_comm]
    let : Group.IsNilpotent ↥H := hyp.H_nilpotent
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  have hMgt1 : 1 < Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
    have : Nontrivial ↥(hyp.centralCommutator.subgroupOf H) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hMne
    exact Finite.one_lt_card
  have hRdvd : Nat.card hyp.W1 ∣ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hMmod.symm
  have hW1odd : Odd (Nat.card hyp.W1) :=
    Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hModd : Odd (Nat.card ↥(hyp.centralCommutator.subgroupOf H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card H))
      (Subgroup.card_subgroup_dvd_card (hyp.centralCommutator.subgroupOf H))
  exact two_mul_add_one_le_of_odd_dvd hW1odd hModd hRdvd hMgt1

/-- **(6.8.3) case-(A) fixed-point-free bound, c2 form** `|Zc| ≥ 2|W₁| + 1`.  The (c2) analogue of
`centralCommutator_card_subgroupOf_lower` (which used `hF.toFrobeniusAction`).  `W₁` acts on `H` by
conjugation, restricting (characteristic `Z(H) ⊓ H′`) to `Zc.subgroupOf H`; the restricted action is
fixed-point-free *not* from a global Frobenius action but from the math-(A) FPF on `Zc`
(`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`: `C_L(w) ⊓ Zc = ⊥` for `w ∈ W₁^#`), giving
`|Zc| ≡ 1 (mod |W₁|)` and then `2|W₁| + 1 ≤ |Zc|`. -/
theorem centralCommutator_card_subgroupOf_lower_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥) :
    2 * Nat.card hyp.W1 + 1 ≤ Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
  classical
  let : H.Normal := hyp.H_normal
  let actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hMeq : hyp.centralCommutator.subgroupOf H = Subgroup.center ↥H ⊓ _root_.commutator ↥H :=
    hyp.centralCommutator_subgroupOf_eq
  have hcprod : ∀ (K : Subgroup ↥H) [K.Characteristic] (a : ↥hyp.W1) (m : ↥H),
      m ∈ K → a • m ∈ K := by
    intro K _ a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹K.Characteristic›
      (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ K := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hinv : ∀ a : ↥hyp.W1, ∀ m ∈ hyp.centralCommutator.subgroupOf H,
      a • m ∈ hyp.centralCommutator.subgroupOf H := by
    intro a m hm
    rw [hMeq, Subgroup.mem_inf] at hm ⊢
    exact ⟨hcprod (Subgroup.center ↥H) a m hm.1, hcprod (_root_.commutator ↥H) a m hm.2⟩
  let instM : MulDistribMulAction ↥hyp.W1 ↥(hyp.centralCommutator.subgroupOf H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction _ hinv
  -- FPF on `Zc.subgroupOf H` directly from the math-(A) FPF `C_L(w) ⊓ Zc = ⊥` (no global action).
  have hFrobM : @OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥hyp.W1
      ↥(hyp.centralCommutator.subgroupOf H) _ _ instM := by
    intro a ha m hm hfix
    apply hm
    -- `↑↑m ∈ Zc`
    have hmZc : ((m : ↥H) : ↥L) ∈ hyp.centralCommutator :=
      (Subgroup.mem_subgroupOf).mp m.2
    have ha1 : (hyp.W1.subtype a : ↥L) ≠ 1 := fun h => ha (Subtype.ext h)
    -- actH-fixedness of `↑m` (definitional from the invariant-subgroup action)
    have hfixH : a • (m : ↥H) = (m : ↥H) := Subtype.ext_iff.mp hfix
    have hc : MulAut.conjNormal (hyp.W1.subtype a) (m : ↥H) = (m : ↥H) := hfixH
    -- `↑a` centralizes `↑↑m`
    have hcomm : ((m : ↥H) : ↥L) ∈
        Subgroup.centralizer ({(hyp.W1.subtype a : ↥L)} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hL := congrArg (fun x : ↥H => (x : ↥L)) hc
      simp only [MulAut.conjNormal_apply] at hL
      rw [mul_inv_eq_iff_eq_mul] at hL
      exact hL.symm
    have hbot := hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA
      (w := (hyp.W1.subtype a : ↥L)) a.2 ha1
    have hmem : ((m : ↥H) : ↥L) ∈
        Subgroup.centralizer ({(hyp.W1.subtype a : ↥L)} : Set ↥L) ⊓ hyp.centralCommutator :=
      ⟨hcomm, hmZc⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have : Fintype ↥hyp.W1 := Fintype.ofFinite _
  have : Fintype ↥(hyp.centralCommutator.subgroupOf H) := Fintype.ofFinite _
  have hMmod : Nat.card ↥(hyp.centralCommutator.subgroupOf H) ≡ 1 [MOD Nat.card hyp.W1] := by
    simpa only [Fintype.card_eq_nat_card] using hFrobM.card_modEq_one
  have hMne : hyp.centralCommutator.subgroupOf H ≠ ⊥ := by
    rw [hMeq, inf_comm]
    let : Group.IsNilpotent ↥H := hyp.H_nilpotent
    exact isNilpotent_normal_inf_center_ne_bot (Subgroup.commutator_normal ⊤ ⊤) hHnonab
  have hMgt1 : 1 < Nat.card ↥(hyp.centralCommutator.subgroupOf H) := by
    have : Nontrivial ↥(hyp.centralCommutator.subgroupOf H) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hMne
    exact Finite.one_lt_card
  have hRdvd : Nat.card hyp.W1 ∣ Nat.card ↥(hyp.centralCommutator.subgroupOf H) - 1 :=
    (Nat.modEq_iff_dvd' (by omega)).mp hMmod.symm
  have hW1odd : Odd (Nat.card hyp.W1) :=
    Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hModd : Odd (Nat.card ↥(hyp.centralCommutator.subgroupOf H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hyp.card_L_odd (Subgroup.card_subgroup_dvd_card H))
      (Subgroup.card_subgroup_dvd_card (hyp.centralCommutator.subgroupOf H))
  exact two_mul_add_one_le_of_odd_dvd hW1odd hModd hRdvd hMgt1

/-- Membership in `S(A)`, unfolded. -/
theorem mem_SsubFiltration (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.SsubFiltration A ↔ ∃ θ : IrreducibleCharacter ↥H,
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H ∧
      (A.subgroupOf H : Set ↥H) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
  Iff.rfl

/-- `S(⊥) = S`: the kernel condition `⊥ ⊆ Ker θ` is vacuous, so the bottom filtration is all of
`S`.  (Peterfalvi writes `S(1) = S`.) -/
theorem SsubFiltration_bot (hyp : SibleyDadeHypothesis G L H) :
    hyp.SsubFiltration ⊥ = hyp.S := by
  ext φ
  rw [hyp.mem_SsubFiltration, hyp.S_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, -, hφ⟩
    exact ⟨θ, hθ, hφ⟩
  · rintro ⟨θ, hθ, hφ⟩
    refine ⟨θ, hθ, ?_, hφ⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _

/-- Membership in `X = S − S(Z)`, unfolded. -/
theorem mem_Xset (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Xset Z ↔ φ ∈ hyp.S ∧ φ ∉ hyp.SsubFiltration Z :=
  Iff.rfl

/-- Every member of the filtration `S(A)` is a member of the ambient set `S`. -/
theorem SsubFiltration_subset_S (hyp : SibleyDadeHypothesis G L H) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.S := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, _hker, hφeq⟩ := hφ
  rw [hyp.S_eq]
  exact ⟨θ, hθ_ne, hφeq⟩

/-- `X(Z) = S - S(Z)` is contained in `S`. -/
theorem Xset_subset_S (hyp : SibleyDadeHypothesis G L H) {Z : Subgroup ↥L} :
    hyp.Xset Z ⊆ hyp.S := by
  intro φ hφ
  exact (hyp.mem_Xset.mp hφ).1

/-- `Y = S(H')` is contained in `S`. -/
theorem Yset_subset_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Yset ⊆ hyp.S := by
  intro φ hφ
  rw [Yset] at hφ
  exact hyp.SsubFiltration_subset_S hφ

/-- `X(Z) = S - S(Z)` is disjoint from `S(Z)`. -/
theorem disjoint_Xset_SsubFiltration
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    Disjoint (hyp.Xset Z) (hyp.SsubFiltration Z) := by
  rw [Set.disjoint_left]
  intro φ hφX hφZ
  exact (hyp.mem_Xset.mp hφX).2 hφZ

/-- `X(Z)` and `S(Z)` partition `S`. -/
theorem Xset_union_SsubFiltration_eq_S
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.Xset Z ∪ hyp.SsubFiltration Z = hyp.S := by
  ext φ
  constructor
  · intro hφ
    rcases hφ with hφX | hφZ
    · exact hyp.Xset_subset_S hφX
    · exact hyp.SsubFiltration_subset_S hφZ
  · intro hφS
    by_cases hφZ : φ ∈ hyp.SsubFiltration Z
    · exact Or.inr hφZ
    · exact Or.inl (hyp.mem_Xset.mpr ⟨hφS, hφZ⟩)

/-- The Peterfalvi filtration is antitone: a larger subgroup imposes a stronger kernel
condition. -/
theorem SsubFiltration_antitone
    (hyp : SibleyDadeHypothesis G L H) {A B : Subgroup ↥L} (hAB : A ≤ B) :
    hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ_ne, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

/-- The (6.8) sets `X = S - S(H')` and `Y = S(H')` partition `S`. -/
theorem Xset_union_Yset_eq_S (hyp : SibleyDadeHypothesis G L H) :
    hyp.Xset ⁅H, H⁆ ∪ hyp.Yset = hyp.S := by
  simpa [Yset] using hyp.Xset_union_SsubFiltration_eq_S (Z := ⁅H, H⁆)

/-- A nontrivial irreducible character remains nontrivial after complex conjugation. -/
theorem irreducibleCharacter_conj_ne_trivial {Γ : Type*} [Group Γ] [Finite Γ]
    {θ : IrreducibleCharacter Γ}
    (hθ_ne : θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ) :
    (⟨(θ : ClassFunction Γ ℂ).conj, θ.isIrreducible.conj⟩ :
      IrreducibleCharacter Γ) ≠
        OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ := by
  intro hθc
  apply hθ_ne
  apply IrreducibleCharacter.ext
  have hval : (θ : ClassFunction Γ ℂ).conj =
      (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
    simpa using congrArg
      (fun η : IrreducibleCharacter Γ => (η : ClassFunction Γ ℂ)) hθc
  calc
    (θ : ClassFunction Γ ℂ) = ((θ : ClassFunction Γ ℂ).conj).conj := by
      rw [ClassFunction.conj_conj]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ).conj := by
      rw [hval]
    _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter Γ :
        ClassFunction Γ ℂ) := by
      ext x
      simp

/-- `S = {Ind_H^L θ | θ ∈ Irr(H), θ ≠ 1}` is finite, directly from the finite source
irreducible-character set. -/
theorem S_finite (hyp : SibleyDadeHypothesis G L H) :
    hyp.S.Finite := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter ↥H) :=
    OddOrder.RepresentationTheory.finite_irreducibleCharacter (G := ↥H)
  refine (Set.finite_range
    (fun θ : {θ : IrreducibleCharacter ↥H //
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H} =>
      ClassFunction.induce H (θ.1 : ClassFunction ↥H ℂ))).subset ?_
  intro φ hφ
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  exact ⟨⟨θ, hθ_ne⟩, hφeq.symm⟩

/-- Every filtration layer `S(A)` is finite, because it is a subset of `S`. -/
theorem SsubFiltration_finite (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    (hyp.SsubFiltration A).Finite :=
  hyp.S_finite.subset hyp.SsubFiltration_subset_S

/-- `X(Z) = S - S(Z)` is finite, because it is a subset of `S`. -/
theorem Xset_finite (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    (hyp.Xset Z).Finite :=
  hyp.S_finite.subset hyp.Xset_subset_S

/-- `S` is closed under complex conjugation.  This is a source-side fact:
`conj (Ind_H^L θ) = Ind_H^L (conj θ)`. -/
theorem S_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.S := by
  intro φ hφ
  rw [hyp.S_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_⟩
  rw [hφeq]
  simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- Each Peterfalvi filtration layer `S(A)` is closed under complex conjugation.  The
kernel condition is preserved by conjugating the source character. -/
theorem SsubFiltration_closedUnderConjugate
    (hyp : SibleyDadeHypothesis G L H) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.SsubFiltration A) := by
  intro φ hφ
  rw [hyp.mem_SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial hθ_ne, ?_, ?_⟩
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `X(Z) = S - S(Z)` is closed under complex conjugation, without first proving
`X(Z) ⊆ Irr(L)`. -/
theorem Xset_closedUnderConjugate_unconditional
    (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.Xset Z) := by
  intro φ hφ
  obtain ⟨hφS, hφnotZ⟩ := hyp.mem_Xset.mp hφ
  refine hyp.mem_Xset.mpr ⟨hyp.S_closedUnderConjugate hφS, ?_⟩
  intro hφcZ
  have hφccZ := hyp.SsubFiltration_closedUnderConjugate Z hφcZ
  exact hφnotZ (by simpa [ClassFunction.conj_conj] using hφccZ)

/-- A nontrivial linear source character induces to a member of `Y = S(H')`.

The witness in `S(H')` is `linearIrreducibleCharacter χ`.  Its kernel contains
`H' = [H,H]` because a degree-one character kills commutators. -/
theorem induce_linearIrreducibleCharacter_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {χ : ↥H →* ℂˣ}
    (hχ_ne : χ ≠ 1) :
    ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) ∈
      hyp.Yset := by
  rw [Yset]
  refine ⟨linearIrreducibleCharacter χ, ?_, ?_, rfl⟩
  · rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
    exact hχ_ne
  · intro x hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, linearIrreducibleCharacter_apply_one]
    have hsubgroupOf_eq :
        ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
      rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [hsubgroupOf_eq] at hx
    have hxclosure : x ∈ Subgroup.closure (commutatorSet ↥H) := by
      rwa [_root_.commutator_eq_closure] at hxcomm
    refine Subgroup.closure_induction
      (p := fun y _ => (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) y = 1)
      ?_ ?_ ?_ ?_ hxclosure
    · rintro _ ⟨a, b, rfl⟩
      have hlin := (linearIrreducibleCharacter χ).isIrreducible
      exact hlin.apply_commutatorElement_eq_one_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a b
    · exact linearIrreducibleCharacter_apply_one χ
    · intro a b _ _ ha hb
      rw [(linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ), ha, hb, one_mul]
    · intro a _ ha
      have hai := (linearIrreducibleCharacter χ).isIrreducible.map_mul_of_apply_one_eq_one
        (linearIrreducibleCharacter_apply_one χ) a a⁻¹
      rw [mul_inv_cancel, linearIrreducibleCharacter_apply_one χ, ha, one_mul] at hai
      exact hai.symm

/-- A source character whose kernel contains `H'` comes from a linear character of `H`.

The proof factors the source through the abelianization `H/H'`; irreducible characters of a finite
commutative group are degree one, hence are `linearIrreducibleCharacter`s, and pulling that linear
character back along `Abelianization.of` recovers the original source. -/
theorem exists_linearIrreducibleCharacter_eq_of_YsetSource
    (_hyp : SibleyDadeHypothesis G L H) {θ : IrreducibleCharacter ↥H}
    (hker : (((⁅H, H⁆ : Subgroup ↥L).subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    ∃ χ : ↥H →* ℂˣ,
      (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) = (θ : ClassFunction ↥H ℂ) := by
  classical
  have hsubgroupOf_eq :
      ((⁅H, H⁆ : Subgroup ↥L).subgroupOf H) = _root_.commutator ↥H := by
    rw [← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  let q : ↥H →* Abelianization ↥H := Abelianization.of
  have hq_surj : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥H) y
    exact ⟨x, rfl⟩
  have hker_q :
      ((q.ker : Subgroup ↥H) : Set ↥H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro x hx
    apply hker
    have hxcomm : x ∈ _root_.commutator ↥H := by
      rwa [show q.ker = _root_.commutator ↥H by
        change Abelianization.of.ker = _root_.commutator ↥H
        exact Abelianization.ker_of ↥H] at hx
    rwa [hsubgroupOf_eq]
  obtain ⟨θbar, hθbar⟩ := exists_compHom_eq_of_subset_characterKernel hq_surj θ hker_q
  have : Finite (Abelianization ↥H) := Finite.of_surjective q hq_surj
  obtain ⟨χbar, hχbar⟩ :=
    θbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  refine ⟨χbar.comp q, ?_⟩
  rw [← ClassFunction.compHom_linearIrreducibleCharacter, hχbar, hθbar]

/-- Every member of `Y = S(H')` is induced from a nontrivial linear character of `H`. -/
theorem exists_linear_source_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  rw [Yset, SsubFiltration] at hφ
  obtain ⟨θ, hθ_ne, hker, hφ⟩ := hφ
  obtain ⟨χ, hχθ⟩ := hyp.exists_linearIrreducibleCharacter_eq_of_YsetSource hker
  refine ⟨χ, ?_, ?_⟩
  · intro hχ
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hχθ]
    exact congrArg (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ))
      ((linearIrreducibleCharacter_eq_trivial_iff (χ := χ)).mpr hχ)
  · rw [hφ, ← hχθ]

/-- `Y = S(H')` is exactly the image of the nontrivial linear characters of `H` under induction. -/
theorem mem_Yset_iff_exists_linear_source
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {φ : ClassFunction ↥L ℂ} :
    φ ∈ hyp.Yset ↔ ∃ χ : ↥H →* ℂˣ, χ ≠ 1 ∧
      φ = ClassFunction.induce H
        (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) := by
  constructor
  · exact hyp.exists_linear_source_of_mem_Yset
  · rintro ⟨χ, hχ_ne, rfl⟩
    exact hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne

/-- Every `Y = S(H')` member has degree `|W₁|` (`Ind_H^L` of a degree-`1` source of `H`).  The
common degree of the equal-degree `Y`-family; used for the equal-degree difference support
(`sMember_diffSupport_of_charValue_eq`) in the (6.8.1) `himg_ortho`. -/
theorem Yset_apply_one (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
  obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  simpa [linearIrreducibleCharacter_coe] using
    hyp.induce_apply_one_eq_card_W1_of_degree_one
      (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)

/-- If an index family covers all nontrivial linear sources after induction, its induced range is
exactly `Y = S(H')`.

This is the orbit-representative form needed for (6.8): the family need only hit each induced
character in `Y`, not each nontrivial linear source before quotienting by `L`-conjugacy. -/
theorem range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {ι : Type*}
    (χ : ι → (↥H →* ℂˣ)) (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η)) :
    Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  ext φ
  constructor
  · rintro ⟨j, rfl⟩
    simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset (hχ_ne j)
  · intro hφ
    obtain ⟨η, hη_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    obtain ⟨j, hηj⟩ := hχ_cover η hη_ne
    refine ⟨j, ?_⟩
    rw [hφeq, linearIrreducibleCharacter_coe]
    exact hηj

/-- There are finitely many linear characters `Γ →* ℂˣ` for a finite group `Γ`.

Local to §8 because the immediate consumer is the finiteness of `Y = S(H')`; a more global API can
move this later if it gets reused outside the Peterfalvi assembly. -/
theorem finite_linearCharacters_of_finite {Γ : Type*} [Group Γ] [Finite Γ] :
    Finite (Γ →* ℂˣ) := by
  have : Finite (IrreducibleCharacter Γ) := finite_irreducibleCharacter (G := Γ)
  exact Finite.of_injective (linearIrreducibleCharacter (H := Γ))
    linearIrreducibleCharacter_injective

/-- `Y = S(H')` is finite: it is covered by inducing the finite set of nontrivial
linear source characters of `H`. -/
theorem Yset_finite (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Finite := by
  classical
  have : Finite (↥H →* ℂˣ) := finite_linearCharacters_of_finite (Γ := ↥H)
  let T : Set (↥H →* ℂˣ) := {χ | χ ≠ 1}
  refine ((Set.toFinite T).image
    (fun χ => ClassFunction.induce H (linearClassFunction χ))).subset ?_
  intro φ hφ
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  refine ⟨χ, hχ_ne, ?_⟩
  rw [hφeq, linearIrreducibleCharacter_coe]

/-- Every member of `Y = S(H')` is irreducible. -/
theorem isIrreducibleCharacter_of_mem_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    IsIrreducibleCharacter φ := by
  obtain ⟨χ, hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [hφeq]
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one χ) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne)

/-- Disjoint families of irreducible characters are orthogonal after passing to their
integer spans. -/
theorem inner_eq_zero_of_mem_span_of_disjoint_irreducible
    {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]
    {X Y : Set (ClassFunction Γ ℂ)}
    (hXirr : ∀ χ ∈ X, IsIrreducibleCharacter χ)
    (hYirr : ∀ η ∈ Y, IsIrreducibleCharacter η)
    (hdisj : Disjoint X Y) :
    ∀ u ∈ Submodule.span ℤ X, ∀ v ∈ Submodule.span ℤ Y,
      ClassFunction.inner u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem χ hχ =>
      intro v hv
      refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan ?_ hv
      intro η hη
      have hχη : χ ≠ η := by
        intro h
        exact (Set.disjoint_left.mp hdisj) hχ (by simpa [← h] using hη)
      have hχirr : IsIrreducibleCharacter χ := hXirr χ hχ
      have hηirr : IsIrreducibleCharacter η := hYirr η hη
      have hneq :
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ≠ ⟨η, hηirr⟩ := by
        intro h
        exact hχη (congrArg Subtype.val h)
      simpa [hneq] using
        irreducibleCharacter_inner_eq_ite
          (⟨χ, hχirr⟩ : IrreducibleCharacter Γ) ⟨η, hηirr⟩
  | zero =>
      intro v _hv
      exact ClassFunction.inner_zero_left v
  | add x y _hx _hy ihx ihy =>
      intro v hv
      rw [ClassFunction.inner_add_left, ihx v hv, ihy v hv, zero_add]
  | smul a x _hx ih =>
      intro v hv
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih v hv, mul_zero]

/-- Enumerating `Yset` gives nontrivial linear source representatives for its induced members.

The returned family is indexed by `Fin n`, covers `Yset` after induction, and is pairwise
non-`L`-conjugate.  The cardinal lower bound is kept as an explicit input because the later
coherence engine requires `2 ≤ n`. -/
theorem exists_Yset_linearRepresentativeFamily
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    ∃ (n : ℕ) (_ : NeZero n) (χ : Fin n → ↥H →* ℂˣ),
      2 ≤ n ∧
      (∀ j, χ j ≠ 1) ∧
      (∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
        ClassFunction.induce H (linearClassFunction (χ j)) =
          ClassFunction.induce H (linearClassFunction η)) ∧
      (∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
        IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
          linearIrreducibleCharacter (χ j)) ∧
      Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) = hyp.Yset := by
  classical
  obtain ⟨n, ζ, hζinj, hζrange⟩ :=
    exists_finEnum_irreducible (hyp.Yset_finite)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
  have hζmem : ∀ j, (ζ j : ClassFunction ↥L ℂ) ∈ hyp.Yset := by
    intro j
    rw [← hζrange]
    exact Set.mem_range_self j
  choose χ hχ_ne hχeq using fun j => hyp.exists_linear_source_of_mem_Yset (hζmem j)
  have hindRange : Set.range (fun j => ClassFunction.induce H (linearClassFunction (χ j))) =
      hyp.Yset := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      have hζeq :
          (ζ j : ClassFunction ↥L ℂ) =
            ClassFunction.induce H (linearClassFunction (χ j)) := by
        simpa [linearIrreducibleCharacter_coe] using hχeq j
      change ClassFunction.induce H (linearClassFunction (χ j)) ∈ hyp.Yset
      rw [← hζeq]
      exact hζmem j
    · intro hφ
      rw [← hζrange] at hφ
      obtain ⟨j, hj⟩ := hφ
      refine ⟨j, ?_⟩
      rw [← hj]
      simpa [linearIrreducibleCharacter_coe] using (hχeq j).symm
  have hcover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η) := by
    intro η hη_ne
    have hmem : ClassFunction.induce H (linearClassFunction η) ∈ hyp.Yset := by
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_linearIrreducibleCharacter_mem_Yset hη_ne
    rw [← hindRange] at hmem
    exact hmem
  have hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j) := by
    intro i j hij g hconj
    apply hij
    apply hζinj
    apply IrreducibleCharacter.ext
    have hind :
        ClassFunction.induce H
            (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
          ClassFunction.induce H
            (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      (induce_eq_induce_iff_conj
        (G := ↥L) (H := H)
        (linearIrreducibleCharacter (χ i))
        (linearIrreducibleCharacter (χ j))).mpr ⟨g, hconj⟩
    rw [hχeq i, hχeq j]
    exact hind
  have hcoeinj : Function.Injective (fun j => (ζ j : ClassFunction ↥L ℂ)) := by
    intro i j hij
    exact hζinj (IrreducibleCharacter.ext hij)
  have hncard : hyp.Yset.ncard = n := by
    rw [← hζrange, Set.ncard_range_of_injective hcoeinj, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hn2 : 2 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  exact ⟨n, inferInstance, χ, hn2, hχ_ne, hcover, hpairwise, hindRange⟩

/-- `Y = S(H')` coherence from finite orbit representatives of nontrivial linear characters.

The caller supplies representatives whose induced characters cover `Y`, together with the usual
pairwise non-`L`-conjugacy input that makes the constructed family orthonormal.  The exact range
equality rewrites `coherentYFamily` from the constructed range to `hyp.Yset`. -/
noncomputable def coherentYset_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hχ_cover : ∀ η : ↥H →* ℂˣ, η ≠ 1 → ∃ j,
      ClassFunction.induce H (linearClassFunction (χ j)) =
        ClassFunction.induce H (linearClassFunction η))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  have hcoh := hyp.coherentYFamily_of_pairwiseNonconj hn χ hχ_ne hpairwise
  have hrange :=
    hyp.range_induce_linearIrreducibleCharacter_eq_Yset_of_induce_surjective χ hχ_ne hχ_cover
  simpa [hrange] using hcoh

/-- `Y = S(H')` coherence from the finite `Yset` representative construction.

This packages `exists_Yset_linearRepresentativeFamily` with the concrete coherence engine; the
remaining downstream input is the cardinal lower bound `2 ≤ |Y|`. -/
noncomputable def coherentYset_of_two_le_ncard
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] (hYtwo : 2 ≤ hyp.Yset.ncard) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  choose n hnzero χ hn2 hχ_ne hχ_cover hpairwise _hrange using
    hyp.exists_Yset_linearRepresentativeFamily hYtwo
  letI : NeZero n := hnzero
  exact hyp.coherentYset_of_pairwiseNonconj hn2 χ hχ_ne hχ_cover hpairwise

/-- `Y = S(H')` is nonempty.

The nontrivial nilpotent group `H` is solvable, hence has proper commutator subgroup.  The
abelianization therefore has a nontrivial linear character, whose induced character lies in
`Yset`. -/
theorem Yset_nonempty (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    hyp.Yset.Nonempty := by
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have hcomm : _root_.commutator ↥H ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥H)).ne
  obtain ⟨χ, hχ_ne⟩ := exists_monoidHom_units_ne_one_of_commutator_ne_top hcomm
  exact ⟨ClassFunction.induce H (linearClassFunction χ),
    by simpa [linearIrreducibleCharacter_coe] using
      hyp.induce_linearIrreducibleCharacter_mem_Yset hχ_ne⟩

/-- `Y = S(H')` contains no real characters.

Each member of `Yset` is an irreducible induced character of degree `|W₁|`; since `W₁` is
nontrivial this degree is not `1`, so the member is not the trivial irreducible character.  Odd
order of `L` then gives non-realness by Peterfalvi (1.1). -/
theorem Yset_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Yset := by
  intro φ hφ hreal
  let η : IrreducibleCharacter ↥L := ⟨φ, hyp.isIrreducibleCharacter_of_mem_Yset hφ⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    obtain ⟨χ, _hχ_ne, hφeq⟩ := hyp.exists_linear_source_of_mem_Yset hφ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) := by
      rw [hφeq]
      simpa [linearIrreducibleCharacter_coe] using
        hyp.induce_apply_one_eq_card_W1_of_degree_one
          (linearIrreducibleCharacter χ) (linearIrreducibleCharacter_apply_one χ)
    have hcard_ne : (Nat.card hyp.W1 : ℂ) ≠ 1 := by
      have hcard_nat : Nat.card hyp.W1 ≠ 1 := by
        intro hcard
        exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp hcard)
      exact_mod_cast hcard_nat
    exact hcard_ne (hφ_one.symm.trans hφ_one_triv)
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


