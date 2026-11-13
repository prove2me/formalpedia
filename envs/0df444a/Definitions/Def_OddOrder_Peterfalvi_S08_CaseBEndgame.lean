-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEndgame
-- name    : OddOrder_Peterfalvi_S08_CaseBEndgame
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:11:27.301865+00:00
-- url     : https://prove2.me/theorems/07b7dad6-7e90-443c-9e25-222505b3cc83
-- title:
--   Peterfalvi §8: case (B) endgame, $S$ is coherent (the (6.8.3) extension)
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, pp. 30-37, the (6.8.3) step of the (6.8) coherence capstone in case (B) ($Z=W_2$ central in $H$). (6.8.3) is a uniform argument across cases (A) and (B): assuming $S$ is not coherent, one gets a break pair $S_2=\{\psi,\bar\psi\}\subseteq S$ with $X\cup Y\subseteq S_1\subseteq S$ coherent, and derives a contradiction.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBEndgame.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBEndgame.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2

namespace OddOrder.Peterfalvi.S08

/-- **(6.8.3) arithmetic core, case (B).**  The numeric contradiction closing the (6.8.3) extension
in case (B).  From the break-pair (5.6) bound `∑_{χ∈X} χ(1)²/‖χ‖² < 2ψ(1)η₁(1)` — i.e.
`|W₁|·|H:Z|·(|Z|−1) ≤ 2·|W₁|²·d` with `ψ(1) = |W₁|·d`, `η₁(1) = |W₁|` — together with [Is] Cor 2.30
`d² ≤ |H:Z|` (valid since `Z` is central in `H`) and the case-(B) fixed-point-free bound
`|H:Z| ≥ (2|W₁|+1)²` (`W₁` acts FPF on `H/H′` and `H′/Z`), one derives `|H:Z| ≤ 2|W₁|d ≤ 4|W₁|²`
(dropping the `|Z|−1 ≥ 1` factor, then `d ≤ 2|W₁|` from `d² ≤ |H:Z| ≤ 2|W₁|d`), contradicting
`(2|W₁|+1)² = 4|W₁|² + 4|W₁| + 1 ≤ |H:Z|`.

Here `w1 = |W₁|`, `d = θ(1)` (the degree of the `H`-source of `ψ`), `hZ = |H:Z|`, `cZ = |Z|`.
The hypothesis `2 ≤ cZ` holds because `Z ≠ 1` (so `|Z| ≥ 2`); only the factor `|Z|−1 ≥ 1` is used,
so unlike case (A) no lower bound on `|Z|` beyond nontriviality is needed (the FPF strength sits in
`hfpf` on `|H:Z|` instead).  Compare `false_of_centralCommutator_break_arith` (case A). -/
theorem false_of_w2_break_arith {w1 d hZ cZ : ℕ}
    (hw1 : 1 ≤ w1) (hd : 1 ≤ d) (hdsq : d ^ 2 ≤ hZ) (hcZ : 2 ≤ cZ)
    (hfpf : (2 * w1 + 1) ^ 2 ≤ hZ)
    (hbreak : w1 * hZ * (cZ - 1) ≤ 2 * w1 ^ 2 * d) : False := by
  -- the factor `|Z|−1` is at least `1`
  have hm1 : 1 ≤ cZ - 1 := by omega
  -- drop the `(cZ−1)` factor: `w1·hZ ≤ w1·hZ·(cZ−1) ≤ 2·w1²·d`
  have hwz : w1 * hZ ≤ 2 * w1 ^ 2 * d :=
    le_trans (le_mul_of_one_le_right (Nat.zero_le _) hm1) hbreak
  -- cancel `w1`: `hZ ≤ 2·w1·d`
  have hzle : hZ ≤ 2 * w1 * d := by
    refine Nat.le_of_mul_le_mul_left ?_ hw1
    calc w1 * hZ ≤ 2 * w1 ^ 2 * d := hwz
      _ = w1 * (2 * w1 * d) := by ring
  -- cancel `d`: `d ≤ 2·w1` (from `d² ≤ hZ ≤ 2·w1·d`)
  have hdle : d ≤ 2 * w1 := by
    refine Nat.le_of_mul_le_mul_right ?_ hd
    calc d * d = d ^ 2 := (sq d).symm
      _ ≤ hZ := hdsq
      _ ≤ 2 * w1 * d := hzle
  -- hence `hZ ≤ 2·w1·d ≤ 4·w1²`
  have hz4 : hZ ≤ 4 * w1 ^ 2 := by
    calc hZ ≤ 2 * w1 * d := hzle
      _ ≤ 2 * w1 * (2 * w1) := by gcongr
      _ = 4 * w1 ^ 2 := by ring
  -- contradiction: `(2·w1+1)² = 4·w1² + 4·w1 + 1 ≤ hZ ≤ 4·w1²`
  have hcontra : (2 * w1 + 1) ^ 2 ≤ 4 * w1 ^ 2 := le_trans hfpf hz4
  have hexp : (2 * w1 + 1) ^ 2 = 4 * w1 ^ 2 + 4 * w1 + 1 := by ring
  rw [hexp] at hcontra
  omega

/-- **(6.8.3) case-(B) fixed-point-free bound** `(2|W₁|+1)² ≤ |H:Z|`.
In case (B), `W₁` acts fixed-point-freely on `H/H′` and on `H′/Z` (`Z = W₂ ≤ H′`); with all orders
odd this forces `|H:H′|, |H′:Z| ≥ 2|W₁|+1` (`two_mul_add_one_le_of_odd_dvd`), and the index
multiplicativity `|H:Z| = |H:H′|·|H′:Z|` for the chain `Z ≤ H′ ≤ H` gives the square bound.

Stated over the two intermediate index factors as oddness + `card_modEq_one` divisibility
hypotheses (`w1 ∣ idx − 1`, the fixed-point-free outputs) together with the index product, so the
group-theoretic inputs (the two fixed-point-free actions and the chain index identity) are isolated
as named obligations for the case-(B) (6.8.3) extension.  This supplies the `hfpf` hypothesis of
`false_of_w2_break_arith` (with `idxHZ = |H:Z|`).  Mirrors the *single*-factor case-(A) bound
`2|W₁| ≤ |Z| − 1` (`centralCommutator_card_subgroupOf_lower`), which only needs FPF on `Z`
itself. -/
theorem two_mul_add_one_sq_le_of_two_fpf_factors {w1 idxHHc idxHcZ idxHZ : ℕ}
    (hw1odd : Odd w1)
    (h1odd : Odd idxHHc) (h1gt : 1 < idxHHc) (h1dvd : w1 ∣ idxHHc - 1)
    (h2odd : Odd idxHcZ) (h2gt : 1 < idxHcZ) (h2dvd : w1 ∣ idxHcZ - 1)
    (hprod : idxHZ = idxHHc * idxHcZ) :
    (2 * w1 + 1) ^ 2 ≤ idxHZ := by
  have h1 : 2 * w1 + 1 ≤ idxHHc := two_mul_add_one_le_of_odd_dvd hw1odd h1odd h1dvd h1gt
  have h2 : 2 * w1 + 1 ≤ idxHcZ := two_mul_add_one_le_of_odd_dvd hw1odd h2odd h2dvd h2gt
  calc (2 * w1 + 1) ^ 2 = (2 * w1 + 1) * (2 * w1 + 1) := by ring
    _ ≤ idxHHc * idxHcZ := Nat.mul_le_mul h1 h2
    _ = idxHZ := hprod.symm

/-- **(6.8.3) case-(B) FPF index bound over a subgroup chain.**  The group-theoretic bridge from the
abstract FPF bound `two_mul_add_one_sq_le_of_two_fpf_factors` to a concrete chain `W ≤ M ≤ K` in a
finite group `K` of odd order (the Sibley instance is `K = ↥H`, `M = H′ = [H,H]`, `W = W₂` with
`w1 = |W₁|`): all section indices `|K:M|`, `|M:W|` are odd (dividing the odd `|K|`), so the two
fixed-point-free divisibilities `w1 ∣ |K:M| − 1` and `w1 ∣ |M:W| − 1` (the `card_modEq_one` outputs)
force `|K:M|, |M:W| ≥ 2·w1 + 1` and `|K:W| = |K:M|·|M:W| ≥ (2·w1+1)²`.

Only the two fixed-point-free divisibilities and the two section-nontriviality facts (`1 < |K:M|`,
i.e. `M < K`; `1 < |M:W|`, i.e. `W < M`) remain as inputs — the oddness and the chain index identity
are discharged here from `Odd (Nat.card K)`. -/
theorem two_mul_add_one_sq_le_index_of_chain {K : Type*} [Group K] [Finite K]
    {W M : Subgroup K} (hWM : W ≤ M) (hKodd : Odd (Nat.card K))
    {w1 : ℕ} (hw1odd : Odd w1)
    (hMgt : 1 < M.index) (hWMgt : 1 < W.relIndex M)
    (h1dvd : w1 ∣ M.index - 1) (h2dvd : w1 ∣ W.relIndex M - 1) :
    (2 * w1 + 1) ^ 2 ≤ W.index := by
  -- every divisor of the odd `|K|` is odd
  have oddDvd : ∀ {a : ℕ}, a ∣ Nat.card K → Odd a := by
    intro a ha
    rcases ha with ⟨c, hc⟩
    rcases Nat.even_or_odd a with he | ho
    · exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hKodd)
    · exact ho
  -- `|M:W|` divides `|K|` (via `|K|` of the subgroup `M`)
  have hMcard : Nat.card ↥M ∣ Nat.card K := Subgroup.card_subgroup_dvd_card M
  have h1odd : Odd M.index := oddDvd M.index_dvd_card
  have h2odd : Odd (W.relIndex M) :=
    oddDvd (dvd_trans ((W.subgroupOf M).index_dvd_card) hMcard)
  -- chain index identity `|K:W| = |K:M|·|M:W|`
  have hprod : W.index = M.index * W.relIndex M := by
    rw [mul_comm]; exact (Subgroup.relIndex_mul_index hWM).symm
  exact two_mul_add_one_sq_le_of_two_fpf_factors hw1odd h1odd hMgt h1dvd h2odd hWMgt h2dvd hprod

/-- **(6.8.3) case-(B) fixed-point-free divisibility from a fixed-point bound.**  The mechanical
core of the case-(B) `hfpf` derivation: a finite group `W` acting on a finite group `H` with
`(|W|, |H|) = 1`, whose nonidentity elements fix only points of a normal `W`-invariant subgroup
`M` (`a • x = x → x ∈ M`), induces a *fixed-point-free* action on the quotient `H ⧸ M`
(`IsFrobeniusAction.quotient_of_fixedPoints_le`); Burnside's `card_modEq_one` then gives
`|H : M| ≡ 1 (mod |W|)`, i.e. `|W| ∣ |H : M| − 1`.

Applied twice in the (6.8.3) extension with `W = W₁`: once to `M = H′ = [H,H]` (the fixed points
`C_H(W₁) = W₂ ⊆ H′`), giving `|W₁| ∣ |H:H′| − 1`; once to the restricted action on `H′` with
`M = W₂`, giving `|W₁| ∣ |H′:W₂| − 1`.  These are exactly the two divisibility inputs of
`two_mul_add_one_sq_le_index_of_chain`.  The remaining residual is the certain-type fixed-point
bridge `C_H(W₁) = W₂` (`S06 …centralizer_W2`) translating into the `hfix` hypothesis here. -/
theorem W1_dvd_index_of_fixedPoints_le {H W : Type*}
    [Group H] [Finite H] [Group W] [Finite W] [MulDistribMulAction W H]
    (hCop : Nat.Coprime (Nat.card W) (Nat.card H))
    (M : Subgroup H) [M.Normal] (hMinv : ∀ a : W, ∀ m ∈ M, a • m ∈ M)
    (hfix : ∀ a : W, a ≠ 1 → ∀ x : H, a • x = x → x ∈ M) :
    Nat.card W ∣ M.index - 1 := by
  let : MulDistribMulAction W (H ⧸ M) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction M hMinv
  have hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusAction W (H ⧸ M) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le hCop M hMinv hfix
  have : Fintype W := Fintype.ofFinite _
  have : Fintype (H ⧸ M) := Fintype.ofFinite _
  have hmod : Nat.card (H ⧸ M) ≡ 1 [MOD Nat.card W] := by
    simpa only [Fintype.card_eq_nat_card] using hFrob.card_modEq_one
  have hidx : M.index = Nat.card (H ⧸ M) := rfl
  rw [hidx]
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm

/-- **(6.8.3) case-(B) `W₁`-FPF divisibility from the centralizer condition.**  The concrete-action
instance of `W1_dvd_index_of_fixedPoints_le` for the `W₁`-conjugation action on `H`: if `M` is a
*characteristic* subgroup of `H` containing every `x ∈ H` that commutes with some nonidentity
`a ∈ W₁` (the certain-type fixed-point condition `C_H(W₁) = W₂ ⊆ M`), then `|W₁| ∣ |H : M| − 1`.

The conjugation action `a • x = (a:L)·(x:L)·(a:L)⁻¹` is set up internally (so neither the statement
nor
the caller mentions it); a fixed point `a • x = x` unfolds — via
`toMulAut`/`MulAut.conjNormal_apply`
— to `(a:L)·(x:L) = (x:L)·(a:L)`, discharging the `hfix` hypothesis of
`W1_dvd_index_of_fixedPoints_le` from `hcomm`.  `M`-invariance comes from `M` characteristic
(the `toMulAut` map-membership trick).  Applied with `M = [H,H]` and `hcomm` supplied by
`S06 …centralizer_W2`, this is the first FPF divisibility `|W₁| ∣ |H:H′| − 1`. -/
theorem caseB_W1_dvd_index_of_centralizer_le {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} {H : Subgroup ↥L} [H.Normal] (W1 : Subgroup ↥L)
    (hCop : Nat.Coprime (Nat.card ↥W1) (Nat.card ↥H))
    (M : Subgroup ↥H) [M.Characteristic]
    (hcomm : ∀ a : ↥W1, a ≠ 1 → ∀ x : ↥H,
      (a : ↥L) * (x : ↥L) = (x : ↥L) * (a : ↥L) → x ∈ M) :
    Nat.card ↥W1 ∣ M.index - 1 := by
  have : Finite ↥H := inferInstance
  have : Finite ↥W1 := inferInstance
  have : M.Normal := inferInstance
  let act : MulDistribMulAction ↥W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp W1.subtype)
  -- the conjugation action unfolds to `(a:L)·(x:L)·(a:L)⁻¹`
  have hsmul : ∀ (a : ↥W1) (x : ↥H), ((a • x : ↥H) : ↥L) = (a : ↥L) * (x : ↥L) * (a : ↥L)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥H) = (MulDistribMulAction.toMulAut ↥W1 ↥H a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    change ((MulAut.conjNormal (H := H) (W1.subtype a)) x : ↥L) = _
    rw [MulAut.conjNormal_apply]; rfl
  -- `M` characteristic ⟹ invariant under the action
  have hMinv : ∀ a : ↥W1, ∀ m ∈ M, a • m ∈ M := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp ‹M.Characteristic›
      (MulDistribMulAction.toMulAut ↥W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥W1 ↥H a).toMonoidHom m ∈ M := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- a fixed point of `a` commutes with `a`, so lands in `M` by `hcomm`
  have hfix : ∀ a : ↥W1, a ≠ 1 → ∀ x : ↥H, a • x = x → x ∈ M := by
    intro a ha x hx
    refine hcomm a ha x ?_
    have hc := hsmul a x
    rw [hx] at hc
    exact mul_inv_eq_iff_eq_mul.mp hc.symm
  exact W1_dvd_index_of_fixedPoints_le hCop M hMinv hfix

/-- **(6.8.3) case-(B) first FPF divisibility** `|W₁| ∣ |H:H′| − 1`, fully from the Sibley
certain-type data.  Discharges the `hcomm` hypothesis of `caseB_W1_dvd_index_of_centralizer_le` at
`M = [H,H]` from the certain-type centralizer datum `cert.centralizer_W2` (`C_L(a) ⊓ K = W₂`) and
`W₂ ⊆ ⁅H,H⁆`: if `x ∈ H` commutes with a nonidentity `a ∈ W₁`, then `(x:L) ∈ C_L(a) ⊓ K = W₂ ⊆
⁅H,H⁆`, so `x ∈ ([H,H]).subgroupOf H = commutator ↥H` (`commutator_subgroupOf_self`).

The `cert`/`hK`/`hW1`/`hW2`/`hcop` arguments are exactly the case-(c2) projection of `hyp.cases`
(`h46.toCertainTypeHypothesis`, `h46.K = H`, `h46.W1 = W₁`, `h46.W2 ⊆ ⁅H,H⁆`, the Hall
coprimality), mirroring `inertia_eq_H_of_c2`. -/
theorem caseB_W1_dvd_index_commutator {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)] (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1)) :
    Nat.card ↥hyp.W1 ∣ (commutator ↥H).index - 1 := by
  let : H.Normal := hyp.H_normal
  refine caseB_W1_dvd_index_of_centralizer_le hyp.W1 hcop.symm (commutator ↥H) ?_
  intro a ha x hcomm
  -- `(x:L)` commutes with `(a:L)`, so lies in `C_L(a)`
  have hxcen : (x : ↥L) ∈ Subgroup.centralizer ({(a : ↥L)} : Set ↥L) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have haW1 : (a : ↥L) ∈ cert.W1 := by rw [hW1]; exact a.2
  have hane : (a : ↥L) ≠ 1 := fun h => ha (OneMemClass.coe_eq_one.mp h)
  -- `(x:L) ∈ C_L(a) ⊓ K = W₂`
  have hxW2 : (x : ↥L) ∈ cert.W2 := by
    rw [← cert.centralizer_W2 (a : ↥L) haW1 hane]
    exact Subgroup.mem_inf.mpr ⟨hxcen, by rw [hK]; exact x.2⟩
  -- `W₂ ⊆ ⁅H,H⁆`, so `x ∈ commutator ↥H`
  rw [← commutator_subgroupOf_self]
  exact Subgroup.mem_subgroupOf.mpr (hW2 hxW2)

/-- **(6.8.3) case-(B) second FPF divisibility** `|W₁| ∣ |H′:W₂| − 1`, from the Sibley data.
The `H′/W₂` companion of `caseB_W1_dvd_index_commutator`: `W₁` acts (by conjugation) on
`H′ = commutator ↥H` (restricting the `H`-action, `H′` characteristic), and its fixed points lie in
`W₂` (`cert.centralizer_W2`), so `|W₁| ∣ |H′:W₂| − 1` by `W1_dvd_index_of_fixedPoints_le`.  `W₂`'s
`W₁`-invariance is automatic from `W₂ ≤ Z(↥L)` (central elements are fixed by conjugation), and its
normality from the same.  With `caseB_W1_dvd_index_commutator` this feeds
`two_mul_add_one_sq_le_index_of_chain` to give the full `hfpf` bound `(2|W₁|+1)² ≤ |H:W₂|`. -/
theorem caseB_W1_dvd_relIndex_commutator {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)] (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (_hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hW2cen : cert.W2 ≤ Subgroup.center ↥L)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1)) :
    Nat.card ↥hyp.W1 ∣ (cert.W2.subgroupOf H).relIndex (commutator ↥H) - 1 := by
  let : H.Normal := hyp.H_normal
  have : Finite ↥H := inferInstance
  have : Finite ↥hyp.W1 := inferInstance
  -- `W₂` is normal in `↥L` (it is central)
  have hW2normalL : cert.W2.Normal :=
    { conj_mem := fun n hn g => by
        have hc := (Subgroup.mem_center_iff).mp (hW2cen hn)
        have hgn : g * (n : ↥L) * g⁻¹ = n := by
          rw [hc g, mul_assoc, mul_inv_cancel, mul_one]
        rw [hgn]; exact hn }
  -- the `W₁`-conjugation action on `H`
  let actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hsmulH : ∀ (a : ↥hyp.W1) (x : ↥H),
      ((a • x : ↥H) : ↥L) = (a : ↥L) * (x : ↥L) * (a : ↥L)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥H) = (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    change ((MulAut.conjNormal (H := H) (hyp.W1.subtype a)) x : ↥L) = _
    rw [MulAut.conjNormal_apply]; rfl
  -- `commutator ↥H` is `W₁`-invariant (characteristic)
  have hcommInv : ∀ a : ↥hyp.W1, ∀ m ∈ commutator ↥H, a • m ∈ commutator ↥H := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥H).Characteristic) (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a)
    have hmem : (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a).toMonoidHom m ∈ commutator ↥H := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  -- the restricted `W₁`-action on `H′ = commutator ↥H`
  let actHp : MulDistribMulAction ↥hyp.W1 ↥(commutator ↥H) :=
    OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantSubgroupMulDistribMulAction
      (commutator ↥H) hcommInv
  have : Finite ↥(commutator ↥H) := inferInstance
  -- the `H′`-smul coerces to the `H`-action on the underlying element (definitional)
  have hsmulHp : ∀ (a : ↥hyp.W1) (y : ↥(commutator ↥H)),
      ((a • y : ↥(commutator ↥H)) : ↥H) = a • (y : ↥H) := fun _ _ => rfl
  have hW2subH_normal : (cert.W2.subgroupOf H).Normal := hW2normalL.subgroupOf H
  have hMnorm : ((cert.W2.subgroupOf H).subgroupOf (commutator ↥H)).Normal :=
    hW2subH_normal.subgroupOf (commutator ↥H)
  have hCop' : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥(commutator ↥H)) :=
    hcop.symm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
  -- `W₂` central ⟹ conjugation fixes its elements ⟹ `M`-invariance
  have hMinv : ∀ a : ↥hyp.W1, ∀ m ∈ (cert.W2.subgroupOf H).subgroupOf (commutator ↥H),
      a • m ∈ (cert.W2.subgroupOf H).subgroupOf (commutator ↥H) := by
    intro a m hm
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hm ⊢
    rw [hsmulHp a m, hsmulH a (m : ↥H)]
    exact hW2normalL.conj_mem _ hm (a : ↥L)
  -- fixed points of `W₁` on `H′` lie in `W₂` (`centralizer_W2`)
  have hfix : ∀ a : ↥hyp.W1, a ≠ 1 → ∀ y : ↥(commutator ↥H),
      a • y = y → y ∈ (cert.W2.subgroupOf H).subgroupOf (commutator ↥H) := by
    intro a ha y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hcoe : (((a • y : ↥(commutator ↥H)) : ↥H) : ↥L)
        = (a : ↥L) * ((y : ↥H) : ↥L) * (a : ↥L)⁻¹ := by
      rw [hsmulHp a y, hsmulH a (y : ↥H)]
    rw [hy] at hcoe
    have hcomm : ((y : ↥H) : ↥L) * (a : ↥L) = (a : ↥L) * ((y : ↥H) : ↥L) :=
      (mul_inv_eq_iff_eq_mul.mp hcoe.symm).symm
    have haW1 : (a : ↥L) ∈ cert.W1 := by rw [hW1]; exact a.2
    have hane : (a : ↥L) ≠ 1 := fun h => ha (OneMemClass.coe_eq_one.mp h)
    rw [← cert.centralizer_W2 (a : ↥L) haW1 hane]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm, ?_⟩
    rw [hK]; exact (y : ↥H).2
  have hdvd := W1_dvd_index_of_fixedPoints_le hCop'
    ((cert.W2.subgroupOf H).subgroupOf (commutator ↥H)) hMinv hfix
  exact hdvd

/-- **(6.8.3) case-(B) full FPF bound** `(2|W₁|+1)² ≤ |H:W₂|`, assembled from the Sibley data.
Combines the two FPF divisibilities `caseB_W1_dvd_index_commutator` (H/H′) and
`caseB_W1_dvd_relIndex_commutator` (H′/W₂) through the chain bound
`two_mul_add_one_sq_le_index_of_chain`, discharging the group-order oddnesses from the odd order of
`L` (`card_L_odd`).  The two section-nontriviality facts `1 < |H:H′|` (`H` non-abelian) and
`1 < |H′:W₂|` (`W₂ ≠ H′`, the (6.8.3) `Z ≠ H′` case) remain as inputs — both are (6.8.3)-context
hypotheses.  This is exactly the `hfpf` input to `false_of_w2_break_arith` (with
`|H:W₂| = (cert.W2.subgroupOf H).index`). -/
theorem caseB_fpf_bound {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)] (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hW2cen : cert.W2 ≤ Subgroup.center ↥L)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    (hMgt : 1 < (commutator ↥H).index)
    (hWMgt : 1 < (cert.W2.subgroupOf H).relIndex (commutator ↥H)) :
    (2 * Nat.card ↥hyp.W1 + 1) ^ 2 ≤ (cert.W2.subgroupOf H).index := by
  let : H.Normal := hyp.H_normal
  have hW2le : cert.W2.subgroupOf H ≤ commutator ↥H := by
    rw [← commutator_subgroupOf_self]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hW2 (Subgroup.mem_subgroupOf.mp hx))
  have oddOf : ∀ {a : ℕ}, a ∣ Nat.card ↥L → Odd a := by
    intro a ha
    rcases ha with ⟨c, hc⟩
    rcases Nat.even_or_odd a with he | ho
    · exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hyp.card_L_odd)
    · exact ho
  have hKodd : Odd (Nat.card ↥H) := oddOf (Subgroup.card_subgroup_dvd_card H)
  have hw1odd : Odd (Nat.card ↥hyp.W1) := oddOf (Subgroup.card_subgroup_dvd_card hyp.W1)
  exact two_mul_add_one_sq_le_index_of_chain hW2le hKodd hw1odd hMgt hWMgt
    (caseB_W1_dvd_index_commutator hyp cert hK hW1 hW2 hcop)
    (caseB_W1_dvd_relIndex_commutator hyp cert hK hW1 hW2 hW2cen hcop)

end OddOrder.Peterfalvi.S08


