-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowCyclic
-- name    : OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowCyclic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:44:50.148511+00:00
-- url     : https://prove2.me/theorems/2a7ccc01-03fa-4d87-b866-7c0928735e09
-- title:
--   Peterfalvi (8.1)/(12.16): witness Sylow cyclic
-- statement:
--   Formalizes results used in the type I analysis, including Peterfalvi (8.1.b) for an arbitrary complement and the numeric input $4|K'|\le|K|$ of (8.1.c)/(12.16).
--
--   Main declarations: `exists_abelian_centralizer_le_of_isComplement` (Peterfalvi (8.1.b) for an arbitrary complement of `M_F`); `four_mul_card_Kprime_le` (Peterfalvi (8.1.c) → (12.16) numeric input: `4·|K'| ≤ |K|`).
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/WitnessSylowCyclic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/WitnessSylowCyclic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_CentralizerContainment
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowBasic

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Pointwise in
/-- **Peterfalvi (8.1.b) for an arbitrary complement of `M_F`.**  For a type-`F` group `M` with
kernel `K = M_F`, if `V` is *any* complement of `K` in `M`, then the `V`-centralizers of nontrivial
kernel elements all lie in a single abelian subgroup `W ≤ V` — the conjugate of the type-`F` datum's
`U₁` by the Schur–Zassenhaus element carrying the datum's complement `U` to `V`.  (Peterfalvi (8.1)
remark: "(b) holds whatever complement `U` is chosen".)

Used in (12.11): with `V = M ∩ L` (a complement of `K` by the first assertion `(12.11)`), both a
`p'`-subgroup `A ≤ M ∩ L` and the witness `x ∈ P₀ ⊆ M ∩ L` land in this abelian `W` (via
`C_K(A) ≠ 1` and `C_K(x) ≠ 1`), so `A` centralizes `x`. -/
theorem exists_abelian_centralizer_le_of_isComplement [Finite G] {M : Subgroup G}
    (hMsolv : Group.IsSolvable ↥M) (typeF : TypeFData M) {V : Subgroup G} (hV_le : V ≤ M)
    (hVcompl : Subgroup.IsComplement' (typeF.H.subgroupOf M) (V.subgroupOf M)) :
    ∃ W : Subgroup G, IsMulCommutative ↥W ∧
      ∀ y ∈ typeF.H, y ≠ 1 → V ⊓ Subgroup.centralizer ({y} : Set G) ≤ W := by
  classical
  have hHnormal : (typeF.H.subgroupOf M).Normal := by
    rw [typeF.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  have hcop : Nat.Coprime (Nat.card ↥(typeF.H.subgroupOf M)) (typeF.H.subgroupOf M).index := by
    rw [typeF.H_eq]; exact (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M).coprime_index
  -- Schur–Zassenhaus: `U` and `V` are conjugate in `↥M` by `n ∈ H = M_F`.
  have : Group.IsSolvable ↥M := hMsolv
  obtain ⟨n, hn_mem, hn_conj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) typeF.complement
      hVcompl
  set m : G := (n : G) with hm
  have hmH : m ∈ typeF.H := Subgroup.mem_subgroupOf.mp hn_mem
  have hmM : m ∈ M := n.2
  -- Bridge `↥M`-conjugation to ambient `G`: `U.map (conj m) = V`.
  have hbridge : M.subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj m).toMonoidHom.comp M.subtype := by
    ext a; simp [MulAut.conj_apply, hm, mul_assoc]
  have hUmV : typeF.U.map (MulAut.conj m).toMonoidHom = V := by
    have h1 := congrArg (Subgroup.map M.subtype) hn_conj
    rw [Subgroup.map_map, hbridge, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le typeF.U_le,
      Subgroup.map_subgroupOf_eq_of_le hV_le] at h1
    exact h1
  refine ⟨typeF.U1.map (MulAut.conj m).toMonoidHom, ⟨⟨?_⟩⟩, ?_⟩
  · -- `W = U₁ᵐ` is abelian (conjugate of abelian `U₁`).
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp ha
    obtain ⟨u', hu', hub⟩ := Subgroup.mem_map.mp hb
    have huu' : u * u' = u' * u := by
      have h := typeF.U1_commutative.is_comm.comm (⟨u, hu⟩ : ↥typeF.U1) ⟨u', hu'⟩
      simpa using congrArg Subtype.val h
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hua, ← hub, ← map_mul, ← map_mul, huu']
  · -- `V ⊓ C(y) ≤ W`: `v ∈ V = Uᵐ`, `v` centralizes `y`, so `u = vᵐ⁻¹ ∈ U ⊓ C(yᵐ⁻¹) ≤ U₁`.
    intro y hyH hy1 v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    rw [← hUmV] at hvV
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hvV
    apply Subgroup.mem_map_of_mem
    -- `y' = m⁻¹ y m ∈ H^#`.
    have hy'H : m⁻¹ * y * m ∈ typeF.H := by
      have hyM : y ∈ M := typeF.H_le hyH
      have hconj := hHnormal.conj_mem ⟨y, hyM⟩ (Subgroup.mem_subgroupOf.mpr hyH)
        ⟨m⁻¹, M.inv_mem hmM⟩
      have := Subgroup.mem_subgroupOf.mp hconj
      simpa [mul_assoc] using this
    have hy'1 : m⁻¹ * y * m ≠ 1 := by
      intro h; apply hy1
      have hyeq : y = m * (m⁻¹ * y * m) * m⁻¹ := by group
      rw [hyeq, h]; group
    -- `u` centralizes `m⁻¹ y m` because `mᵘ = (conj m) u` centralizes `y`.
    have hcvy : (m * u * m⁻¹) * y = y * (m * u * m⁻¹) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hvC
      simpa [MulAut.conj_apply] using h
    have hthis : m * (u * (m⁻¹ * y * m)) * m⁻¹ = m * ((m⁻¹ * y * m) * u) * m⁻¹ := by
      have hE : m * (u * (m⁻¹ * y * m)) * m⁻¹ = (m * u * m⁻¹) * y := by group
      have hE' : m * ((m⁻¹ * y * m) * u) * m⁻¹ = y * (m * u * m⁻¹) := by group
      rw [hE, hE', hcvy]
    have hu_cent : u ∈ Subgroup.centralizer ({m⁻¹ * y * m} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_left_cancel (mul_right_cancel hthis))
    exact typeF.centralizer_le_U1 (m⁻¹ * y * m) hy'H hy'1 (Subgroup.mem_inf.mpr ⟨hu, hu_cent⟩)

/-- A `p`-Hall subgroup `H` (its order having only `p`-primary divisors among `π = π(|H|)`) with
`p ∣ |H|` contains a Sylow `p`-subgroup of the ambient group `G`.

A Sylow `p`-subgroup `R` of `↥H` maps to a subgroup `R.map H.subtype ≤ H` of `G` of the same
order `p ^ v_p(|H|)`.  Since `H` is Hall, `p ∤ [G : H]`, so `v_p(|H|) = v_p(|G|)`; hence
`R.map H.subtype` is a Sylow `p`-subgroup of `G` contained in `H`. -/
theorem exists_sylow_le_of_hall [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H) (hp : p ∣ Nat.card ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ H := by
  classical
  -- A Sylow `p`-subgroup `R` of `↥H`.
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥H))
  -- The `p`-multiplicity of `|H|` equals that of `|G|`, because `H` is Hall and `p ∣ |H|`.
  have hfact : (Nat.card ↥H).factorization p = (Nat.card G).factorization p := by
    have hcop : Nat.Coprime (Nat.card ↥H) H.index := hHall.coprime_index
    have hp_notdvd : ¬ p ∣ H.index :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hp)
    have hidx0 : H.index.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_notdvd
    have hsplit : (Nat.card G).factorization p =
        (Nat.card ↥H).factorization p + H.index.factorization p := by
      rw [← H.card_mul_index, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
        Subgroup.index_ne_zero_of_finite]
      rfl
    rw [hsplit, hidx0, add_zero]
  -- `R.map H.subtype` is a `p ^ v_p(|G|)`-subgroup of `G`, i.e. a Sylow `p`-subgroup.
  have hcardR : Nat.card ↥(R : Subgroup ↥H) = p ^ (Nat.card G).factorization p := by
    rw [R.card_eq_multiplicity, hfact]
  have hcardQ : Nat.card ↥((R : Subgroup ↥H).map H.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hcardR]
  exact ⟨Sylow.ofCard ((R : Subgroup ↥H).map H.subtype) hcardQ,
    by rw [Sylow.coe_ofCard]; exact Subgroup.map_subtype_le _⟩

/-- **Peterfalvi (12.9), existence of the second maximal `L`** — a §8 obligation
(`(8.17.a)` `bgTheoremE_cover_data`: `p ∈ π(G)` is covered by some `π((M_i)_s)`, giving a maximal
`L` with `p ∣ |L_s|`; then `(8.11)`/`L_s ⊇ Sylow_p(G)` and Sylow conjugation place `P₀ ⊆ L_s`). -/
theorem exists_second_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ (L : Subgroup G) (Lt : PeterfalviType), L ∈ maximalSubgroups G ∧ L ≠ ctr.M ∧
      HasPeterfalviType Lt L ∧ ctr.P0 ≤ mainSubgroup L Lt := by
  classical
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `p ∈ π(G)`: `p ∣ [M : M_F] ∣ |M| ∣ |G|`.
  have hp_in_G : ctr.p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨ctr.p_prime, ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ctr.p_dvd_index (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card ctr.M))
    exact Subgroup.relIndex_dvd_card (H := ctr.K) (K := ctr.M)
  -- `p ∤ |M_F| = |K|`: `(8.11)` makes `M_F` Hall, and `p ∣ [M : M_F] ∣ [G : M_F]`.
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hpK : ¬ ctr.p ∣ Nat.card ↥ctr.K := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    exact ctr.p_prime.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm)
  -- BG Theorem E cover data: `p ∈ π((M_i)_s)` for some representative `M_i = L₀`.  Repackage the
  -- representative as genuine local variables `L₀, Lt` (so we may later `cases` on the type label).
  obtain ⟨data, -⟩ := OddOrder.Peterfalvi.S10.bgTheoremE_cover_data.{_, 0} hG
  obtain ⟨i, hi⟩ := (data.primeFactors_cover ctr.p ctr.p_prime).mp hp_in_G
  obtain ⟨L₀, Lt, hL₀max, hL₀typed, hi'⟩ :
      ∃ (L₀ : Subgroup G) (Lt : PeterfalviType), L₀ ∈ maximalSubgroups G ∧
        HasPeterfalviType Lt L₀ ∧
        ctr.p ∈ (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors :=
    ⟨data.reps i, data.tau i, data.maximal i, data.typed i, hi⟩
  have hp_Ls : ctr.p ∣ Nat.card ↥(mainSubgroup L₀ Lt) := (Nat.mem_primeFactors.mp hi').2.1
  -- `(8.11)`: `(L₀)_s` is Hall, hence contains a Sylow `p`-subgroup `Q` of `G`.
  have hLsHall : Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup L₀ Lt)).primeFactors
      (mainSubgroup L₀ Lt) :=
    (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hL₀max hL₀typed).2
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_hall hLsHall hp_Ls
  -- A Sylow `p`-subgroup `Q'` of `G` over `P₀`, then conjugate `Q` to `Q'`.
  obtain ⟨Q', hQ'le⟩ := ctr.P0_pGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  -- `P₀ ≤ Q' = ↑(g • Q) = conj g • ↑Q ≤ conj g • (L₀)_s`.
  have hP0_le : ctr.P0 ≤ MulAut.conj g • mainSubgroup L₀ Lt := by
    refine hQ'le.trans ?_
    have hQ'eq : (Q' : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul]
    rw [hQ'eq]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQle
  -- Assemble: `L = conj g • L₀`, type `Lt`, with `P₀ ⊆ (conj g • L₀)_s`.
  refine ⟨MulAut.conj g • L₀, Lt, mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL₀max)), ?_,
    hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed, ?_⟩
  · -- `conj g • L₀ ≠ M`: else `M` has type `Lt`; if `Lt = I` then `p ∣ |K|` (false), else `M` is
    -- both type I and non-I (false).
    rintro hEq
    have hMtype : HasPeterfalviType Lt ctr.M :=
      hEq ▸ hasPeterfalviType_pointwise_smul (MulAut.conj g) Lt hL₀typed
    -- transport the divisibility `p ∣ |(L₀)_s|` to `p ∣ |M_s|`.
    have hp_Ms : ctr.p ∣ Nat.card ↥(mainSubgroup ctr.M Lt) := by
      have hcard : Nat.card ↥(mainSubgroup ctr.M Lt) = Nat.card ↥(mainSubgroup L₀ Lt) := by
        rw [← hEq, ← mainSubgroup_pointwise_smul, card_pointwise_smul]
      rw [hcard]; exact hp_Ls
    -- `ctr.M` has type `Lt` and type I.  Type `I` forces `p ∣ |K|` (false); any non-I label
    -- makes `ctr.M` non-I, contradicting type I via `not_isTypeI_of_isTypeNonI`.
    have hMnotNonI : ¬ IsTypeNonI ctr.M := fun h =>
      OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG ctr.M_maximal h ctr.M_typeI
    cases Lt with
    | I => exact hpK (by rw [ctr.K_eq_MF]; exact hp_Ms)
    | II => exact hMnotNonI (Or.inl hMtype)
    | III => exact hMnotNonI (Or.inr (Or.inl hMtype))
    | IV => exact hMnotNonI (Or.inr (Or.inr (Or.inl hMtype)))
    | V => exact hMnotNonI (Or.inr (Or.inr (Or.inr hMtype)))
  · -- `P₀ ⊆ mainSubgroup (conj g • L₀) Lt`.
    rw [← mainSubgroup_pointwise_smul]; exact hP0_le

/-- **Peterfalvi (12.9), centralizer control** — **discharged** from `(8.12.b)`
(`typeI_or_typeII_centralizer_unique`) + `G` simple.

Applying `(8.12.b)` with `U = M` and `X = {x}` (`x ∈ M^#`, and `C_K(x) ⊄ K'` gives
`M_F ⊓ C_G(x) ≠ 1`) yields `C_G(x) ≤ M` together with `IsUniquelyMaximal (C_G(x))` — `M` is the
*unique* maximal subgroup over `C_G(x)`.  Hence: `N_G(⟨x⟩) ⊇ C_G(x)` is a proper subgroup
(`⟨x⟩` is a proper nontrivial subgroup of the nonabelian simple `G`, so not normal), so it lies
in a maximal subgroup over `C_G(x)`, which must be `M`; and any maximal `L ≠ M` cannot contain
`C_G(x)`. -/
theorem centralizer_control_of_CKx [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) {L : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hLM : L ≠ ctr.M)
    {Lt : PeterfalviType} (_hLt : HasPeterfalviType Lt L) (_hPL : ctr.P0 ≤ mainSubgroup L Lt)
    {x : G} (hx : x ∈ ctr.P0) (hxne : x ≠ 1)
    (hCKx : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)) :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ≤ L) := by
  classical
  have : IsSimpleGroup G := hG.simple
  have hMcoatom : IsCoatom ctr.M := ctr.M_maximal
  have hLcoatom : IsCoatom L := hL
  have hxM : x ∈ ctr.M := ctr.P0_le_M hx
  -- `M_F ⊓ C_G(x) ≠ ⊥` from `C_K(x) ⊄ K'`.
  have hCKne : maxNilpotentNormalHall ctr.M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot; apply hCKx; rw [ctr.K_eq_MF, inf_comm, hbot]; exact bot_le
  -- The genuine `(κ ∪ σ)ᶜ`-Hall complement `U₀ ⊇ P₀ ∋ x` that BG (8.12.b) requires.
  obtain ⟨U0, hP0U0, hU0M, hU0hall⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  have hxsharp : ({x} : Set G) ⊆ sharpSubgroup U0 := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨hP0U0 hx, fun h => hxne (Set.mem_singleton_iff.mp h)⟩
  -- (8.12.b): `C_G(x) ≤ M` and uniquely maximal.
  obtain ⟨hCxleM, huniq⟩ := OddOrder.Peterfalvi.S10.typeI_or_typeII_centralizer_unique_hall hG
    ctr.M_maximal (Or.inl ctr.M_typeI) hU0M hU0hall ({x} : Set G) (Set.singleton_nonempty x)
    hxsharp hCKne
  refine ⟨?_, fun hCxleL => hLM (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hLcoatom hCxleL).symm⟩
  -- `N_G(⟨x⟩) ⊆ M`.
  have hCx_le_Nx : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.centralizer_closure]; exact Subgroup.centralizer_le_normalizer _
  have hcl_le_M : Subgroup.closure ({x} : Set G) ≤ ctr.M := Subgroup.closure_le _ |>.mpr (by
    simpa using hxM)
  have hNx_lt : Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≠ ⊤ :=
      by
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
    · exact hxne (by simpa [hb] using Subgroup.subset_closure (Set.mem_singleton x))
    · exact hMcoatom.1 (top_le_iff.mp (ht ▸ hcl_le_M))
  obtain ⟨N, hNco, hNx_le_N⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNx_lt
  exact hNx_le_N.trans (le_of_eq
    (huniq.eq_of_isCoatom_of_le hMcoatom hCxleM hNco (hCx_le_Nx.trans hNx_le_N)).symm)

/-- **Peterfalvi (12.9)**: the counterexample has an abelian rank-two Sylow
witness and an element whose centralizers force a second maximal subgroup.

Honest assembly: the structural inputs `(8.12.a)`/`(8.11)` (`counterexample_P0_K_structure`) give
`P₀` abelian of rank `2`, coprime to `K`, normalizing `K`, with `K` not perfect; the genuine
`§8`-free `exists_orderP_centralizer_witness` then produces the order-`p` element `x` with
`C_K(x) ⊄ K'`; `(8.17.a)` (`exists_second_maximal`) supplies `L`; and `(8.12.b)`
(`centralizer_control_of_CKx`) the centralizer conditions. -/
theorem exists_rankTwoWitness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 ∧ Nonempty (RankTwoWitnessData ctr) := by
  obtain ⟨hab, hrank⟩ := counterexample_P0_K_structure hG ctr
  refine ⟨hab, hrank, ?_⟩
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  -- `P₀` coprime to `K`: `(8.11)` makes `M_F` Hall (`p ∤ |M_F|` from `p ∣ [M : M_F] ∣ [G : M_F]`).
  have hcop : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K) := by
    have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG
      ctr.M_maximal (tau := PeterfalviType.I) ctr.M_typeI).1
    rw [← ctr.K_eq_MF] at hHall
    have hp_idx : ctr.p ∣ ctr.K.index :=
      ctr.p_dvd_index.trans (Subgroup.relIndex_dvd_index_of_le hKM)
    have hcop_p : Nat.Coprime ctr.p (Nat.card ↥ctr.K) :=
      Nat.Coprime.coprime_dvd_left hp_idx hHall.coprime_index.symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn]; exact hcop_p.pow_left n
  -- `P₀ ≤ N_G(K)` from `M_F ◁ M` (`maxNilpotentNormalHall_le_normalizer`).
  have hnorm : ctr.P0 ≤ Subgroup.normalizer ctr.K := by
    rw [ctr.K_eq_MF]
    exact ctr.P0_le_M.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M)
  -- `⁅K, K⁆ ≠ K`: `K = M_F` is nilpotent and nontrivial, hence not perfect.
  have hperf : ⁅ctr.K, ctr.K⁆ ≠ ctr.K := by
    obtain ⟨tiData⟩ := ctr.M_typeI
    have hKH : ctr.K = tiData.typeF.H := ctr.K_eq_MF.trans tiData.typeF.H_eq.symm
    have : Nontrivial ↥ctr.K :=
      ctr.K.nontrivial_iff_ne_bot.mpr (hKH ▸ tiData.typeF.H_nontrivial)
    have : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hlt : commutator ↥ctr.K < ⊤ :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ctr.K)
    intro hEq
    have htop_map : (⊤ : Subgroup ↥ctr.K).map ctr.K.subtype = ctr.K := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
      exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
    exact hlt.ne (Subgroup.map_injective ctr.K.subtype_injective
      (by rw [Subgroup.map_subtype_commutator, hEq, htop_map]))
  obtain ⟨x, hxP0, hxne, hxp, hCKx⟩ := exists_orderP_centralizer_witness ctr hab hcop hnorm hperf
  obtain ⟨L, Lt, hLmax, hLne, hLt, hPL⟩ := exists_second_maximal hG ctr
  obtain ⟨hNx, hCx⟩ := centralizer_control_of_CKx hG ctr hLmax hLne hLt hPL hxP0 hxne hCKx
  exact ⟨{ L := L, L_maximal := hLmax, L_type := Lt, L_hasType := hLt, P0_le_Ls := hPL,
           x := x, x_mem_P0 := hxP0, x_ne_one := hxne, x_mem_omega1 := hxp,
           CKx_not_le_Kprime := hCKx, normalizer_closure_x_le_M := hNx,
           centralizer_x_not_le_L := hCx }⟩

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b) kernel reduction, Type III/IV** (§9–§11
obligation pinned as an explicit hypothesis, hub 9003 Cluster A; the upstream has since been
proved): for a maximal subgroup `L` of Type III or IV, a noncyclic
`p`-group `P₀ ⊆ L_s` lies in the Fitting kernel `L_F`.

This is the second paragraph of (12.10) up to its final (8.6.a) step: by Theorem (10.10)
(`S12.no_typeV_maximal_unconditional`, available — excludes Type V) and (11.9.c)
(the §13 type determination, `S13_NonGaloisExclusion`) `L` is Type III with case (b) of
(9.7); by (11.6)
(`C_U(H) = 1`) and (9.7.b) the complement `U` of `H = L_F` in `[L,L]` is **cyclic**.  Since
`L_F` is a normal Hall subgroup of `L_s = [L,L]` with cyclic complement, a noncyclic `p`-group
`P₀ ≤ L_s` cannot embed in the complement side (`p ∣ |U|` would make `P₀ ↪ L_s/L_F ≅ U` cyclic),
so `p ∣ |L_F|` and `P₀` lies in the Sylow `p`-subgroup of the normal Hall `L_F`, i.e. `P₀ ⊆ L_F`.
**Genuinely still-missing**: assembling the (9.7.b)/(11.6) cyclicity of `U`
(`S13.U_isCyclic_of_hypothesis`, proven in `S13_NonGaloisExclusion`) and the Hall-embedding
bookkeeping in reach of S14. -/
theorem typeIIIorIV_noncyclic_le_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) {p : ℕ} (hp : p.Prime) (hP0p : IsPGroup p ↥P0)
    (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) :
    P0 ≤ maxNilpotentNormalHall L := by
  have : Fact p.Prime := ⟨hp⟩
  -- The genuine content, for types III/IV where `mainSubgroup L = L' = [L,L]`.  For types I/II/V
  -- `mainSubgroup L = M_F` and the goal is exactly `hP0`.
  have key : P0 ≤ derivedInG L → P0 ≤ maxNilpotentNormalHall L := by
    intro hP0'
    -- (10.10)+(11.9.c): the (10.1)/(11.2) Hypothesis holds, so (11.6)+(9.7.b) makes `U` cyclic.
    obtain ⟨hyp12⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hL
      (hIIIIV.imp id Or.inl)
    obtain ⟨s13, -⟩ := OddOrder.Peterfalvi.S13.exists_hypothesis_of_isTypeIIIorIV hG hyp12 hIIIIV
    have : NeZero (Nat.card (s13.base.toHypothesis46 hG hG.odd).W1) := ⟨Nat.card_pos.ne'⟩
    -- **(11.9.c)/(9.7.b): `U` is cyclic** (Peterfalvi §11.9, proven sorry-free in
    -- `S13_NonGaloisExclusion`).  Available here now that the §12–16 import inversion is resolved
    -- (HUB RULING, issue 9093: the §16 pair-data structures were extracted to
    -- `S13_Section16PairData`
    -- and the (12.17) producer to `FeitThompsonPairProducer`, so `S13_NonGaloisExclusion` sits
    -- upstream
    -- of §12.10 as the mathematics requires).
    have hUcyc : IsCyclic ↥s13.base.typeP.U :=
      OddOrder.Peterfalvi.S13.U_isCyclic_of_hypothesis hG s13
    set d : TypePData L := s13.base.typeP with hd
    -- `M_F = H ≤ L' ≤ L`, and `M_F ⊴ L'` (via `L' ≤ L ≤ N_G(M_F)`).
    have hLFle : maxNilpotentNormalHall L ≤ derivedInG L := by rw [← d.H_eq]; exact d.H_le
    have hL'le : derivedInG L ≤ L := Subgroup.map_subtype_le _
    have hNnorm : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLFle).mpr
        (hL'le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer L))
    -- `|U| = [L' : M_F]` divides `[L : M_F]`, and `M_F` is Hall in `L`, so `gcd(|M_F|, |U|) = 1`.
    have hUdvd : Nat.card ↥d.U ∣ ((maxNilpotentNormalHall L).subgroupOf L).index := by
      have htower := Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall L) (derivedInG L) L
        hLFle hL'le
      rw [d.card_U_eq_index]
      change (maxNilpotentNormalHall L).relIndex (derivedInG L)
        ∣ (maxNilpotentNormalHall L).relIndex L
      exact ⟨(derivedInG L).relIndex L, htower.symm⟩
    have hcopHU : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall L)) (Nat.card ↥d.U) := by
      have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L
      have hcard : Nat.card ↥((maxNilpotentNormalHall L).subgroupOf L)
          = Nat.card ↥(maxNilpotentNormalHall L) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le L)).toEquiv
      have hci := hHall.coprime_index
      rw [hcard] at hci
      exact hci.coprime_dvd_right hUdvd
    -- The crux: `p ∤ |U|`.  Otherwise `P₀` embeds in the cyclic quotient `L'/M_F ≅ U`, making
    -- `P₀` cyclic (contradiction).
    have hpU : ¬ p ∣ Nat.card ↥d.U := by
      intro hpU
      apply hP0nc
      have hpLF : ¬ p ∣ Nat.card ↥(maxNilpotentNormalHall L) := fun h =>
        hp.ne_one (Nat.dvd_one.mp (hcopHU.gcd_eq_one ▸ Nat.dvd_gcd h hpU))
      -- `P₀ ∩ M_F = 1`: a `p`-group inside the `p'`-order `M_F`.
      have hP0inf : P0 ⊓ maxNilpotentNormalHall L = ⊥ := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
          (hP0p.to_inf_left (K := maxNilpotentNormalHall L))
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · exact Subgroup.card_eq_one.mp (by rw [hn, h0, pow_zero])
        · exact absurd (dvd_trans (dvd_pow_self p hpos.ne')
            (hn ▸ Subgroup.card_dvd_of_le inf_le_right)) hpLF
      -- `L'/M_F ≅ U` is cyclic.
      have hcompl : Subgroup.IsComplement'
          ((maxNilpotentNormalHall L).subgroupOf (derivedInG L))
          (d.U.subgroupOf (derivedInG L)) := by rw [← d.H_eq]; exact d.derived_complement
      have : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal := hNnorm
      have hUcyc' : IsCyclic ↥(d.U.subgroupOf (derivedInG L)) :=
        (Subgroup.subgroupOfEquivOfLe d.U_le).isCyclic.mpr hUcyc
      have hQcyc :
          IsCyclic (↥(derivedInG L) ⧸ (maxNilpotentNormalHall L).subgroupOf (derivedInG L)) :=
        (hcompl.symm.QuotientMulEquiv).isCyclic.mpr hUcyc'
      -- `P₀ ↪ L'/M_F` (kernel `P₀ ∩ M_F = 1`), so `P₀` is cyclic.
      have hinj : Function.Injective
          ((QuotientGroup.mk' ((maxNilpotentNormalHall L).subgroupOf (derivedInG L))).comp
            (P0.subgroupOf (derivedInG L)).subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have hxN : ((x : ↥(derivedInG L)) : G) ∈ maxNilpotentNormalHall L := by
          rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
            Subgroup.mem_subgroupOf] at hx
        have hxP0 : ((x : ↥(derivedInG L)) : G) ∈ P0 := by
          have h2 := x.2; rwa [Subgroup.mem_subgroupOf] at h2
        have hbot : ((x : ↥(derivedInG L)) : G) ∈ P0 ⊓ maxNilpotentNormalHall L := ⟨hxP0, hxN⟩
        rw [hP0inf, Subgroup.mem_bot] at hbot
        exact Subtype.ext (Subtype.ext hbot)
      have : IsCyclic ↥(P0.subgroupOf (derivedInG L)) := isCyclic_of_injective _ hinj
      exact (Subgroup.subgroupOfEquivOfLe hP0').isCyclic.mp inferInstance
    -- With `p ∤ |U|`, `|P₀|` (a `p`-power) is coprime to `|U| = [L' : M_F]`, so `P₀ ≤ M_F`.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP0p
    have hcop : Nat.Coprime (Nat.card ↥P0) (Nat.card ↥d.U) := by
      rw [hn]; exact (hp.coprime_iff_not_dvd.mpr hpU).pow_left n
    have : ((maxNilpotentNormalHall L).subgroupOf (derivedInG L)).Normal := hNnorm
    have hle : P0.subgroupOf (derivedInG L)
        ≤ (maxNilpotentNormalHall L).subgroupOf (derivedInG L) := by
      apply OddOrder.BG.Ch4.S14.le_of_coprime_index
      rw [← d.card_U_eq_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0').toEquiv]
      exact hcop
    intro x hx
    have hxL' : x ∈ derivedInG L := hP0' hx
    have hmem : (⟨x, hxL'⟩ : ↥(derivedInG L))
        ∈ (maxNilpotentNormalHall L).subgroupOf (derivedInG L) :=
      hle (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rwa [Subgroup.mem_subgroupOf] at hmem
  cases Lt with
  | I => simpa [mainSubgroup] using hP0
  | II => simpa [mainSubgroup] using hP0
  | III => exact key (by simpa [mainSubgroup] using hP0)
  | IV => exact key (by simpa [mainSubgroup] using hP0)
  | V => simpa [mainSubgroup] using hP0

/-- **Peterfalvi (10.10)+(11.9.c)+(11.6)+(9.7.b)+(8.6.a), Type III/IV route**: for a maximal
subgroup `L` of Type III or IV and a noncyclic `p`-group `P₀ ⊆ L_s`, `C_G(y) ⊆ L` for every
nonidentity `y ∈ P₀`.

**Assembly** (`sorry`-free modulo the (11.9.c)/(9.7.b) kernel reduction): the reduction
`typeIIIorIV_noncyclic_le_fitting` places `P₀ ⊆ L_F`, and the (8.6.a) TI containment
`typeP_core_centralizer_le_of_mem_fitting` (via the `TypePNontrivialCore` carried by both the
`TypeIIIData` and `TypeIVData` witnesses) yields `C_G(y) ≤ L` for `y ∈ L_F^#`. -/
theorem typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L P0 : Subgroup G} (hL : L ∈ maximalSubgroups G)
    (hIIIIV : IsTypeIII L ∨ IsTypeIV L) {p : ℕ} (hp : p.Prime) (hP0p : IsPGroup p ↥P0)
    (hP0nc : ¬ IsCyclic ↥P0)
    {Lt : PeterfalviType} (hLhasType : HasPeterfalviType Lt L)
    (hP0 : P0 ≤ mainSubgroup L Lt) {y : G} (hy : y ∈ P0) (hy1 : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ L := by
  have hyF : y ∈ maxNilpotentNormalHall L :=
    typeIIIorIV_noncyclic_le_fitting hG hL hIIIIV hp hP0p hP0nc hLhasType hP0 hy
  have hcommon : ∃ pdata : TypePData L, TypePNontrivialCore L pdata := by
    rcases hIIIIV with h3 | h4
    · obtain ⟨iiiData⟩ := h3
      exact ⟨iiiData.typeP, iiiData.common⟩
    · obtain ⟨ivData⟩ := h4
      exact ⟨ivData.typeP, ivData.common⟩
  obtain ⟨pdata, hcore⟩ := hcommon
  exact typeP_core_centralizer_le_of_mem_fitting hG hL hcore hyF hy1

/-- **Peterfalvi (12.10) obligation A**: the (12.9) witness `L` is of Type I.

(12.10) rules out every non-Type-I possibility, each forcing `C_G(x) ⊆ L` and so contradicting the
(12.9) escape condition `data.centralizer_x_not_le_L` (`¬ C_G(x) ≤ L`).  The witness `x` lies in
`P₀^# ⊆ (L_s)^#` (`data.x_mem_P0`, `data.P0_le_Ls`, `data.x_ne_one`), and `P₀` is noncyclic
(`ctr.P0_noncyclic`).

* **Type V** is excluded outright by the (10.10) hypothesis `hnoV` (instantiate with the
  axiom-clean `no_typeV_maximal_unconditional`, `S12_Noncoherence`; issue 9087).
* **Type II**: (8.16) gives `C_G(x) ⊆ L` for `x ∈ (L_s)^# = A_1(L)`
  (`typeII_centralizer_le_of_mem_mainSubgroup`), contradiction.
* **Types III/IV**: via (10.10)+(11.9.c)+(11.6)+(9.7.b), `P₀ ⊆ L_F`, and (8.6.a) gives
  `C_G(x) ⊆ L` for `x ∈ L_F^#` (`typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup`),
  contradiction.

The two §8–§11 centralizer-containment facts are pinned above as explicit hypotheses (when this
was written they were genuinely missing as usable containments — the upstream
(8.16)/(8.6.a)/(11.9.c) results were themselves sorried or overstated; the repository is now
sorry-free, so the pinning may be dischargeable).  The case analysis, the Type-V exclusion
(hypothesised, honest), and the contradiction assembly here are honest. -/
theorem witness_L_isTypeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    IsTypeI data.L := by
  -- `x ∈ (L_s)^#`: nonidentity element of `mainSubgroup L L_type`.
  have hx_mem : data.x ∈ mainSubgroup data.L data.L_type := data.P0_le_Ls data.x_mem_P0
  -- The escape condition to be contradicted in every non-Type-I case.
  have hEsc : ¬ (Subgroup.centralizer ({data.x} : Set G) ≤ data.L) := data.centralizer_x_not_le_L
  -- Case-split on the Peterfalvi type of `L` (carried by `data.L_hasType`).
  have hLt := data.L_hasType
  cases hLtype : data.L_type with
  | I =>
    -- `HasPeterfalviType .I L` is definitionally `IsTypeI L`.
    rw [hLtype] at hLt; exact hLt
  | II =>
    rw [hLtype] at hLt hx_mem
    exact absurd (typeII_centralizer_le_of_mem_mainSubgroup hG data.L_maximal hLt hx_mem
      data.x_ne_one) hEsc
  | III =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inl hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ hnoV

/-- **Peterfalvi (12.9)/(12.10): the witness type is exactly `I`.**  The recorded type `data.L_type`
of the witness `L` is forced to be `I`: every other type contradicts the escape condition
`C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`) via the type-II/III/IV centralizer-containment lemmas
(and type `V` is excluded outright by the (10.10) hypothesis `hnoV`).  Same case-split as
`witness_L_isTypeI`, but concluding the identity `data.L_type = I` needed to compute
`L_s = L_F`. -/
theorem witness_L_type_eq_typeI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    data.L_type = PeterfalviType.I := by
  have hx_mem : data.x ∈ mainSubgroup data.L data.L_type := data.P0_le_Ls data.x_mem_P0
  have hEsc : ¬ (Subgroup.centralizer ({data.x} : Set G) ≤ data.L) := data.centralizer_x_not_le_L
  have hLt := data.L_hasType
  cases hLtype : data.L_type with
  | I => rfl
  | II =>
    rw [hLtype] at hLt hx_mem
    exact absurd (typeII_centralizer_le_of_mem_mainSubgroup hG data.L_maximal hLt hx_mem
      data.x_ne_one) hEsc
  | III =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inl hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | IV =>
    rw [hLtype] at hLt
    exact absurd (typeIIIorIV_centralizer_le_of_mem_noncyclic_mainSubgroup hG data.L_maximal
      (Or.inr hLt) ctr.p_prime ctr.P0_pGroup ctr.P0_noncyclic data.L_hasType data.P0_le_Ls
      data.x_mem_P0 data.x_ne_one) hEsc
  | V =>
    rw [hLtype] at hLt
    exact absurd ⟨data.L, data.L_maximal, hLt⟩ hnoV

/-- **Peterfalvi (12.10): `P₀ ⊆ L_F`.**  Since the witness type is `I` (`witness_L_type_eq_typeI`),
`L_s = mainSubgroup L I = L_F`, so `data.P0_le_Ls` (`P₀ ⊆ L_s`) gives `P₀ ⊆ L_F`. -/
theorem witness_P0_le_kernel [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.P0 ≤ maxNilpotentNormalHall data.L := by
  have hI := witness_L_type_eq_typeI hG hnoV data
  have hP0 := data.P0_le_Ls
  rw [hI] at hP0
  simpa [mainSubgroup] using hP0

/-- **A `q`-subgroup of a nilpotent subgroup `K` lies in `O_q(K) = opiCoreInG {q} K`** (the unique
Sylow `q`-subgroup of the nilpotent `K`).  Generalisation of `pGroup_le_opiCoreInG_fittingInG` from
`F(E)` to any nilpotent `K`; the proof uses only `IsNilpotent ↥K`. -/
theorem pGroup_le_opiCoreInG_of_le_of_isNilpotent [Finite G]
    {K : Subgroup G} [Group.IsNilpotent ↥K] {q : ℕ} [Fact q.Prime]
    {T : Subgroup G} (hT : IsPGroup q ↥T) (hTK : T ≤ K) :
    T ≤ opiCoreInG ({q} : Set ℕ) K := by
  classical
  have hHall := OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent (K := ↥K) ({q} : Set ℕ)
  have hTpi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (T.subgroupOf K) := by
    intro r hr
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv, hk] at hr
    have h2 := Nat.prime_of_mem_primeFactors hr
    have h3 := Nat.dvd_of_mem_primeFactors hr
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq h2 Fact.out).mp (h2.dvd_of_dvd_pow h3)
    simpa using hrq
  have h1 : T.subgroupOf K ≤ Ch03.oPiCore ({q} : Set ℕ) ↥K :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall hTpi
  calc T = (T.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hTK).symm
    _ ≤ (Ch03.oPiCore ({q} : Set ℕ) ↥K).map K.subtype := Subgroup.map_mono h1
    _ = opiCoreInG ({q} : Set ℕ) K := rfl

/-- **`N_G(L_F) = L` for the witness subgroup** (`TypeIData` form, Frobenius-free): `L` is maximal
(a coatom) and normalizes its Fitting kernel `H = L_F ≠ ⊥`; a strictly larger normalizer would be
`⊤` by maximality, making `H ≠ ⊥` normal in the simple `G` — impossible.  Shared by the (12.10)
TI-case exclusion (`witness_H_sharp_not_isTISubset_of_typeI`) and its Frobenius specialization. -/
theorem witness_normalizer_kernel_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    Subgroup.normalizer ((typeI.typeF.H : Subgroup G) : Set G) = data.L := by
  have hne : maxNilpotentNormalHall data.L ≠ ⊥ := by
    rw [← typeI.typeF.H_eq]; exact typeI.typeF.H_nontrivial
  rw [typeI.typeF.H_eq]
  exact (maximalSubgroup_eq_normalizer_maxNilpotentNormalHall hG data.L_maximal hne).symm

/-- **(12.10), TI-case exclusion for the witness** (`TypeIData` form, Frobenius-free): the
kernel-sharp set `H^#` of the witness `L` is **not** a TI-subset of `G`.  The rank-two witness
`x ∈ Ω₁(P₀)^# ⊆ H^#` (`witness_P0_le_kernel`) has `C_G(x) ⊄ L` (`data.centralizer_x_not_le_L`)
while `N_G(H) = L` (`witness_normalizer_kernel_eq`); picking `g ∈ C_G(x) ∖ L` gives
`g x g⁻¹ = x ∈ H^# ∩ (H^#)^g` with `g ∉ N_G(H)` — the TI failure.  Dispatches case (a) of the
(8.3) alternative in the (12.10) minimality argument. -/
theorem witness_H_sharp_not_isTISubset_of_typeI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup typeI.typeF.H)
        (Subgroup.normalizer (typeI.typeF.H : Set G)) := by
  intro hTI
  have hNL := witness_normalizer_kernel_eq hG data typeI
  have hxH : data.x ∈ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]
    exact witness_P0_le_kernel hG hnoV data data.x_mem_P0
  have hxsharp : data.x ∈ OddOrder.GroupTheory.sharpSubgroup typeI.typeF.H :=
    ⟨hxH, by simpa using data.x_ne_one⟩
  obtain ⟨g, hgC, hgL⟩ := SetLike.not_le_iff_exists.mp data.centralizer_x_not_le_L
  have hgc : g * data.x * g⁻¹ = data.x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  exact hgL (hNL ▸ hTI g ⟨data.x, hxsharp, by rw [hgc]; exact hxsharp⟩)

/-- An **odd** prime `q` dividing `p² − 1` for an **odd** prime `p` satisfies `q < p`:
`q ∣ (p+1)(p−1)` splits as `q ∣ p−1` (so `q ≤ p−1 < p`) or `q ∣ p+1`; in the latter case
`q ≠ p+1` (`p+1` is even, `q` odd), so `q` is a proper divisor: `2q ≤ p+1 < 2p`.  The `q < p`
conclusion of the (8.3.b)/(8.3.c) prime comparison in Peterfalvi (12.10). -/
theorem prime_lt_of_odd_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp_odd : Odd p) (hq_odd : Odd q) (hdvd : q ∣ p ^ 2 - 1) : q < p := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · exact absurd hp_odd (by decide)
    · exact h
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [sq]; exact mul_self_tsub_one p
  rcases (Nat.Prime.dvd_mul hq).mp (hfac ▸ hdvd) with h | h
  · -- `q ∣ p + 1`: a proper (odd) divisor of the even `p + 1`, so `2q ≤ p + 1 < 2p`.
    have hne : q ≠ p + 1 := by
      intro heq
      obtain ⟨m, hm⟩ := hq_odd
      obtain ⟨l, hl⟩ := hp_odd
      omega
    obtain ⟨c, hc⟩ := h
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with h' | h'
      · interval_cases c
        · omega
        · exact absurd (by omega : q = p + 1) hne
      · exact h'
    have h2q : 2 * q ≤ p + 1 := by
      calc 2 * q ≤ c * q := Nat.mul_le_mul_right q hc2
        _ = q * c := mul_comm c q
        _ = p + 1 := hc.symm
    omega
  · -- `q ∣ p − 1 < p`.
    have := Nat.le_of_dvd (by omega) h
    omega

/-- **(12.10), case (8.3.b) counting core** (type-`F` general form): if the kernel `H` of a
type-`F` subgroup is **abelian of rank ≤ 2** with `p ∣ |H|`, then every prime `q` dividing `|U|`
divides `p² − 1`.

Peterfalvi's argument: `q ∣ |U|` gives an order-`q` element of `U` (Cauchy), so
`q ∣ exp U = exp U₀ ∣ |U₀|` (the `(8.1.c)`/`(8.2.a)` fields) and `U₀` has an element `u` of
order `q`.  `H U₀` is Frobenius with kernel `H` (`frobenius_HU0`), so the nontrivial cyclic
`⟨u⟩` (meeting `H` trivially) acts fixed-point-freely on the `⟨u⟩`-invariant subgroup
`Ω₁(H) ≠ ⊥`, whence `|Ω₁(H)| ≡ 1 (mod q)`
(`IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient`).  As `H` is abelian of rank
≤ 2, `|Ω₁(H)| = p^k` with `1 ≤ k ≤ 2`, so `q ∣ p^k − 1 ∣ p² − 1`. -/
theorem _root_.OddOrder.GroupTheory.TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel
    [Finite G] {M : Subgroup G} (typeF : OddOrder.GroupTheory.TypeFData M)
    (hab : IsMulCommutative ↥typeF.H) (hrank : OddOrder.GroupTheory.rank ↥typeF.H ≤ 2)
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpH : p ∣ Nat.card ↥typeF.H)
    (hqU : q ∣ Nat.card ↥typeF.U) :
    q ∣ p ^ 2 - 1 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fintype ↥typeF.U := Fintype.ofFinite _
  have : Fintype ↥typeF.U0 := Fintype.ofFinite _
  have : Fintype ↥typeF.H := Fintype.ofFinite _
  -- Abelian commutation witness for `Ω₁(H)`.
  have hcomm : ∀ x ∈ typeF.H, ∀ y ∈ typeF.H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm (⟨x, hx⟩ : ↥typeF.H) (⟨y, hy⟩ : ↥typeF.H))
  set Ω : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G typeF.H p hcomm with hΩdef
  -- An order-`q` element `u ∈ U₀` via `q ∣ exp U = exp U₀ ∣ |U₀|`.
  obtain ⟨u₁, hu₁⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.U) q
    (by rwa [← Nat.card_eq_fintype_card])
  have hqU0 : q ∣ Nat.card ↥typeF.U0 :=
    ((hu₁ ▸ Monoid.order_dvd_exponent u₁ : q ∣ Monoid.exponent ↥typeF.U).trans
      (typeF.exponent_eq ▸ dvd_refl _ : Monoid.exponent ↥typeF.U ∣ Monoid.exponent ↥typeF.U0)).trans
      Group.exponent_dvd_nat_card
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.U0) q
    (by rwa [← Nat.card_eq_fintype_card])
  have hu_ord : orderOf ((u : G)) = q := by
    rw [← hu]
    exact orderOf_injective typeF.U0.subtype typeF.U0.subtype_injective u
  have hu_ne : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu_ord
    exact hq.one_lt.ne' hu_ord.symm
  set A : Subgroup G := Subgroup.zpowers (u : G) with hAdef
  have hAcard : Nat.card ↥A = q := by rw [hAdef, Nat.card_zpowers, hu_ord]
  -- `Ω₁(H) ≠ ⊥`: an order-`p` element of `H` (Cauchy at `p ∣ |H|`) lies in it.
  have hΩne : Ω ≠ ⊥ := by
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥typeF.H) p
      (by rwa [← Nat.card_eq_fintype_card])
    have hg_ord : orderOf (g : G) = p := by
      rw [← hg]
      exact orderOf_injective typeF.H.subtype typeF.H.subtype_injective g
    have hgΩ : (g : G) ∈ Ω := ⟨g.2, by rw [← hg_ord]; exact pow_orderOf_eq_one _⟩
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hgΩ
    rw [hgΩ, orderOf_one] at hg_ord
    exact (Fact.out : p.Prime).one_lt.ne' hg_ord.symm
  -- `u ∉ H` (complement disjointness), so the prime-order `A = ⟨u⟩` meets `H` trivially.
  have huH : (u : G) ∉ typeF.H := by
    intro huH
    have huU : (u : G) ∈ typeF.U := typeF.U0_le u.2
    have huM : (u : G) ∈ M := typeF.U_le huU
    have hmem : (⟨(u : G), huM⟩ : ↥M) ∈ typeF.H.subgroupOf M ⊓ typeF.U.subgroupOf M :=
      ⟨Subgroup.mem_subgroupOf.mpr huH, Subgroup.mem_subgroupOf.mpr huU⟩
    rw [typeF.complement.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact hu_ne (congrArg Subtype.val hmem)
  have hAH : A ⊓ typeF.H = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ typeF.H) ∣ q := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqq
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : A ⊓ typeF.H = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hAcard, hqq])
      exact huH ((heq.symm ▸ Subgroup.mem_zpowers (u : G) : (u : G) ∈ A ⊓ typeF.H)).2
  -- `⟨u⟩` normalizes `Ω₁(H)` (it normalizes `H = M_F ◁ M`).
  have hAnorm : A ≤ Subgroup.normalizer ((Ω : Subgroup G) : Set G) := by
    rw [hAdef, Subgroup.zpowers_le]
    refine OddOrder.GroupTheory.mem_normalizer_omega1OfAbelian ?_
    have huM : (u : G) ∈ M := typeF.U_le (typeF.U0_le u.2)
    have hMN : M ≤ Subgroup.normalizer ((typeF.H : Subgroup G) : Set G) := by
      rw [typeF.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
    exact hMN huM
  -- Frobenius counting: `|Ω₁(H)| ≡ 1 (mod q)`.
  have hmod :=
    OddOrder.GroupTheory.IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient
      (le_sup_left : typeF.H ≤ typeF.H ⊔ typeF.U0) ⟨_, typeF.frobenius_HU0⟩
      (OddOrder.GroupTheory.omega1OfAbelian_le) hΩne
      (by rw [hAdef, Subgroup.zpowers_le]; exact Subgroup.mem_sup_right u.2) hAH
      (by
        rw [hAdef]
        intro hbot
        exact hu_ne (by
          have := Subgroup.mem_zpowers (u : G)
          rwa [hbot, Subgroup.mem_bot] at this))
      hAnorm
  rw [hAcard] at hmod
  have hq_dvd : q ∣ Nat.card ↥Ω - 1 :=
    (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm
  -- `|Ω₁(H)| = p^k` with `1 ≤ k ≤ 2` (elementary abelian; rank bound).
  have hΩelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥Ω :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
  obtain ⟨k, hΩcard⟩ : ∃ k, Nat.card ↥Ω = p ^ k := ⟨_, hΩelem.card_eq_pow_finrank⟩
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    exact hΩne (Subgroup.card_eq_one.mp (by rw [hΩcard, hk0, pow_zero]))
  have hk2 : k ≤ 2 := by
    have hsub_elem : (Ω.subgroupOf typeF.H).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe OddOrder.GroupTheory.omega1OfAbelian_le).symm hΩelem
    have hle := OddOrder.GroupTheory.le_pRank (Ω.subgroupOf typeF.H) hsub_elem
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        OddOrder.GroupTheory.omega1OfAbelian_le).toEquiv,
      hΩcard, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    calc k ≤ OddOrder.GroupTheory.pRank ↥typeF.H p := hle
      _ ≤ OddOrder.GroupTheory.rank ↥typeF.H := OddOrder.GroupTheory.pRank_le_rank p
      _ ≤ 2 := hrank
  -- `q ∣ p^k − 1 ∣ p² − 1`.
  have hdvd_pk : q ∣ p ^ k - 1 := by rw [← hΩcard]; exact hq_dvd
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [sq]; exact mul_self_tsub_one p
  interval_cases k
  · exact hdvd_pk.trans (by rw [hfac, pow_one]; exact dvd_mul_left _ _)
  · exact hdvd_pk

/-- **Counterexample fact: `p ∤ |K|`.**  `K = M_F` is Hall in `M` while `p ∣ [M : M_F]`
(Hypothesis (12.8)), so `p` cannot also divide `|K|`. -/
theorem p_not_dvd_card_K [Finite G] (ctr : CounterexampleHypothesis (G := G)) :
    ¬ ctr.p ∣ Nat.card ↥ctr.K := by
  intro hdvd
  have hKleM : ctr.K ≤ ctr.M :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hcard : Nat.card ↥(ctr.K.subgroupOf ctr.M) = Nat.card ↥ctr.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleM).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥ctr.K) (ctr.K.relIndex ctr.M) := by
    have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
    rw [← ctr.K_eq_MF, hcard] at h
    rwa [Subgroup.relIndex]
  exact Nat.Prime.not_dvd_one ctr.p_prime (hcop ▸ Nat.dvd_gcd hdvd ctr.p_dvd_index)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Peterfalvi (8.1.c) → (12.16) numeric input: `4·|K'| ≤ |K|`** (the `hidx` field of
`CounterexampleDadeData`).

The type-I structure of `M` supplies, via the (8.1.c) Frobenius group `H ⋊ U₀`
(`typeF.frobenius_HU0`) and `p ∣ [M : M_F] = |U|` with `exp U₀ = exp U`, an element `u ∈ U₀`
of order `p` acting fixed-point-freely on `K = M_F` by conjugation.  The FPF property descends
along the coprime quotient `K/K'` (Isaacs Cor 3.28, `coprime_fixedPoints_quotient`), so the
`p`-group `⟨u⟩` acts on `K/K'` with `1` as its only fixed point; orbit counting
(`IsPGroup.card_modEq_card_fixedPoints`) gives `|K/K'| ≡ 1 (mod p)`.  `K` is nilpotent and
nontrivial, hence not perfect, so `|K/K'| ≠ 1`, whence `|K/K'| ≥ p + 1 ≥ 4` (`p ≥ 3` odd) and
`|K| = |K/K'|·|K'| ≥ 4·|K'|`. -/
theorem four_mul_card_Kprime_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    4 * Nat.card ↥ctr.Kprime ≤ Nat.card ↥ctr.K := by
  classical
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨tI⟩ := ctr.M_typeI
  have hHK : tI.typeF.H = ctr.K := tI.typeF.H_eq.trans ctr.K_eq_MF.symm
  -- `p ∣ |U|` (the type-I complement realizes `[M : M_F]`).
  have hpU : ctr.p ∣ Nat.card ↥tI.typeF.U := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have h := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at h
    rw [← hHK, tI.typeF.complement.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tI.typeF.U_le).toEquiv] at h1
  -- An order-`p` element `u ∈ U₀` (Cauchy through `exp U₀ = exp U`).
  have : Fintype ↥tI.typeF.U := Fintype.ofFinite _
  obtain ⟨xU, hxU⟩ := exists_prime_orderOf_dvd_card (G := ↥tI.typeF.U) ctr.p
    (by rwa [Nat.card_eq_fintype_card] at hpU)
  have hpU0 : ctr.p ∣ Nat.card ↥tI.typeF.U0 := by
    have : Fintype ↥tI.typeF.U0 := Fintype.ofFinite _
    have hexp : Monoid.exponent ↥tI.typeF.U0 ∣ Nat.card ↥tI.typeF.U0 := by
      rw [Nat.card_eq_fintype_card]
      exact Group.exponent_dvd_card
    refine Dvd.dvd.trans ?_ hexp
    rw [tI.typeF.exponent_eq]
    exact hxU ▸ Monoid.order_dvd_exponent xU
  have : Fintype ↥tI.typeF.U0 := Fintype.ofFinite _
  obtain ⟨u0, hu0⟩ := exists_prime_orderOf_dvd_card (G := ↥tI.typeF.U0) ctr.p
    (by rwa [Nat.card_eq_fintype_card] at hpU0)
  set u : G := (u0 : G) with hu_def
  have huU0 : u ∈ tI.typeF.U0 := u0.2
  have hu_ord : orderOf u = ctr.p := by
    rw [← hu0]
    exact orderOf_injective tI.typeF.U0.subtype tI.typeF.U0.subtype_injective u0
  have hu_ne : u ≠ 1 := fun h =>
    ctr.p_prime.one_lt.ne' (by rw [← hu_ord, h, orderOf_one])
  -- `u` acts fixed-point-freely on `K` (ambient form of `frobenius_HU0.conj_frobenius`).
  have hfpf : ∀ n ∈ ctr.K, u * n * u⁻¹ = n → n = 1 := by
    intro n hnK hconj
    by_contra hn_ne
    have hnH : n ∈ tI.typeF.H := hHK ▸ hnK
    have huS : u ∈ tI.typeF.H ⊔ tI.typeF.U0 := Subgroup.mem_sup_right huU0
    have hnS : n ∈ tI.typeF.H ⊔ tI.typeF.U0 := Subgroup.mem_sup_left hnH
    exact tI.typeF.frobenius_HU0.conj_frobenius ⟨u, huS⟩
      (Subgroup.mem_subgroupOf.mpr huU0)
      (fun h => hu_ne (congrArg Subtype.val h)) ⟨n, hnS⟩
      (Subgroup.mem_subgroupOf.mpr hnH)
      (fun h => hn_ne (congrArg Subtype.val h)) (Subtype.ext hconj)
  -- The conjugation action of `⟨u⟩` on `K` and its descent to `K/K'`.
  have huM : u ∈ ctr.M := tI.typeF.U_le (tI.typeF.U0_le huU0)
  have hu_norm : u ∈ Subgroup.normalizer ctr.K := by
    have h := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M
    exact ctr.K_eq_MF ▸ h huM
  have hAnorm : Subgroup.zpowers u ≤ Subgroup.normalizer ctr.K :=
    Subgroup.zpowers_le.mpr hu_norm
  set φ : ↥(Subgroup.zpowers u) →* MulAut ↥ctr.K :=
    (Subgroup.normalizerMonoidHom ctr.K).comp (Subgroup.inclusion hAnorm) with hφ
  have hN_inv : Ch03.IsAInvariant φ (commutator ↥ctr.K) :=
    Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  let : MulAction ↥(Subgroup.zpowers u) (↥ctr.K ⧸ commutator ↥ctr.K) :=
    MulAction.compHom _ ψ
  -- `p ∤ |K|`, so Isaacs 3.28 lifts quotient fixed points; FPF then leaves only `1`.
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥ctr.K) := by
    rw [Nat.card_zpowers, hu_ord]
    exact ctr.p_prime.coprime_iff_not_dvd.mpr (p_not_dvd_card_K ctr)
  have hfix_eq : MulAction.fixedPoints ↥(Subgroup.zpowers u) (↥ctr.K ⧸ commutator ↥ctr.K)
      = {1} := by
    ext q
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator ↥ctr.K) q
      have hg_fix : ∀ a : ↥(Subgroup.zpowers u), ∃ n ∈ commutator ↥ctr.K, φ a g = g * n := by
        intro a
        have hb : ψ a (QuotientGroup.mk' (commutator ↥ctr.K) g)
            = QuotientGroup.mk' (commutator ↥ctr.K) g := hq a
        rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
          QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
        exact ⟨g⁻¹ * φ a g, by simpa using (commutator ↥ctr.K).inv_mem hb, by group⟩
      obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
        Ch04.coprime_fixedPoints_quotient hCop (Or.inl inferInstance) hN_inv hg_fix
      have hca : φ ⟨u, Subgroup.mem_zpowers u⟩ c = c := hc_fix ⟨u, Subgroup.mem_zpowers u⟩
      have hc1 : (c : G) = 1 := hfpf (c : G) c.2 (congrArg Subtype.val hca)
      have hg_mem : g ∈ commutator ↥ctr.K := by
        have hgc : g = c * n⁻¹ := by rw [hcn]; group
        rw [hgc, show c = (1 : ↥ctr.K) from Subtype.ext hc1, one_mul]
        exact (commutator ↥ctr.K).inv_mem hn
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hg_mem
    · rintro rfl
      intro a
      change ψ a 1 = 1
      exact map_one (ψ a)
  -- Orbit counting: `|K/K'| ≡ 1 (mod p)`.
  have : Fintype (↥ctr.K ⧸ commutator ↥ctr.K) := Fintype.ofFinite _
  have : Fintype (MulAction.fixedPoints ↥(Subgroup.zpowers u)
    (↥ctr.K ⧸ commutator ↥ctr.K)) := Fintype.ofFinite _
  have hApG : IsPGroup ctr.p ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu_ord, pow_one])
  have hmod := hApG.card_modEq_card_fixedPoints (↥ctr.K ⧸ commutator ↥ctr.K)
  have hfixcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers u)
      (↥ctr.K ⧸ commutator ↥ctr.K)) = 1 := by
    rw [Nat.card_congr (Equiv.setCongr hfix_eq)]
    exact Nat.card_unique
  have hQmod : Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) % ctr.p = 1 % ctr.p := by
    have h2 := hmod
    rw [hfixcard] at h2
    exact h2
  -- `|K/K'| ≠ 1` (`K` is nilpotent and nontrivial, hence not perfect).
  have hQne1 : Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) ≠ 1 := by
    intro h1
    have : Nontrivial ↥ctr.K :=
      (Subgroup.nontrivial_iff_ne_bot ctr.K).mpr (hHK ▸ tI.typeF.H_nontrivial)
    have : Group.IsNilpotent ↥ctr.K :=
      ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent ctr.M
    have hcomm_ne : commutator ↥ctr.K ≠ ⊤ :=
      (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥ctr.K).ne
    exact hcomm_ne (Subgroup.index_eq_one.mp h1)
  -- `p ≥ 3` (odd), so `|K/K'| ≥ p + 1 ≥ 4`.
  have hpG : ctr.p ∣ Nat.card G := by
    have h1 : ctr.p ∣ (ctr.K.subgroupOf ctr.M).index := by
      have := ctr.p_dvd_index
      rwa [Subgroup.relIndex] at this
    exact (h1.trans (Subgroup.index_dvd_card _)).trans
      (Subgroup.card_subgroup_dvd_card ctr.M)
  have hpodd : Odd ctr.p := hG.odd.of_dvd_nat hpG
  have hp3 : 3 ≤ ctr.p := by
    have h2 := ctr.p_prime.two_le
    have hne : ctr.p ≠ 2 := fun h => by
      rw [h] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    omega
  have hQ4 : 4 ≤ Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) := by
    set c := Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) with hc
    have h1p : (1 : ℕ) % ctr.p = 1 := Nat.mod_eq_of_lt (by omega)
    have hdm := Nat.div_add_mod c ctr.p
    rw [hQmod, h1p] at hdm
    have hq1 : 1 ≤ c / ctr.p := by
      rcases Nat.eq_zero_or_pos (c / ctr.p) with h0 | hpos
      · rw [h0, mul_zero, zero_add] at hdm
        exact absurd hdm.symm hQne1
      · exact hpos
    have hple : ctr.p ≤ ctr.p * (c / ctr.p) := Nat.le_mul_of_pos_right _ hq1
    obtain ⟨X, hX⟩ : ∃ X, ctr.p * (c / ctr.p) = X := ⟨_, rfl⟩
    rw [hX] at hdm hple
    omega
  -- `|K| = |K/K'|·|K'|`.
  have hKfact : Nat.card ↥ctr.K
      = Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) * Nat.card ↥(commutator ↥ctr.K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hK'card : Nat.card ↥ctr.Kprime = Nat.card ↥(commutator ↥ctr.K) := by
    rw [ctr.Kprime_eq]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (commutator ↥ctr.K) ctr.K.subtype
      ctr.K.subtype_injective).toEquiv).symm
  calc 4 * Nat.card ↥ctr.Kprime
      = 4 * Nat.card ↥(commutator ↥ctr.K) := by rw [hK'card]
    _ ≤ Nat.card (↥ctr.K ⧸ commutator ↥ctr.K) * Nat.card ↥(commutator ↥ctr.K) :=
        Nat.mul_le_mul_right _ hQ4
    _ = Nat.card ↥ctr.K := hKfact.symm

end OddOrder.Peterfalvi.S14


