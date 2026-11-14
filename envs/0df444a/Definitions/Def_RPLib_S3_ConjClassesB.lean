-- Prove2me | Definitions.Def_RPLib_S3_ConjClassesB
-- name    : RPLib_S3_ConjClassesB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:55:40.815754+00:00
-- url     : https://prove2.me/theorems/97aac637-e343-4d18-b7ad-56b17cf12e05
-- title:
--   The Eichler-Selberg trace formula, conjugacy classes part B: the elliptic class sum
-- statement:
--   For $t^2 < 4n$, the $\Gamma_1(M)$-conjugacy classes of integer matrices with determinant $n$, trace $t$, lower-left entry $c > 0$, $c \equiv 0$ and $a \equiv \delta'$ mod $M$, each weighted by the inverse order of its centraliser, sum to the level-vector count of reduced forms of discriminant $t^2 - 4n$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesA

/-!
# Conjugacy classes of `Δ^{(δ')}_n(M)` (unit S3-ConjClasses, part B: the elliptic class sum)

For `t² < 4n`, the `Γ₁(M)`-conjugacy classes of `γ ∈ M₂(ℤ)` with `det γ = n`, `tr γ = t`, lower-left entry
`c > 0`, `a ≡ δ'`, `c ≡ 0 (mod M)`, each weighted by `1 / #centraliser`, sum to `ellCount M δ' t n`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Conj

open Matrix MatrixGroups RamanujanPetersson.Hurwitz CongruenceSubgroup

/-! ## Generic helpers -/

/-- `Σ_{G-orbits C} 1 / #Stab(C)`. -/
noncomputable def classSum (G : Type*) [Group G] (X : Type*) [MulAction G X] : ℚ :=
  ∑ᶠ C : MulAction.orbitRel.Quotient G X, (1 : ℚ) / Nat.card (MulAction.stabilizer G C.out)

theorem mk_eq_mk_iff {G X : Type*} [Group G] [MulAction G X] (a b : X) :
    Quotient.mk (MulAction.orbitRel G X) a = Quotient.mk _ b ↔ ∃ h : G, h • b = a :=
  ⟨fun e => MulAction.mem_orbit_iff.1 (Quotient.exact e),
    fun ⟨h, hh⟩ => Quotient.sound (MulAction.mem_orbit_iff.2 ⟨h, hh⟩)⟩

theorem card_stab_out {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (MulAction.stabilizer G (Quotient.out (Quotient.mk (MulAction.orbitRel G X) x))) =
      Nat.card (MulAction.stabilizer G x) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (Quotient.exact (Quotient.out_eq _))).toEquiv

theorem finsum_eq_sum_fiber {ι α : Type*} [Fintype ι] (f : ι → α) (hf : Function.Surjective f)
    (w : α → ℚ) : ∑ᶠ a, w a = ∑ i, w (f i) / Nat.card {j // f j = f i} := by
  classical
  have : Finite α := Finite.of_surjective f hf
  letI := Fintype.ofFinite α
  have hcard : ∀ i, (Nat.card {j // f j = f i} : ℚ) = ((Finset.univ.filter fun j => f j = f i).card : ℚ) := by
    intro i; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [hcard]
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨i0, rfl⟩ := hf a
  have hc : ((Finset.univ.filter fun j => f j = f i0).card : ℚ) ≠ 0 := by
    have : (Finset.univ.filter fun j => f j = f i0).card ≠ 0 := Finset.card_ne_zero.2 ⟨i0, by simp⟩
    exact_mod_cast this
  have key : ∀ i ∈ Finset.univ.filter (fun j => f j = f i0),
      w (f i) / ((Finset.univ.filter fun j => f j = f i).card : ℚ) =
        w (f i0) / ((Finset.univ.filter fun j => f j = f i0).card : ℚ) := by
    intro i hi; rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ## Forms and centralisers -/

theorem toBQF_injective : Function.Injective toBQF := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [toBQF, BQF.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; rfl

theorem mem_stabilizer_iff_conj (z : SL(2, ℤ)) (γ : Mat) :
    z ∈ MulAction.stabilizer SL(2, ℤ) (formOf γ) ↔ conj z γ = γ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h; exact eq_of_formOf_eq (by rw [formOf_conj, h]) (trace_conj z γ)
  · intro h; rw [← formOf_conj, h]

theorem gammaQ_facts {t : ℤ} {n : ℕ} {Q : ℤ × ℤ × ℤ} (hQ : Q ∈ redForms (t ^ 2 - 4 * n)) :
    (gammaQ Q t).det = n ∧ (gammaQ Q t).trace = t ∧ (formOf (gammaQ Q t)).PosDef := by
  obtain ⟨hD, hR⟩ := mem_redForms.1 hQ
  obtain ⟨h1, h2, h3⟩ := gammaQ_props hD
  exact ⟨h2, h1, h3 ▸ hR.posDef⟩

theorem card_stab_mul_ncard_orbit {M : ℕ} {Q : ℤ × ℤ × ℤ} (hQ : (toBQF Q).IsReduced) (v : Fin 2 → ZMod M) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer SL(2, ℤ) (toBQF Q)) v) *
      (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) (toBQF Q)) v).ncard = stabOrd Q := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index, stabOrd_eq_card hQ]

/-! ## The set `EllPos` and the `Γ₁(M)`-action -/

/-- Elliptic `γ ∈ Δ^{(δ')}_n(M)` of trace `t` with lower-left entry `c > 0`
(`PosDef` of `[c, d - a, -b]` is `c > 0 ∧ t² < 4n`). -/
def EllPos (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) : Set Mat :=
  {γ | γ.det = n ∧ γ.trace = t ∧ (formOf γ).PosDef ∧ ((γ 0 0 : ℤ) : ZMod M) = δ' ∧
    ((γ 1 0 : ℤ) : ZMod M) = 0}

theorem mem_EllPos_iff {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} {γ : Mat} :
    γ ∈ EllPos M δ' t n ↔ γ.det = n ∧ γ.trace = t ∧ (formOf γ).PosDef ∧ Eig M δ' γ (e1 M) := by
  rw [eig_e1_iff]; simp only [EllPos, Set.mem_setOf_eq]

theorem conj_mem_EllPos {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} {γ : Mat} (g : SL(2, ℤ))
    (hγ : γ.det = n ∧ γ.trace = t ∧ (formOf γ).PosDef) {w : Fin 2 → ZMod M} (hw : g • w = e1 M)
    (he : Eig M δ' γ w) : conj g γ ∈ EllPos M δ' t n := by
  rw [mem_EllPos_iff, det_conj, trace_conj, formOf_conj, posDef_smul_iff, ← hw, eig_conj_iff]
  exact ⟨hγ.1, hγ.2.1, hγ.2.2, he⟩

/-- `Γ₁(M)` acts on `EllPos` by conjugation. -/
instance ellPosAction (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    MulAction (Gamma1 M) (EllPos M δ' t n) where
  smul h γ := ⟨conj (h : SL(2, ℤ)) γ.1, by
    obtain ⟨h1, h2, h3, h4⟩ := mem_EllPos_iff.1 γ.2
    exact conj_mem_EllPos (h : SL(2, ℤ)) ⟨h1, h2, h3⟩ ((mem_Gamma1_iff M h).1 h.2) h4⟩
  one_smul γ := Subtype.ext (conj_one γ.1)
  mul_smul g h γ := Subtype.ext (conj_mul g h γ.1)

theorem ellPos_smul_val {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} (h : Gamma1 M) (γ : EllPos M δ' t n) :
    ((h • γ : EllPos M δ' t n) : Mat) = conj (h : SL(2, ℤ)) γ := rfl

/-! ## Pairs `(Q, v)` and the surjection onto the classes -/

section Main

variable {M : ℕ} [NeZero M]

open Classical in
/-- The pairs counted by `ellCount`: reduced `Q` of discriminant `t² - 4n` and level vectors `v`. -/
noncomputable def pairSet (δ' : ZMod M) (t : ℤ) (n : ℕ) : Finset ((ℤ × ℤ × ℤ) × (Fin 2 → ZMod M)) :=
  ((redForms (t ^ 2 - 4 * n)) ×ˢ Finset.univ).filter fun p => IsExact M p.2 ∧ Eig M δ' (gammaQ p.1 t) p.2

theorem mem_pairSet (δ' : ZMod M) (t : ℤ) (n : ℕ) {p : (ℤ × ℤ × ℤ) × (Fin 2 → ZMod M)} :
    p ∈ pairSet δ' t n ↔ p.1 ∈ redForms (t ^ 2 - 4 * n) ∧ IsExact M p.2 ∧ Eig M δ' (gammaQ p.1 t) p.2 := by
  simp [pairSet]

theorem sum_pairSet (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    ∑ p ∈ pairSet δ' t n, (1 : ℚ) / stabOrd p.1 = ellCount M δ' t n := by
  classical
  rw [pairSet, Finset.sum_filter, Finset.sum_product, ellCount]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [levelCount, Finset.card_filter, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [IsExact, Eig, redMat]
  split_ifs <;> simp_all

open Classical in
/-- A chosen `g` with `g e₁ = v`. -/
noncomputable def rep (v : Fin 2 → ZMod M) : SL(2, ℤ) :=
  if h : IsExact M v then Classical.choose (exists_smul_e1 h) else 1

theorem rep_spec {v : Fin 2 → ZMod M} (h : IsExact M v) : rep v • e1 M = v := by
  rw [rep, dif_pos h]; exact Classical.choose_spec (exists_smul_e1 h)

theorem xpt_mem (δ' : ZMod M) (t : ℤ) (n : ℕ) (i : pairSet δ' t n) :
    conj (rep i.1.2)⁻¹ (gammaQ i.1.1 t) ∈ EllPos M δ' t n := by
  obtain ⟨hQ, hv, he⟩ := (mem_pairSet δ' t n).1 i.2
  exact conj_mem_EllPos _ (gammaQ_facts hQ) (inv_smul_eq_iff.2 (rep_spec hv).symm) he

/-- The point `g⁻¹ γ_Q g` of `EllPos` attached to `(Q, v = g e₁)`. -/
noncomputable def xpt (δ' : ZMod M) (t : ℤ) (n : ℕ) (i : pairSet δ' t n) : EllPos M δ' t n :=
  ⟨conj (rep i.1.2)⁻¹ (gammaQ i.1.1 t), xpt_mem δ' t n i⟩

/-- `(Q, v) ↦` the class of `g⁻¹ γ_Q g`. -/
noncomputable def psi (δ' : ZMod M) (t : ℤ) (n : ℕ) (i : pairSet δ' t n) :
    MulAction.orbitRel.Quotient (Gamma1 M) (EllPos M δ' t n) :=
  Quotient.mk _ (xpt δ' t n i)

theorem psi_eq_iff (δ' : ZMod M) (t : ℤ) (n : ℕ) (i j : pairSet δ' t n) :
    psi δ' t n i = psi δ' t n j ↔ i.1.1 = j.1.1 ∧
      ∃ z ∈ MulAction.stabilizer SL(2, ℤ) (toBQF i.1.1), z • i.1.2 = j.1.2 := by
  obtain ⟨hQ, hv, he⟩ := (mem_pairSet δ' t n).1 i.2
  obtain ⟨hQ', hv', he'⟩ := (mem_pairSet δ' t n).1 j.2
  obtain ⟨hD, hR⟩ := mem_redForms.1 hQ
  obtain ⟨hD', hR'⟩ := mem_redForms.1 hQ'
  have hf := (gammaQ_props hD).2.2
  have hf' := (gammaQ_props hD').2.2
  have hg := rep_spec hv
  have hg' := rep_spec hv'
  rw [psi, psi, mk_eq_mk_iff]
  constructor
  · rintro ⟨h, hh⟩
    have hx : conj (h : SL(2, ℤ)) (conj (rep j.1.2)⁻¹ (gammaQ j.1.1 t)) =
        conj (rep i.1.2)⁻¹ (gammaQ i.1.1 t) := congrArg Subtype.val hh
    have hk : conj (rep i.1.2 * h * (rep j.1.2)⁻¹) (gammaQ j.1.1 t) = gammaQ i.1.1 t := by
      rw [conj_mul, conj_mul, hx, conj_conj_inv]
    have hform : (rep i.1.2 * h * (rep j.1.2)⁻¹) • toBQF j.1.1 = toBQF i.1.1 := by
      rw [← hf, ← hf', ← formOf_conj, hk]
    have hred : (act (rep i.1.2 * h * (rep j.1.2)⁻¹)⁻¹ (toBQF j.1.1)).IsReduced := by
      rw [← smul_def, hform]; exact hR
    have heq : toBQF i.1.1 = toBQF j.1.1 := by rw [← hform, smul_def]; exact hR'.act_eq hred
    refine ⟨toBQF_injective heq, (rep i.1.2 * h * (rep j.1.2)⁻¹)⁻¹, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff, heq, hform, heq]
    · have e : (rep j.1.2)⁻¹ • j.1.2 = e1 M := inv_smul_eq_iff.2 hg'.symm
      rw [inv_smul_eq_iff, mul_smul, mul_smul, e, (mem_Gamma1_iff M _).1 h.2, hg]
  · rintro ⟨hQQ, z, hz, hzv⟩
    refine ⟨⟨(rep i.1.2)⁻¹ * z⁻¹ * rep j.1.2, ?_⟩, ?_⟩
    · rw [mem_Gamma1_iff, mul_smul, mul_smul, hg', ← hzv, inv_smul_smul, inv_smul_eq_iff, hg]
    · apply Subtype.ext
      show conj ((rep i.1.2)⁻¹ * z⁻¹ * rep j.1.2) (conj (rep j.1.2)⁻¹ (gammaQ j.1.1 t)) =
        conj (rep i.1.2)⁻¹ (gammaQ i.1.1 t)
      rw [← conj_mul, mul_assoc ((rep i.1.2)⁻¹ * z⁻¹), mul_inv_cancel, mul_one, conj_mul, ← hQQ]
      congr 1
      rw [← mem_stabilizer_iff_conj, hf]; exact inv_mem hz

theorem psi_surjective (δ' : ZMod M) (t : ℤ) (n : ℕ) : Function.Surjective (psi δ' t n) := by
  intro C
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C
  obtain ⟨hdet, htr, hpd, heig⟩ := mem_EllPos_iff.1 x.2
  obtain ⟨k, hk⟩ := exists_act_isReduced (formOf x.1) hpd
  have hkf : k⁻¹ • formOf x.1 = act k (formOf x.1) := by rw [smul_def, inv_inv]
  set Q : ℤ × ℤ × ℤ := ((act k (formOf x.1)).a, (act k (formOf x.1)).b, (act k (formOf x.1)).c) with hQdef
  have hQf : toBQF Q = act k (formOf x.1) := rfl
  have hD : (toBQF Q).disc = t ^ 2 - 4 * n := by rw [hQf, disc_act, disc_formOf, htr, hdet]
  have hQ : Q ∈ redForms (t ^ 2 - 4 * n) := mem_redForms.2 ⟨hD, hQf ▸ hk⟩
  have hconj : conj k⁻¹ x.1 = gammaQ Q t := by
    obtain ⟨h1, -, h3⟩ := gammaQ_props hD
    exact eq_of_formOf_eq (by rw [formOf_conj, hkf, h3, hQf]) (by rw [trace_conj, htr, h1])
  have hv : IsExact M (k⁻¹ • e1 M) := isExact_smul (isExact_e1 M) _
  have he : Eig M δ' (gammaQ Q t) (k⁻¹ • e1 M) := by rw [← hconj, eig_conj_iff]; exact heig
  refine ⟨⟨(Q, k⁻¹ • e1 M), (mem_pairSet δ' t n).2 ⟨hQ, hv, he⟩⟩, ?_⟩
  have hg := rep_spec hv
  rw [psi, mk_eq_mk_iff]
  refine ⟨⟨(rep (k⁻¹ • e1 M))⁻¹ * k⁻¹, ?_⟩, ?_⟩
  · rw [mem_Gamma1_iff, mul_smul, inv_smul_eq_iff, hg]
  · apply Subtype.ext
    show conj ((rep (k⁻¹ • e1 M))⁻¹ * k⁻¹) x.1 = conj (rep (k⁻¹ • e1 M))⁻¹ (gammaQ Q t)
    rw [conj_mul, hconj]

theorem card_stab_xpt (δ' : ZMod M) (t : ℤ) (n : ℕ) (i : pairSet δ' t n) :
    Nat.card (MulAction.stabilizer (Gamma1 M) (xpt δ' t n i)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer SL(2, ℤ) (toBQF i.1.1)) i.1.2) := by
  obtain ⟨hQ, hv, he⟩ := (mem_pairSet δ' t n).1 i.2
  have hf := (gammaQ_props (mem_redForms.1 hQ).1).2.2
  have hg := rep_spec hv
  have hZ : ∀ z : SL(2, ℤ), z ∈ MulAction.stabilizer SL(2, ℤ) (toBQF i.1.1) ↔
      conj z (gammaQ i.1.1 t) = gammaQ i.1.1 t := by
    intro z; rw [← hf]; exact mem_stabilizer_iff_conj z _
  have hx : ((xpt δ' t n i : EllPos M δ' t n) : Mat) = conj (rep i.1.2)⁻¹ (gammaQ i.1.1 t) := rfl
  apply Nat.card_congr
  exact
    { toFun := fun h => ⟨⟨rep i.1.2 * h.1.1 * (rep i.1.2)⁻¹, by
          have hc : conj h.1.1 (xpt δ' t n i : Mat) = xpt δ' t n i :=
            congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 h.2)
          rw [hZ, conj_mul, conj_mul, ← hx, hc, hx, conj_conj_inv]⟩, by
          rw [MulAction.mem_stabilizer_iff]
          show (rep i.1.2 * h.1.1 * (rep i.1.2)⁻¹) • i.1.2 = i.1.2
          have e : (rep i.1.2)⁻¹ • i.1.2 = e1 M := inv_smul_eq_iff.2 hg.symm
          rw [mul_smul, mul_smul, e, (mem_Gamma1_iff M _).1 h.1.2, hg]⟩
      invFun := fun z => ⟨⟨(rep i.1.2)⁻¹ * z.1.1 * rep i.1.2, by
          have hz : z.1.1 • i.1.2 = i.1.2 := MulAction.mem_stabilizer_iff.1 z.2
          rw [mem_Gamma1_iff, mul_smul, mul_smul, hg, hz, inv_smul_eq_iff, hg]⟩, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          show conj ((rep i.1.2)⁻¹ * z.1.1 * rep i.1.2) (xpt δ' t n i : Mat) = xpt δ' t n i
          rw [hx, conj_mul, conj_mul, conj_conj_inv, (hZ _).1 z.1.2]⟩
      left_inv := fun h => by
        apply Subtype.ext; apply Subtype.ext
        show (rep i.1.2)⁻¹ * (rep i.1.2 * h.1.1 * (rep i.1.2)⁻¹) * rep i.1.2 = h.1.1
        group
      right_inv := fun z => by
        apply Subtype.ext; apply Subtype.ext
        show rep i.1.2 * ((rep i.1.2)⁻¹ * z.1.1 * rep i.1.2) * (rep i.1.2)⁻¹ = z.1.1
        group }

theorem card_fiber (δ' : ZMod M) (t : ℤ) (n : ℕ) (i : pairSet δ' t n) :
    Nat.card {j // psi δ' t n j = psi δ' t n i} =
      (MulAction.orbit (MulAction.stabilizer SL(2, ℤ) (toBQF i.1.1)) i.1.2).ncard := by
  rw [← Nat.card_coe_set_eq]
  apply Nat.card_congr
  obtain ⟨hQ, hv, he⟩ := (mem_pairSet δ' t n).1 i.2
  have hf := (gammaQ_props (mem_redForms.1 hQ).1).2.2
  exact
    { toFun := fun j => ⟨j.1.1.2, by
        obtain ⟨-, z, hz, hzv⟩ := (psi_eq_iff δ' t n i j.1).1 j.2.symm
        exact MulAction.mem_orbit_iff.2 ⟨⟨z, hz⟩, hzv⟩⟩
      invFun := fun w =>
        have hmem : (i.1.1, w.1) ∈ pairSet δ' t n := by
          obtain ⟨⟨z, hz⟩, hzw⟩ := MulAction.mem_orbit_iff.1 w.2
          have hzw' : z • i.1.2 = w.1 := hzw
          have hc : conj z (gammaQ i.1.1 t) = gammaQ i.1.1 t := by
            rw [← mem_stabilizer_iff_conj, hf]; exact hz
          refine (mem_pairSet δ' t n).2 ⟨hQ, ?_, ?_⟩
          · show IsExact M w.1
            rw [← hzw']; exact isExact_smul hv z
          · show Eig M δ' (gammaQ i.1.1 t) w.1
            rw [← hzw', ← hc, eig_conj_iff]; exact he
        ⟨⟨(i.1.1, w.1), hmem⟩, by
          obtain ⟨⟨z, hz⟩, hzw⟩ := MulAction.mem_orbit_iff.1 w.2
          exact ((psi_eq_iff δ' t n i ⟨(i.1.1, w.1), hmem⟩).2 ⟨rfl, z, hz, hzw⟩).symm⟩
      left_inv := fun j => by
        obtain ⟨hQQ, -⟩ := (psi_eq_iff δ' t n i j.1).1 j.2.symm
        exact Subtype.ext (Subtype.ext (Prod.ext hQQ rfl))
      right_inv := fun w => rfl }

/-- **Main theorem (positive orientation).** `Σ_{Γ₁(M)-classes in EllPos} 1/#centraliser = ellCount M δ' t n`. -/
theorem classSum_EllPos (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    classSum (Gamma1 M) (EllPos M δ' t n) = ellCount M δ' t n := by
  rw [classSum, finsum_eq_sum_fiber (psi δ' t n) (psi_surjective δ' t n), ← sum_pairSet,
    ← Finset.sum_coe_sort (pairSet δ' t n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hQ, -, -⟩ := (mem_pairSet δ' t n).1 i.2
  have h1 : Nat.card (MulAction.stabilizer (Gamma1 M) (psi δ' t n i).out) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer SL(2, ℤ) (toBQF i.1.1)) i.1.2) := by
    rw [psi, card_stab_out, card_stab_xpt]
  rw [h1, card_fiber, div_div, ← Nat.cast_mul, card_stab_mul_ncard_orbit (mem_redForms.1 hQ).2]

theorem finite_EllPos_quot (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    Finite (MulAction.orbitRel.Quotient (Gamma1 M) (EllPos M δ' t n)) :=
  Finite.of_surjective _ (psi_surjective δ' t n)

end Main

end RamanujanPetersson.S3.Conj


