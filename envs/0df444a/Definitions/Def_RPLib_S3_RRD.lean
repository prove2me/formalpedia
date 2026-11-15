-- Prove2me | Definitions.Def_RPLib_S3_RRD
-- name    : RPLib_S3_RRD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:25:32.039564+00:00
-- url     : https://prove2.me/theorems/7e5d5a2b-d3b8-47a6-96c3-5049e55799cf
-- title:
--   Weight-two Ramanujan-Petersson library: the pole-divisor family and constant field extensions
-- statement:
--   The pole-divisor family and constant field extensions.
--
--   For the separating element `x` with pole divisor `B`, `L(n B) = Rfin ∩ x ^ n Rinf`
--   (`mem_LF_poleB`). For a constant field extension `F' / L` of `F / Fq` (given in coordinates by an
--   `Fq`-basis `c` of `L`: the images of `c` form an `F`-basis of `F'`, both rings of integers are spanned
--   coordinatewise, and `x` is kept), `ℓ'(n B') = ℓ(n B)` for every `n`; hence `ℓ'(0) = ℓ(0)`,
--   `deg B' = deg B`, the genus is invariant (`IsConstExt.genusF_eq`) and a full constant field stays full.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_RRC

/-!
# Riemann-Roch, part D: the pole-divisor family and constant field extensions

For the separating element `x` with pole divisor `B`, `L(n B) = Rfin ∩ x ^ n Rinf`
(`mem_LF_poleB`). For a constant field extension `F' / L` of `F / Fq` (given in coordinates by an
`Fq`-basis `c` of `L`: the images of `c` form an `F`-basis of `F'`, both rings of integers are spanned
coordinatewise, and `x` is kept), `ℓ'(n B') = ℓ(n B)` for every `n`; hence `ℓ'(0) = ℓ(0)`,
`deg B' = deg B`, the genus is invariant (`IsConstExt.genusF_eq`) and a full constant field stays full.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.RR

theorem mem_range_iff_valuation_le_one {S : Type*} [CommRing S] [IsDedekindDomain S] {K : Type*}
    [Field K] [Algebra S K] [IsFractionRing S K] (f : K) :
    f ∈ (algebraMap S K).range ↔ ∀ P : HeightOneSpectrum S, P.valuation K f ≤ 1 := by
  refine ⟨?_, HeightOneSpectrum.mem_integers_of_valuation_le_one K f⟩
  rintro ⟨r, rfl⟩ P
  exact P.valuation_le_one r

section PoleFamily

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem poleB_inl (P : HeightOneSpectrum (Places.Rfin Fq F)) : poleB Fq F (Sum.inl P) = 0 := by
  have hv : ffv Fq F (Sum.inl P) (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_right.2 ((log_nonpos_iff' hv).2 (ffv_xF_inl P))

theorem poleB_inr (P : HeightOneSpectrum (Places.Rinf Fq F)) :
    poleB Fq F (Sum.inr P) = log (P.valuation F (xF Fq F)) := by
  have hv : ffv Fq F (Sum.inr P) (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
  rw [poleB, Finsupp.sup_apply, Finsupp.neg_apply, Data.div_apply, ffData_v, neg_neg,
    Finsupp.coe_zero, Pi.zero_apply]
  exact sup_eq_left.2 ((log_nonneg_iff' hv).2 (one_le_ffv_xF_inr P))

/-- `L(n B) = Rfin ∩ x ^ n Rinf` for the pole divisor `B` of `x`. -/
theorem mem_LF_poleB (n : ℕ) (f : F) :
    f ∈ LF Fq F (n • poleB Fq F) ↔ f ∈ (algebraMap (Places.Rfin Fq F) F).range ∧
      f * (xF Fq F)⁻¹ ^ n ∈ (algebraMap (Places.Rinf Fq F) F).range := by
  rw [mem_range_iff_valuation_le_one, mem_range_iff_valuation_le_one, Data.mem_LD, Sum.forall]
  refine and_congr (forall_congr' fun P => ?_) (forall_congr' fun P => ?_)
  · rw [Finsupp.smul_apply, poleB_inl, smul_zero, exp_zero]; rfl
  · have hv : P.valuation F (xF Fq F) ≠ 0 := (Valuation.ne_zero_iff _).2 xF_ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℤ, P.valuation F (xF Fq F) = exp k := ⟨_, (exp_log hv).symm⟩
    show P.valuation F f ≤ _ ↔ _
    rw [Finsupp.smul_apply, poleB_inr, hk, log_exp, map_mul, map_pow, map_inv₀, hk, ← exp_neg,
      ← exp_nsmul, mul_comm, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_mul_le_exp_iff, smul_neg,
      sub_neg_eq_add, zero_add]

theorem degD_poleB_pos : 0 < (poleB Fq F).deg := by
  have := (bas Fq F).index_nonempty
  have hpos : 0 < Fintype.card (Module.Free.ChooseBasisIndex Fq[X] (Places.Rfin Fq F)) :=
    Fintype.card_pos
  rw [← ffData_degD, degD_poleB]; exact_mod_cast hpos

end PoleFamily

section ConstantFieldExtension

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']

/-- `F' / L` is the constant field extension `L F` of `F / Fq`, in coordinates: for an `Fq`-basis
`c` of `L`, the elements `c j` form an `F`-basis of `F'`, an element `Σ f_j c_j` lies in the ring
of integers over `L[x]` (resp. over the valuation ring at `x = ∞`) iff every coordinate `f_j` lies in
the corresponding ring of `F`, and the separating element `x` of `F'` is that of `F`
(`Rfin L F' = L ⊗ Rfin Fq F`, `Rinf L F' = L ⊗ Rinf Fq F`). -/
structure IsConstExt {ι : Type*} [Fintype ι] (c : Module.Basis ι Fq L) : Prop where
  linearIndependent : LinearIndependent F fun j => algebraMap L F' (c j)
  span : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j))
  xF_eq : algebraMap F F' (xF Fq F) = xF L F'
  fin : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rfin L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rfin Fq F) F).range
  inf : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap (Places.Rinf L F') F').range ↔
    ∀ j, f j ∈ (algebraMap (Places.Rinf Fq F) F).range

variable {Fq L}
variable {ι : Type*} [Fintype ι]

/-- The coordinate map `(f_j) ↦ Σ f_j c_j`. -/
noncomputable def coordMap (c : Module.Basis ι Fq L) : (ι → F) →ₗ[Fq] F' where
  toFun f := ∑ j, f j • algebraMap L F' (c j)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.smul_sum, smul_assoc]

variable {F F'}
variable {c : Module.Basis ι Fq L}

theorem coordMap_apply (f : ι → F) : coordMap F F' c f = ∑ j, f j • algebraMap L F' (c j) := rfl

theorem IsConstExt.mem_LF_iff (h : IsConstExt Fq F L F' c) (n : ℕ) (f : ι → F) :
    coordMap F F' c f ∈ LF L F' (n • poleB L F') ↔ ∀ j, f j ∈ LF Fq F (n • poleB Fq F) := by
  simp only [mem_LF_poleB, coordMap_apply]
  rw [h.fin, ← h.xF_eq]
  have e : (∑ j, f j • algebraMap L F' (c j)) * (algebraMap F F' (xF Fq F))⁻¹ ^ n =
      ∑ j, (f j * (xF Fq F)⁻¹ ^ n) • algebraMap L F' (c j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, map_inv₀]; ring
  rw [e, h.inf, forall_and]

/-- The coordinate isomorphism `L(D)^ι ≃ L'(D')` (over `Fq`) for a pair of divisors whose
Riemann-Roch spaces correspond coordinatewise. -/
noncomputable def IsConstExt.psi (_h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    (ι → LF Fq F D) →ₗ[Fq] LF L F' D' where
  toFun f := ⟨coordMap F F' c fun j => (f j : F), (hD _).2 fun j => (f j).2⟩
  map_add' f g := Subtype.ext (by
    simp only [Pi.add_apply, Submodule.coe_add]
    exact map_add (coordMap F F' c) (fun j => (f j : F)) fun j => (g j : F))
  map_smul' a f := Subtype.ext (by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply]
    exact map_smul (coordMap F F' c) a fun j => (f j : F))

theorem IsConstExt.psi_bijective (h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    Function.Bijective (h.psi hD) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : coordMap F F' c (fun j => (f j : F)) = 0 := congrArg Subtype.val hf
    rw [coordMap_apply] at h0
    funext j
    exact Subtype.ext (Fintype.linearIndependent_iff.1 h.linearIndependent _ h0 j)
  · intro y
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1
      (h.span (Submodule.mem_top (x := (y : F'))))
    have hgy : coordMap F F' c g = y := hg
    have hmem := (hD g).1 (by rw [hgy]; exact y.2)
    exact ⟨fun j => ⟨g j, hmem j⟩, Subtype.ext hgy⟩

/-- **Invariance of `ℓ` under constant field extension**: `ℓ'(D') = ℓ(D)` whenever `L'(D')` is
`L(D)` coordinatewise (`L'(D') = L ⊗ L(D)`). -/
theorem IsConstExt.ellF_eq (h : IsConstExt Fq F L F' c) {D : Places.Divisor Fq F}
    {D' : Places.Divisor L F'}
    (hD : ∀ f : ι → F, coordMap F F' c f ∈ LF L F' D' ↔ ∀ j, f j ∈ LF Fq F D) :
    ellF L F' D' = ellF Fq F D := by
  have := finiteDimensional_LF (Fq := Fq) (F := F) D
  have : Module.Finite Fq L := Module.Finite.of_finite
  have e1 := (LinearEquiv.ofBijective (h.psi hD) (h.psi_bijective hD)).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Module.finrank_mul_finrank Fq L (LF L F' D'), ← Module.finrank_eq_card_basis c] at e1
  have hpos : 0 < Module.finrank Fq L := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos e1).symm

/-- `ℓ'(n B') = ℓ(n B)` for the pole divisors of `x` in the constant field extension. -/
theorem IsConstExt.ellF_poleB (h : IsConstExt Fq F L F' c) (n : ℕ) :
    ellF L F' (n • poleB L F') = ellF Fq F (n • poleB Fq F) :=
  h.ellF_eq (h.mem_LF_iff n)

theorem IsConstExt.ellF_zero (h : IsConstExt Fq F L F' c) : ellF L F' 0 = ellF Fq F 0 := by
  simpa using h.ellF_poleB 0

/-- **Invariance of the genus under constant field extension** (together with `deg B' = deg B`). -/
theorem IsConstExt.genusF_eq_and (h : IsConstExt Fq F L F' c) :
    genusF L F' = genusF Fq F ∧ (poleB L F').deg = (poleB Fq F).deg := by
  have ha : 0 < (poleB Fq F).deg := degD_poleB_pos
  have ha' : 0 < (poleB L F').deg := degD_poleB_pos
  have ha1 : (1 : ℤ) ≤ (poleB Fq F).deg := by omega
  have ha1' : (1 : ℤ) ≤ (poleB L F').deg := by omega
  have h0 := h.ellF_zero
  have key : ∀ m : ℕ, 2 * (genusF Fq F + genusF L F') + 1 ≤ m →
      ((ellF Fq F (m • poleB Fq F) : ℤ) = m * (poleB Fq F).deg + ellF Fq F 0 - genusF Fq F) ∧
      ((ellF Fq F (m • poleB Fq F) : ℤ) = m * (poleB L F').deg + ellF Fq F 0 - genusF L F') := by
    intro m hm
    have hm' : (2 * ((genusF Fq F : ℤ) + genusF L F') + 1 : ℤ) ≤ m := by exact_mod_cast hm
    have hg : (0 : ℤ) ≤ genusF Fq F := by positivity
    have hg' : (0 : ℤ) ≤ genusF L F' := by positivity
    have h00 : (0 : ℤ) ≤ ellF Fq F 0 := by positivity
    have h00' : (0 : ℤ) ≤ ellF L F' 0 := by positivity
    have hma : (m : ℤ) * 1 ≤ m * (poleB Fq F).deg := mul_le_mul_of_nonneg_left ha1 (by positivity)
    have hma' : (m : ℤ) * 1 ≤ m * (poleB L F').deg := mul_le_mul_of_nonneg_left ha1' (by positivity)
    refine ⟨?_, ?_⟩
    · have := Data.ell_eq_of_large_degD (ffData_axioms (Fq := Fq) (F := F))
        (D := m • poleB Fq F) (by
          rw [Data.degD_nsmul, ffData_degD]
          change 2 * ((genusF Fq F : ℕ) : ℤ) - 2 * ((ellF Fq F 0 : ℕ) : ℤ) < _
          linarith)
      rw [Data.degD_nsmul, ffData_degD] at this
      exact this
    · have := Data.ell_eq_of_large_degD (ffData_axioms (Fq := L) (F := F'))
        (D := m • poleB L F') (by
          rw [Data.degD_nsmul, ffData_degD]
          change 2 * ((genusF L F' : ℕ) : ℤ) - 2 * ((ellF L F' 0 : ℕ) : ℤ) < _
          linarith)
      rw [Data.degD_nsmul, ffData_degD] at this
      change ((ellF L F' (m • poleB L F') : ℕ) : ℤ) = _ + ((ellF L F' 0 : ℕ) : ℤ) -
        ((genusF L F' : ℕ) : ℤ) at this
      rw [h.ellF_poleB m, h0] at this
      exact this
  obtain ⟨h1, h3⟩ := key _ le_rfl
  obtain ⟨h2, h4⟩ := key _ (Nat.le_succ _)
  push_cast at h1 h2 h3 h4
  have haa : (poleB Fq F).deg = (poleB L F').deg := by linear_combination h1 - h2 - h3 + h4
  refine ⟨?_, haa.symm⟩
  have : (genusF Fq F : ℤ) = genusF L F' := by
    linear_combination h1 - h3 + (2 * ((genusF Fq F : ℤ) + genusF L F') + 1) * haa
  exact_mod_cast this.symm

theorem IsConstExt.genusF_eq (h : IsConstExt Fq F L F' c) : genusF L F' = genusF Fq F :=
  h.genusF_eq_and.1

theorem IsConstExt.deg_poleB (h : IsConstExt Fq F L F' c) : (poleB L F').deg = (poleB Fq F).deg :=
  h.genusF_eq_and.2

/-- A full constant field stays full under constant field extension. -/
theorem IsConstExt.constField_eq_bot (h : IsConstExt Fq F L F' c)
    (hk : Places.constField Fq F = ⊥) : Places.constField L F' = ⊥ := by
  have h1 : ellF L F' 0 = 1 := by rw [h.ellF_zero]; exact ellF_zero_of_bot hk
  rw [RamanujanPetersson.RR.ellF_zero] at h1
  exact IntermediateField.finrank_eq_one_iff.1 h1

end ConstantFieldExtension

end RamanujanPetersson.RR


