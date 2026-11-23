-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryRootEmbedding
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryRootEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:54.3998+00:00
-- url     : https://prove2.me/theorems/55dca25e-eab1-40d8-9c48-1aa60c9791f6
-- title:
--   Unitary Root Embedding
-- statement:
--   Definitions and structural lemmas for Unitary Root Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryRootEmbedding.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT :
    {A : Type} → [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) ↦ (M.map (⇑σ : A → A)).transpose
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m p q : Type} [Fintype p]
    (M : Matrix m p A) (N : Matrix p q A) : cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [DecidableEq n] :
    cT σ (1 : Matrix n n A) = 1 := by
  simp only [cT]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
theorem cT_add {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M N : Matrix m p A) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  simp [cT]
theorem cT_sub {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M N : Matrix m p A) :
    cT σ (M - N) = cT σ M - cT σ N := by
  ext i j
  simp [cT]
theorem cT_cT {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x : A, σ (σ x) = x)
    {m p : Type} (M : Matrix m p A) : cT σ (cT σ M) = M := by
  ext i j
  simp [cT, hσ]
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {a b : GL n A},
      a ∈ {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        b ∈ {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
          a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J a b ha hb
  have ha' : cT σ (a : Matrix n n A) * J * (a : Matrix n n A) = J := ha
  have hb' : cT σ (b : Matrix n n A) * J * (b : Matrix n n A) = J := hb
  show cT σ ((a * b : GL n A) : Matrix n n A) * J * ((a * b : GL n A) : Matrix n n A) = J
  rw [Units.val_mul, cT_mul]
  calc _ = cT σ (b : Matrix n n A) * (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha', hb']
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A), UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑(1 : GL n A) : Matrix n n A) * J * (↑(1 : GL n A) : Matrix n n A) = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {g : GL n A},
      g ∈ {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have h1 : (g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : cT σ ((g⁻¹ : GL n A) : Matrix n n A) * cT σ (g : Matrix n n A) = 1 := by
    rw [← cT_mul, h1, cT_one]
  show cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A) = J
  calc _ = cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
        ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg']
    _ = (cT σ ((g⁻¹ : GL n A) : Matrix n n A) * cT σ (g : Matrix n n A)) * J *
        ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
        (J : Matrix n n A) ↦
      { carrier := {g : GL n A | UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J},
        mul_mem' := @UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux2 A inst n inst_1 inst_2 σ J, one_mem' := UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux3 σ J,
        inv_mem' := @UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux4 A inst n inst_1 inst_2 σ J : Subgroup (GL n A) }
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.antiJ :
    (L : Type) → [Field L] → (n : ℕ) → Matrix (Fin n) (Fin n) L :=
    fun (L : Type) [Field L] (n : ℕ) (i j : Fin n) ↦ if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (1 : L) else (0 : L)
@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU :
    {L : Type} → [inst : Field L] → (L →+* L) → (n : ℕ) → Subgroup (GL (Fin n) L) :=
    fun {L : Type} [Field L] (σ : L →+* L) (n : ℕ) ↦ UpperTheory.Reformulated.B.AntidiagonalWeylElement.UJ σ (UpperTheory.Reformulated.B.AntidiagonalWeylElement.antiJ L n)
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsBorelU :
    {L : Type} → [inst : Field L] → {σ : L →+* L} → {n : ℕ} → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) → Prop :=
    fun {L : Type} [Field L] {σ : L →+* L} {n : ℕ} (b : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)) ↦
      ∀ (i j : Fin n), j < i → (↑(↑b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (0 : L)
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsUnipU :
    {L : Type} → [inst : Field L] → {σ : L →+* L} → {n : ℕ} → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) → Prop :=
    fun {L : Type} [Field L] {σ : L →+* L} {n : ℕ} (u : ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)) ↦
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.IsBorelU u ∧ ∀ (i : Fin n), (↑(↑u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = (1 : L)
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.cM :
    {n : ℕ} → (L : Type) → [Field L] → (Fin (2 : ℕ) → Fin n) → Matrix (Fin n) (Fin (2 : ℕ)) L :=
    fun {n : ℕ} (L : Type) [Field L] (c : Fin (2 : ℕ) → Fin n) (b : Fin n) (p : Fin (2 : ℕ)) ↦
      if b = c p then (1 : L) else (0 : L)
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux12 :
    ∀ (n a : ℕ), (2 : ℕ) * (a + (2 : ℕ)) ≤ n → ∀ (p : Fin (2 : ℕ)), a + (↑p : ℕ) < n := by
  intro n a h p
  have := p.isLt
  omega
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.cI :
    (n a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → Fin (2 : ℕ) → Fin n :=
    fun (n a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) (p : Fin (2 : ℕ)) ↦
      (⟨a + (↑p : ℕ), UpperTheory.Reformulated.B.AntidiagonalWeylElement.aux12 n a h p⟩ : Fin n)
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.zero_contDiffOn_supported :
    ∀ (n a : ℕ), (2 : ℕ) * (a + (2 : ℕ)) ≤ n → ∀ (p : Fin (2 : ℕ)), n - (2 : ℕ) - a + (↑p : ℕ) < n := by
  intro n a h p
  have := p.isLt
  omega
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.cJ :
    (n a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → Fin (2 : ℕ) → Fin n :=
    fun (n a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) (p : Fin (2 : ℕ)) ↦
      (⟨n - (2 : ℕ) - a + (↑p : ℕ), UpperTheory.Reformulated.B.AntidiagonalWeylElement.zero_contDiffOn_supported n a h p⟩ : Fin n)
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM :
    {L : Type} →
      [Field L] →
        {n : ℕ} →
          (a : ℕ) →
            (2 : ℕ) * (a + (2 : ℕ)) ≤ n →
              Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L → Matrix (Fin n) (Fin n) L :=
    fun {L : Type} [Field L] {n : ℕ} (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n)
        (X Y : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) ↦
      (1 : Matrix (Fin n) (Fin n) L) +
          UpperTheory.Reformulated.B.AntidiagonalWeylElement.cM L (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cI n a h) * (X - (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L)) *
            (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cM L (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cI n a h)).transpose +
        UpperTheory.Reformulated.B.AntidiagonalWeylElement.cM L (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cJ n a h) * (Y - (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L)) *
          (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cM L (UpperTheory.Reformulated.B.AntidiagonalWeylElement.cJ n a h)).transpose
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 :
    (L : Type) → [Field L] → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L :=
    fun (L : Type) [Field L] ↦ !![(0 : L), (1 : L); (1 : L), (0 : L)]
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner :
    {L : Type} → [inst : Field L] → (L →+* L) → GL (Fin (2 : ℕ)) L → Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L :=
    fun {L : Type} [Field L] (σ : L →+* L) (h : GL (Fin (2 : ℕ)) L) ↦
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L * UpperTheory.Reformulated.B.AntidiagonalWeylElement.cT σ (↑h⁻¹ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) * UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem weyl_mul_weyl (L : Type) [Field L] : w2 L * w2 L = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]
theorem w2_transpose_eq_self (L : Type) [Field L] : (w2 L).transpose = w2 L := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]
theorem conj_transpose_antidiag_fixed {L : Type} [Field L] (σ : L →+* L) : cT σ (w2 L) = w2 L := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, cT]
theorem partner_one {L : Type} [Field L] (σ : L →+* L) : partner σ 1 = 1 := by
  simp only [partner, inv_one, Units.val_one, cT_one, Matrix.mul_one, weyl_mul_weyl]
theorem partner_mul {L : Type} [Field L] (σ : L →+* L) (g g' : GL (Fin 2) L) :
    partner σ (g * g') = partner σ g * partner σ g' := by
  simp only [partner, mul_inv_rev, Units.val_mul, cT_mul]
  calc _ = w2 L * cT σ ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * 1 *
        cT σ ((g'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * w2 L := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by
        rw [← weyl_mul_weyl L]
        simp only [Matrix.mul_assoc]
theorem cM_tr_mul {n : ℕ} (L : Type) [Field L] (c d : Fin 2 → Fin n) (p q : Fin 2) :
    ((cM L c).transpose * cM L d) p q = if c p = d q then 1 else 0 := by
  simp [Matrix.mul_apply, cM, Matrix.transpose_apply]
  exact if_congr eq_comm rfl rfl
theorem cII {n a : ℕ} (L : Type) [Field L] (h : 2 * (a + 2) ≤ n) :
    (cM L (cI n a h)).transpose * cM L (cI n a h) = 1 := by
  ext p q
  rw [cM_tr_mul, Matrix.one_apply]
  simp [cI, Fin.ext_iff]
theorem cJJ {n a : ℕ} (L : Type) [Field L] (h : 2 * (a + 2) ≤ n) :
    (cM L (cJ n a h)).transpose * cM L (cJ n a h) = 1 := by
  ext p q
  rw [cM_tr_mul, Matrix.one_apply]
  simp [cJ, Fin.ext_iff]
theorem cIJ {n a : ℕ} (L : Type) [Field L] (h : 2 * (a + 2) ≤ n) :
    (cM L (cI n a h)).transpose * cM L (cJ n a h) = 0 := by
  ext p q
  rw [cM_tr_mul, if_neg]
  · rfl
  · have := p.isLt
    simp only [cI, cJ, Fin.ext_iff]
    omega
theorem cJI {n a : ℕ} (L : Type) [Field L] (h : 2 * (a + 2) ≤ n) :
    (cM L (cJ n a h)).transpose * cM L (cI n a h) = 0 := by
  ext p q
  rw [cM_tr_mul, if_neg]
  · rfl
  · have := q.isLt
    simp only [cI, cJ, Fin.ext_iff]
    omega
theorem sand {m r : Type} [Fintype r] [Fintype m] {L : Type} [Field L]
    (P R S T : Matrix m r L) (A B : Matrix r r L) :
    P * A * T.transpose * (R * B * S.transpose) = P * (A * (T.transpose * R) * B) * S.transpose := by
  simp only [Matrix.mul_assoc]
theorem blk_mul {m r : Type} [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r]
    {L : Type} [Field L] (P Q : Matrix m r L)
    (PP : P.transpose * P = 1) (QQ : Q.transpose * Q = 1)
    (PQ : P.transpose * Q = 0) (QP : Q.transpose * P = 0) (X X' Y Y' : Matrix r r L) :
    1 + P * (X * X' - 1) * P.transpose + Q * (Y * Y' - 1) * Q.transpose =
      (1 + P * (X - 1) * P.transpose + Q * (Y - 1) * Q.transpose) *
        (1 + P * (X' - 1) * P.transpose + Q * (Y' - 1) * Q.transpose) := by
  have e1 : X * X' - 1 = (X - 1) * (X' - 1) + (X - 1) + (X' - 1) := by noncomm_ring
  have e2 : Y * Y' - 1 = (Y - 1) * (Y' - 1) + (Y - 1) + (Y' - 1) := by noncomm_ring
  have s1 : P * (X - 1) * P.transpose * (P * (X' - 1) * P.transpose) = P * ((X - 1) * (X' - 1)) * P.transpose := by
    rw [sand, PP, Matrix.mul_one]
  have s2 : Q * (Y - 1) * Q.transpose * (Q * (Y' - 1) * Q.transpose) = Q * ((Y - 1) * (Y' - 1)) * Q.transpose := by
    rw [sand, QQ, Matrix.mul_one]
  have s3 : P * (X - 1) * P.transpose * (Q * (Y' - 1) * Q.transpose) = 0 := by
    rw [sand, PQ]; simp
  have s4 : Q * (Y - 1) * Q.transpose * (P * (X' - 1) * P.transpose) = 0 := by
    rw [sand, QP]; simp
  rw [e1, e2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, s1, s2, s3, s4]
  abel
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM_one_partner_eq_one :
    ∀ {L : Type} [inst : Field L] {n : ℕ} (σ : L →+* L) (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n),
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM a h (↑(1 : GL (Fin (2 : ℕ)) L) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L)
          (UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner σ (1 : GL (Fin (2 : ℕ)) L)) =
        (1 : Matrix (Fin n) (Fin n) L) := by
  intro L _ n σ a h
  rw [partner_one, Units.val_one]
  simp [blockM]
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM_mul_alt :
    ∀ {L : Type} [inst : Field L] {n : ℕ} (σ : L →+* L) (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n)
      (g g' : GL (Fin (2 : ℕ)) L),
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM a h (↑(g * g') : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner σ (g * g')) =
        UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM a h (↑g : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner σ g) *
          UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM a h (↑g' : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner σ g') := by
  intro L _ n σ a h g g'
  rw [partner_mul, Units.val_mul]
  exact blk_mul _ _ (cII L h) (cJJ L h) (cIJ L h) (cJI L h) _ _ _ _
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootGL :
    {L : Type} →
      [inst : Field L] → {n : ℕ} → (L →+* L) → (a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → GL (Fin (2 : ℕ)) L →* GL (Fin n) L :=
    fun {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) ↦
      {
          toFun := fun (g : GL (Fin (2 : ℕ)) L) ↦
            UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM a h (↑g : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.partner σ g),
          map_one' := UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM_one_partner_eq_one σ a h, map_mul' := UpperTheory.Reformulated.B.AntidiagonalWeylElement.blockM_mul_alt σ a h :
          GL (Fin (2 : ℕ)) L →* Matrix (Fin n) (Fin n) L }.toHomUnits
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem blk_unit {m r : Type} [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r]
    {L : Type} [Field L] (P Q : Matrix m r L) (J : Matrix m m L) (w A B C D : Matrix r r L)
    (PP : P.transpose * P = 1) (QQ : Q.transpose * Q = 1)
    (PQ : P.transpose * Q = 0) (QP : Q.transpose * P = 0)
    (JP : J * P = Q * w) (JQ : J * Q = P * w)
    (PJ : P.transpose * J = w * Q.transpose) (QJ : Q.transpose * J = w * P.transpose)
    (e1 : w * D + A * w + A * w * D = 0) (e2 : w * C + B * w + B * w * C = 0) :
    (1 + P * A * P.transpose + Q * B * Q.transpose) * J *
      (1 + P * C * P.transpose + Q * D * Q.transpose) = J := by
  have st : (1 + P * A * P.transpose + Q * B * Q.transpose) * J =
      J + P * (A * w) * Q.transpose + Q * (B * w) * P.transpose := by
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, PJ, QJ]
  have t1 : J * (P * C * P.transpose) = Q * (w * C) * P.transpose := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JP]
    simp only [Matrix.mul_assoc]
  have t2 : J * (Q * D * Q.transpose) = P * (w * D) * Q.transpose := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JQ]
    simp only [Matrix.mul_assoc]
  have t3 : P * (A * w) * Q.transpose * (P * C * P.transpose) = 0 := by
    rw [sand, QP]; simp
  have t4 : P * (A * w) * Q.transpose * (Q * D * Q.transpose) = P * (A * w * D) * Q.transpose := by
    rw [sand, QQ, Matrix.mul_one]
  have t5 : Q * (B * w) * P.transpose * (P * C * P.transpose) = Q * (B * w * C) * P.transpose := by
    rw [sand, PP, Matrix.mul_one]
  have t6 : Q * (B * w) * P.transpose * (Q * D * Q.transpose) = 0 := by
    rw [sand, PQ]; simp
  have f1 : P * (w * D) * Q.transpose + P * (A * w) * Q.transpose + P * (A * w * D) * Q.transpose = 0 := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e1]; simp
  have f2 : Q * (w * C) * P.transpose + Q * (B * w) * P.transpose + Q * (B * w * C) * P.transpose = 0 := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e2]; simp
  have g1 := eq_neg_of_add_eq_zero_right f1
  have g2 := eq_neg_of_add_eq_zero_right f2
  rw [st]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, t1, t2, t3, t4, t5, t6]
  rw [g1, g2]
  abel
theorem antiJ_apply {L : Type} [Field L] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  have e : ((i : ℕ) + j + 1 = n) ↔ j = Fin.rev i := by
    rw [Fin.ext_iff, Fin.val_rev]
    have := i.isLt
    omega
  simp only [e]
theorem antiJ_apply' {L : Type} [Field L] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i = Fin.rev j then 1 else 0 := by
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  have e : ((i : ℕ) + j + 1 = n) ↔ i = Fin.rev j := by
    rw [Fin.ext_iff, Fin.val_rev]
    have := j.isLt
    omega
  simp only [e]
theorem antiJ_tr {L : Type} [Field L] {n : ℕ} : (antiJ L n).transpose = antiJ L n := by
  ext i j
  rw [Matrix.transpose_apply, antiJ_apply, antiJ_apply']
theorem J_mul {L : Type} [Field L] {n : ℕ} {p : Type} (M : Matrix (Fin n) p L) (i : Fin n) (q : p) :
    (antiJ L n * M) i q = M (Fin.rev i) q := by
  simp [Matrix.mul_apply, antiJ_apply]
theorem JP {L : Type} [Field L] {n a : ℕ} (h : 2 * (a + 2) ≤ n) :
    antiJ L n * cM L (cI n a h) = cM L (cJ n a h) * w2 L := by
  ext i p
  rw [J_mul]
  have := i.isLt
  fin_cases p <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, cM, w2, cI, cJ, Fin.ext_iff, Fin.val_rev] <;>
    split_ifs <;> first | rfl | (exfalso; omega)
theorem JQ {L : Type} [Field L] {n a : ℕ} (h : 2 * (a + 2) ≤ n) :
    antiJ L n * cM L (cJ n a h) = cM L (cI n a h) * w2 L := by
  ext i p
  rw [J_mul]
  have := i.isLt
  fin_cases p <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, cM, w2, cI, cJ, Fin.ext_iff, Fin.val_rev] <;>
    split_ifs <;> first | rfl | (exfalso; omega)
theorem PJ {L : Type} [Field L] {n a : ℕ} (h : 2 * (a + 2) ≤ n) :
    (cM L (cI n a h)).transpose * antiJ L n = w2 L * (cM L (cJ n a h)).transpose := by
  have := congrArg Matrix.transpose (JP (L := L) h)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_tr, w2_transpose_eq_self] at this
theorem QJ {L : Type} [Field L] {n a : ℕ} (h : 2 * (a + 2) ≤ n) :
    (cM L (cJ n a h)).transpose * antiJ L n = w2 L * (cM L (cI n a h)).transpose := by
  have := congrArg Matrix.transpose (JQ (L := L) h)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_tr, w2_transpose_eq_self] at this
theorem cT_cM {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (c : Fin 2 → Fin n) :
    cT σ (cM L c) = (cM L c).transpose := by
  ext i j
  simp only [cT, cM, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp
theorem cT_cM_tr {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (c : Fin 2 → Fin n) :
    cT σ (cM L c).transpose = cM L c := by
  ext i j
  simp only [cT, cM, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp
theorem cT_blockM {L : Type} [Field L] {n a : ℕ} (σ : L →+* L) (h : 2 * (a + 2) ≤ n)
    (X Y : Matrix (Fin 2) (Fin 2) L) :
    cT σ (blockM a h X Y) =
      1 + cM L (cI n a h) * (cT σ X - 1) * (cM L (cI n a h)).transpose +
        cM L (cJ n a h) * (cT σ Y - 1) * (cM L (cJ n a h)).transpose := by
  simp only [blockM, cT_add, cT_mul, cT_sub, cT_one, cT_cM, cT_cM_tr, Matrix.mul_assoc]
end UpperTheory.Reformulated.B.AntidiagonalWeylElement
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootGL_mem_unitary :
    ∀ {L : Type} [inst : Field L] {n : ℕ} (σ : L →+* L),
      (∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) →
        ∀ (a : ℕ) (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) (g : GL (Fin (2 : ℕ)) L),
          (UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootGL σ a h : GL (Fin (2 : ℕ)) L → GL (Fin n) L) g ∈ UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n := by
  intro L _ n σ hσ a h g
  show cT σ (blockM a h (g : Matrix (Fin 2) (Fin 2) L) (partner σ g)) * antiJ L n *
    blockM a h (g : Matrix (Fin 2) (Fin 2) L) (partner σ g) = antiJ L n
  rw [cT_blockM]
  have hg1 : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hw := weyl_mul_weyl L
  have k1 : cT σ (g : Matrix (Fin 2) (Fin 2) L) * w2 L * partner σ g = w2 L := by
    have : cT σ (g : Matrix (Fin 2) (Fin 2) L) * cT σ ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
      rw [← cT_mul, hg1, cT_one]
    calc _ = cT σ (g : Matrix (Fin 2) (Fin 2) L) * (w2 L * w2 L) *
          cT σ ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * w2 L := by
          simp only [partner, Matrix.mul_assoc]
      _ = _ := by rw [hw, Matrix.mul_one, this, Matrix.one_mul]
  have k2 : cT σ (partner σ g) * w2 L * (g : Matrix (Fin 2) (Fin 2) L) = w2 L := by
    have : cT σ (partner σ g) = w2 L * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * w2 L := by
      simp only [partner, cT_mul, conj_transpose_antidiag_fixed, cT_cT σ hσ, Matrix.mul_assoc]
    rw [this]
    calc _ = w2 L * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (w2 L * w2 L) *
          (g : Matrix (Fin 2) (Fin 2) L) := by simp only [Matrix.mul_assoc]
      _ = w2 L * (((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L)) := by
          rw [hw, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hg1, Matrix.mul_one]
  have e1 : w2 L * (partner σ g - 1) + (cT σ (g : Matrix (Fin 2) (Fin 2) L) - 1) * w2 L +
      (cT σ (g : Matrix (Fin 2) (Fin 2) L) - 1) * w2 L * (partner σ g - 1) = 0 := by
    calc _ = cT σ (g : Matrix (Fin 2) (Fin 2) L) * w2 L * partner σ g - w2 L := by noncomm_ring
      _ = 0 := by rw [k1, sub_self]
  have e2 : w2 L * ((g : Matrix (Fin 2) (Fin 2) L) - 1) + (cT σ (partner σ g) - 1) * w2 L +
      (cT σ (partner σ g) - 1) * w2 L * ((g : Matrix (Fin 2) (Fin 2) L) - 1) = 0 := by
    calc _ = cT σ (partner σ g) * w2 L * (g : Matrix (Fin 2) (Fin 2) L) - w2 L := by noncomm_ring
      _ = 0 := by rw [k2, sub_self]
  exact blk_unit _ _ _ (w2 L) _ _ _ _ (cII L h) (cJJ L h) (cIJ L h) (cJI L h) (JP h) (JQ h) (PJ h) (QJ h) e1 e2
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootHom :
    {L : Type} →
      [inst : Field L] →
        {n : ℕ} →
          (σ : L →+* L) →
            (∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) →
              (a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → GL (Fin (2 : ℕ)) L →* ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) :=
    fun {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (hσ : ∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) (a : ℕ)
        (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) ↦
      (UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootGL σ a h).codRestrict (UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootGL_mem_unitary σ hσ a h)
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.span_sub_smul_le_comap_mul_twKer :
    ∀ {L : Type} [inst : Field L],
      UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L * UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L = (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) := by
  intro L _
  exact weyl_mul_weyl L
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.wU :
    (L : Type) → [inst : Field L] → GL (Fin (2 : ℕ)) L :=
    fun (L : Type) [Field L] ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L, inv := UpperTheory.Reformulated.B.AntidiagonalWeylElement.w2 L, val_inv := UpperTheory.Reformulated.B.AntidiagonalWeylElement.span_sub_smul_le_comap_mul_twKer,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalWeylElement.span_sub_smul_le_comap_mul_twKer : (Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L)ˣ }
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR :
    {L : Type} →
      [inst : Field L] →
        {n : ℕ} →
          (σ : L →+* L) →
            (∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) →
              (a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) :=
    fun {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (hσ : ∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) (a : ℕ)
        (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) ↦
      (UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootHom σ hσ a h : GL (Fin (2 : ℕ)) L → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.wU L)
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.unipotent_mul_neg :
    ∀ {L : Type} [inst : Field L] (x : L),
      !![(1 : L), x; (0 : L), (1 : L)] * !![(1 : L), -x; (0 : L), (1 : L)] = (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) := by
  intro L _ x
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
theorem UpperTheory.Reformulated.B.AntidiagonalWeylElement.neg_unipotent_mul :
    ∀ {L : Type} [inst : Field L] (x : L),
      !![(1 : L), -x; (0 : L), (1 : L)] * !![(1 : L), x; (0 : L), (1 : L)] = (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L) := by
  intro L _ x
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.nU :
    {L : Type} → [inst : Field L] → L → GL (Fin (2 : ℕ)) L :=
    fun {L : Type} [Field L] (x : L) ↦
      { val := !![(1 : L), x; (0 : L), (1 : L)], inv := !![(1 : L), -x; (0 : L), (1 : L)],
        val_inv := UpperTheory.Reformulated.B.AntidiagonalWeylElement.unipotent_mul_neg x, inv_val := UpperTheory.Reformulated.B.AntidiagonalWeylElement.neg_unipotent_mul x : (Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) L)ˣ }
noncomputable def UpperTheory.Reformulated.B.AntidiagonalWeylElement.uR :
    {L : Type} →
      [inst : Field L] →
        {n : ℕ} →
          (σ : L →+* L) →
            (∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) →
              (a : ℕ) → (2 : ℕ) * (a + (2 : ℕ)) ≤ n → L → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n) :=
    fun {L : Type} [Field L] {n : ℕ} (σ : L →+* L) (hσ : ∀ (x : L), (σ : L → L) ((σ : L → L) x) = x) (a : ℕ)
        (h : (2 : ℕ) * (a + (2 : ℕ)) ≤ n) (x : L) ↦
      (UpperTheory.Reformulated.B.AntidiagonalWeylElement.rootHom σ hσ a h : GL (Fin (2 : ℕ)) L → ↥(UpperTheory.Reformulated.B.AntidiagonalWeylElement.GU σ n)) (UpperTheory.Reformulated.B.AntidiagonalWeylElement.nU x)
namespace UpperTheory.Reformulated.B.AntidiagonalWeylElement
abbrev Up {n : ℕ} {L : Type} [Field L] (M : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ i j : Fin n, j < i → M i j = 0) ∧ ∀ i : Fin n, M i i = 1
def pm {n : ℕ} (A A1 B B1 k : Fin n) : Fin n :=
  if k = A then A1 else if k = A1 then A else if k = B then B1 else if k = B1 then B else k
end UpperTheory.Reformulated.B.AntidiagonalWeylElement


