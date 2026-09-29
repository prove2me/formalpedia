-- Prove2me | Definitions.Def_RepTheory_GL2CongruenceSubgroup
-- name    : RepTheory_GL2CongruenceSubgroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/72271c90-9efc-5c6f-9024-f8495cfe6053
-- title:
--   Principal congruence subgroups of GL2​(Qp​)
-- statement:
--   Fix a prime $p$. For $n \in \mathbb{N}$, `gl2CongruenceSubgroup p n` is the subgroup $K_n$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ (Lean's `GL (Fin 2) ℚ_[p]`, units of the matrix ring) whose carrier consists of those $g$ for which every entry of $g - 1$ and every entry of $g^{-1} - 1$ has $p$-adic absolute value at most $p^{-n}$; membership is thus a two-sided entrywise closed-ball condition, recorded as an iff by `mem_gl2CongruenceSubgroup_iff`. For $n \ge 1$ the second half is automatic: `mem_gl2CongruenceSubgroup_iff_of_one_le` shows that $\|(g-1)_{ij}\| \le p^{-n}$ for all $i,j$ already forces the same bound for $g^{-1}-1$, so $K_n = 1 + p^n M_2(\mathbb{Z}_p)$ in the usual sense; for $n = 0$ the two conditions say that $g$ and $g^{-1}$ both have entries in $\mathbb{Z}_p$ (via `norm_sub_one_entry_le_one_iff`, which converts a bound on an entry of $M-1$ into the same bound on the entry of $M$ when the radius is $1$). The family is antitone in $n$, each $K_n$ is open, hence clopen, in $\mathrm{GL}_2(\mathbb{Q}_p)$, each $K_n$ is stable under conjugation by elements of $K_0$, and `normal_subgroupOf_gl2CongruenceSubgroup` states normality of $K_n$ as a subgroup of $K_0$. A further group of lemmas supplies the ultrametric entry estimates behind this: the norm of a $p$-adic number within distance $<1$ of $1$ is $1$, non-archimedean bounds for sums and products of entries, the bound $\|(AB)_{ij}\| \le ab$ from entrywise bounds, and, for $g$ with $\|(g-1)_{ij}\| \le \varepsilon < 1$, that $\|\det g\| = 1$ and that the entries of $g^{-1}$ are bounded by $1$ (computed through the explicit $2\times 2$ adjugate).
--
--   `gl2UnipotentPadic p x` is the invertible matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ with prescribed inverse $\begin{pmatrix}1 & -x\\ 0 & 1\end{pmatrix}$; it lies in $K_n$ as soon as $\|x\| \le p^{-n}$ and differs from $1$ whenever $x \ne 0$. Taking $x = p^n$ gives $K_n \ne \{1\}$, and $x = 1$ gives the strict inclusion $K_1 < K_0$. Finally, every neighbourhood of $1$ in $\mathrm{GL}_2(\mathbb{Q}_p)$ contains some $K_n$ (proved via the inducing embedding of the unit group into $M_2(\mathbb{Q}_p) \times M_2(\mathbb{Q}_p)^{\mathrm{op}}$ and an entrywise radius estimate for neighbourhoods of $1$ in $M_2(\mathbb{Q}_p)$), so the $K_n$ form a filter basis of $\mathcal{N}(1)$, indexed by $\mathbb{N}$ with no side condition; this yields the `NonarchimedeanGroup (GL (Fin 2) ℚ_[p])` instance, i.e. every neighbourhood of $1$ contains an open subgroup.
--
--   **Relation to Mathlib.** Mathlib's `CongruenceSubgroup` material concerns $\mathrm{SL}_2(\mathbb{Z})$; the $p$-adic filtration $K_n \subseteq \mathrm{GL}_2(\mathbb{Q}_p)$ defined here is the project's own. The target class `NonarchimedeanGroup` and the ultrametric ball lemmas used are Mathlib's.
--
--   **Where it is used.** These subgroups provide the level filtration at $p$ used in the smooth-representation theory of $\mathrm{GL}_2(\mathbb{Q}_p)$ on which the local analysis in this development rests: smoothness of vectors is tested against the $K_n$, and Hecke double-coset operators are formed relative to them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors

section EntryBounds

variable (p : ℕ) [Fact p.Prime]

theorem norm_eq_one_of_norm_sub_one_lt_one {x : ℚ_[p]} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have hne : ‖x - 1‖ ≠ ‖(1 : ℚ_[p])‖ := by
    rw [norm_one]
    exact ne_of_lt h
  have hmax := Padic.add_eq_max_of_ne hne
  rw [sub_add_cancel] at hmax
  rw [hmax, norm_one, max_eq_right (le_of_lt h)]

theorem padic_norm_add_le_of_le {x y : ℚ_[p]} {ε : ℝ} (hx : ‖x‖ ≤ ε) (hy : ‖y‖ ≤ ε) :
    ‖x + y‖ ≤ ε :=
  le_trans (Padic.nonarchimedean _ _) (max_le hx hy)

theorem padic_norm_mul_le_of_le_of_le_one {x y : ℚ_[p]} {ε : ℝ} (hx : ‖x‖ ≤ ε) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ ε := by
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ ε * 1 :=
        mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg _) hx)
    _ = ε := mul_one ε

theorem padic_norm_mul_le_of_le_one_of_le {x y : ℚ_[p]} {ε : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ ε) :
    ‖x * y‖ ≤ ε := by
  rw [mul_comm]
  exact padic_norm_mul_le_of_le_of_le_one p hy hx

theorem norm_matrix_one_entry_le_one (i j : Fin 2) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h]

theorem norm_entry_le_one_of_sub_entry_le {A : Matrix (Fin 2) (Fin 2) ℚ_[p]} {ε : ℝ}
    (hε : ε ≤ 1) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ ε) (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
  have h : A i j = (A - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
    rw [Matrix.sub_apply]
    ring
  rw [h]
  exact padic_norm_add_le_of_le p (le_trans (hA i j) hε) (norm_matrix_one_entry_le_one p i j)

theorem norm_matrix_mul_entry_le {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {a b : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin 2) :
    ‖(A * B) i j‖ ≤ a * b := by
  have ha0 : (0 : ℝ) ≤ a := le_trans (norm_nonneg _) (hA i j)
  have hb0 : (0 : ℝ) ≤ b := le_trans (norm_nonneg _) (hB i j)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_) <;>
  · rw [norm_mul]
    exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) ha0

theorem norm_det_eq_one_of_sub_entry_le {ε : ℝ} (hε : ε < 1) (g : GL (Fin 2) ℚ_[p])
    (hg : ∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε) :
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 := by
  set A := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hA
  have hε0 : (0 : ℝ) ≤ ε := le_trans (norm_nonneg _) (hg 0 0)
  have ha : A 0 0 = (A - 1) 0 0 + 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    ring
  have hd : A 1 1 = (A - 1) 1 1 + 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    ring
  have hb : A 0 1 = (A - 1) 0 1 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)]
    ring
  have hc : A 1 0 = (A - 1) 1 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by decide)]
    ring
  have hkey : A.det - 1
      = ((A - 1) 0 0 * (A - 1) 1 1 + (A - 1) 0 0)
        + ((A - 1) 1 1 + -((A - 1) 0 1 * (A - 1) 1 0)) := by
    rw [Matrix.det_fin_two, ha, hb, hc, hd]
    ring
  apply norm_eq_one_of_norm_sub_one_lt_one p
  have hbound : ‖A.det - 1‖ ≤ ε := by
    rw [hkey]
    refine padic_norm_add_le_of_le p (padic_norm_add_le_of_le p ?_ (hg 0 0))
      (padic_norm_add_le_of_le p (hg 1 1) ?_)
    · exact padic_norm_mul_le_of_le_of_le_one p (hg 0 0) (le_trans (hg 1 1) (le_of_lt hε))
    · rw [norm_neg]
      exact padic_norm_mul_le_of_le_of_le_one p (hg 0 1) (le_trans (hg 1 0) (le_of_lt hε))
  exact lt_of_le_of_lt hbound hε

theorem norm_inv_entry_le_one_of_sub_entry_le {ε : ℝ} (hε : ε < 1) (g : GL (Fin 2) ℚ_[p])
    (hg : ∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
  have hdet : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 :=
    norm_det_eq_one_of_sub_entry_le p hε g hg
  have hentry : ∀ k l, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) k l‖ ≤ 1 :=
    norm_entry_le_one_of_sub_entry_le p (le_of_lt hε) hg
  have hcoe : ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv]
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hdet, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · simpa using hentry 1 1
  · simpa using hentry 0 1
  · simpa using hentry 1 0
  · simpa using hentry 0 0

theorem inv_sub_one_entry_le {ε : ℝ} (hε : ε < 1) (g : GL (Fin 2) ℚ_[p])
    (hg : ∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε) (i j : Fin 2) :
    ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε := by
  set A := (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hA
  set B := ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfact : B - 1 = B * (1 - A) := by
    rw [mul_sub, mul_one, hBA]
  have hBentry : ∀ k l, ‖B k l‖ ≤ 1 := fun k l =>
    norm_inv_entry_le_one_of_sub_entry_le p hε g hg k l
  have hsub : ∀ k l, ‖(1 - A) k l‖ ≤ ε := by
    intro k l
    have h : (1 - A) k l = -((A - 1) k l) := by
      rw [Matrix.sub_apply, Matrix.sub_apply]
      ring
    rw [h, norm_neg]
    exact hg k l
  rw [hfact, Matrix.mul_apply, Fin.sum_univ_two]
  refine padic_norm_add_le_of_le p ?_ ?_ <;>
    exact padic_norm_mul_le_of_le_one_of_le p (hBentry _ _) (hsub _ _)

end EntryBounds

section CongruenceSubgroup

variable (p : ℕ) [Fact p.Prime]

private theorem radius_pos (n : ℕ) : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  exact zpow_pos hp0 _

private theorem radius_le_one (n : ℕ) : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_one₀ (inv_nonneg.mpr (le_of_lt (lt_trans one_pos hp1))) (le_of_lt hpinv)

private theorem radius_antitone {m n : ℕ} (h : m ≤ n) :
    (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast le_of_lt (Fact.out : p.Prime).one_lt
  apply zpow_le_zpow_right₀ hp1
  omega

private theorem radius_lt_one {n : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ (-(n : ℤ)) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1
  refine lt_of_le_of_lt (radius_antitone p hn) ?_
  rw [Nat.cast_one, zpow_neg, zpow_one]
  exact hpinv

private theorem exists_radius_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, (p : ℝ) ^ (-(n : ℤ)) < ε := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hpinv
  refine ⟨n, ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hn

def gl2CongruenceSubgroup (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) where
  carrier := {g : GL (Fin 2) ℚ_[p] |
    (∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
    (∀ i j, ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖
      ≤ (p : ℝ) ^ (-(n : ℤ)))}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · simp only [inv_one, Units.val_one, sub_self, Matrix.zero_apply, norm_zero]
      exact le_of_lt (radius_pos p n)
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    refine ⟨hg.2, ?_⟩
    rw [inv_inv]
    exact hg.1
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    have hgentry : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hg1
    have hhinventry : ∀ i j,
        ‖((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hh2
    constructor
    · intro i j
      have hfact : ((g * h : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) * ((h : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hg1 i j)
      have := norm_matrix_mul_entry_le p hgentry hh1 i j
      rwa [one_mul] at this
    · intro i j
      have hfact : (((g * h)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = ((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
              * (((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + (((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [mul_inv_rev, Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hh2 i j)
      have := norm_matrix_mul_entry_le p hhinventry hg2 i j
      rwa [one_mul] at this

theorem mem_gl2CongruenceSubgroup_iff {n : ℕ} {g : GL (Fin 2) ℚ_[p]} :
    g ∈ gl2CongruenceSubgroup p n ↔
      (∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
      (∀ i j, ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖
        ≤ (p : ℝ) ^ (-(n : ℤ))) :=
  Iff.rfl

theorem mem_gl2CongruenceSubgroup_iff_of_one_le {n : ℕ} (hn : 1 ≤ n) {g : GL (Fin 2) ℚ_[p]} :
    g ∈ gl2CongruenceSubgroup p n ↔
      ∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [mem_gl2CongruenceSubgroup_iff]
  constructor
  · exact fun hg => hg.1
  · intro hg
    exact ⟨hg, inv_sub_one_entry_le p (radius_lt_one p hn) g hg⟩

theorem gl2CongruenceSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    gl2CongruenceSubgroup p n ≤ gl2CongruenceSubgroup p m := by
  intro g hg
  rw [mem_gl2CongruenceSubgroup_iff] at hg ⊢
  exact ⟨fun i j => le_trans (hg.1 i j) (radius_antitone p h),
    fun i j => le_trans (hg.2 i j) (radius_antitone p h)⟩

theorem norm_sub_one_entry_le_one_iff {M : Matrix (Fin 2) (Fin 2) ℚ_[p]} {i j : Fin 2} :
    ‖(M - 1) i j‖ ≤ 1 ↔ ‖M i j‖ ≤ 1 := by
  constructor
  · intro h
    have heq : M i j = (M - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
      rw [Matrix.sub_apply]
      ring
    rw [heq]
    exact padic_norm_add_le_of_le p h (norm_matrix_one_entry_le_one p i j)
  · intro h
    rw [Matrix.sub_apply, sub_eq_add_neg]
    refine padic_norm_add_le_of_le p h ?_
    rw [norm_neg]
    exact norm_matrix_one_entry_le_one p i j

theorem isOpen_coe_gl2CongruenceSubgroup (n : ℕ) :
    IsOpen ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  have hradius : ((p : ℝ) ^ (-(n : ℤ)) : ℝ) ≠ 0 := ne_of_gt (radius_pos p n)
  have hchar : ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
        Set (GL (Fin 2) ℚ_[p]))
      = (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
          (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
            ∈ Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
              ((p : ℝ) ^ (-(n : ℤ)))})
        ∩ (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
          ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
            ∈ Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
              ((p : ℝ) ^ (-(n : ℤ)))}) := by
    ext g
    simp only [SetLike.mem_coe, mem_gl2CongruenceSubgroup_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply]
  rw [hchar]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hradius).preimage
      (Units.continuous_val.matrix_elem i j)
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hradius).preimage
      (Units.continuous_coe_inv.matrix_elem i j)

theorem isClopen_coe_gl2CongruenceSubgroup (n : ℕ) :
    IsClopen ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) :=
  ⟨Subgroup.isClosed_of_isOpen _ (isOpen_coe_gl2CongruenceSubgroup p n),
    isOpen_coe_gl2CongruenceSubgroup p n⟩

private theorem conj_entry_bound {ε : ℝ} {k a : GL (Fin 2) ℚ_[p]}
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1)
    (ha : ∀ i j, ‖((a : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε) (i j : Fin 2) :
    ‖(((k * a * k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ ε := by
  have hkk : (k : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * ((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfact : ((k * a * k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
      = (k : Matrix (Fin 2) (Fin 2) ℚ_[p]) * ((a : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
          * ((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, mul_one, sub_mul, hkk]
  rw [hfact]
  have h1 : ∀ i' j', ‖((k : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * ((a : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)) i' j'‖ ≤ ε := by
    intro i' j'
    have := norm_matrix_mul_entry_le p hk ha i' j'
    rwa [one_mul] at this
  have h2 := norm_matrix_mul_entry_le p h1 hk' i j
  rwa [mul_one] at h2

theorem conj_mem_gl2CongruenceSubgroup {n : ℕ} {k g : GL (Fin 2) ℚ_[p]}
    (hk : k ∈ gl2CongruenceSubgroup p 0) (hg : g ∈ gl2CongruenceSubgroup p n) :
    k * g * k⁻¹ ∈ gl2CongruenceSubgroup p n := by
  rw [mem_gl2CongruenceSubgroup_iff] at hk hg ⊢
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hg1, hg2⟩ := hg
  have hradius0 : ((p : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  rw [hradius0] at hk1 hk2
  have hkentry : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := fun i j =>
    (norm_sub_one_entry_le_one_iff p).mp (hk1 i j)
  have hkinventry : ∀ i j,
      ‖((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := fun i j =>
    (norm_sub_one_entry_le_one_iff p).mp (hk2 i j)
  constructor
  · exact conj_entry_bound p hkentry hkinventry hg1
  · intro i j
    have hrw : ((k * g * k⁻¹ : GL (Fin 2) ℚ_[p]))⁻¹ = k * g⁻¹ * k⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    rw [hrw]
    exact conj_entry_bound p hkentry hkinventry hg2 i j

theorem normal_subgroupOf_gl2CongruenceSubgroup (n : ℕ) :
    ((gl2CongruenceSubgroup p n).subgroupOf (gl2CongruenceSubgroup p 0)).Normal := by
  constructor
  intro h hh k
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  have hcoe : ((k * h * k⁻¹ : gl2CongruenceSubgroup p 0) : GL (Fin 2) ℚ_[p])
      = (k : GL (Fin 2) ℚ_[p]) * (h : GL (Fin 2) ℚ_[p]) * ((k : GL (Fin 2) ℚ_[p]))⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  exact conj_mem_gl2CongruenceSubgroup p k.2 hh

noncomputable def gl2UnipotentPadic (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp]
theorem coe_gl2UnipotentPadic (x : ℚ_[p]) :
    ((gl2UnipotentPadic p x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![1, x; 0, 1] :=
  rfl

@[simp]
theorem coe_gl2UnipotentPadic_inv (x : ℚ_[p]) :
    (((gl2UnipotentPadic p x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![1, -x; 0, 1] :=
  rfl

theorem gl2UnipotentPadic_mem_gl2CongruenceSubgroup {x : ℚ_[p]} {n : ℕ}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    gl2UnipotentPadic p x ∈ gl2CongruenceSubgroup p n := by
  have hsub : ((gl2UnipotentPadic p x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
      = !![0, x; 0, 0] := by
    rw [coe_gl2UnipotentPadic]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]
  have hsubinv :
      (((gl2UnipotentPadic p x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
      = !![0, -x; 0, 0] := by
    rw [coe_gl2UnipotentPadic_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]
  rw [mem_gl2CongruenceSubgroup_iff]
  constructor
  · intro i j
    rw [hsub]
    fin_cases i <;> fin_cases j
    · simp
    · simpa using hx
    · simp
    · simp
  · intro i j
    rw [hsubinv]
    fin_cases i <;> fin_cases j
    · simp
    · simpa using hx
    · simp
    · simp

theorem gl2UnipotentPadic_ne_one {x : ℚ_[p]} (hx : x ≠ 0) : gl2UnipotentPadic p x ≠ 1 := by
  intro h
  have hcoe : ((gl2UnipotentPadic p x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1
      = ((1 : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 := by rw [h]
  rw [coe_gl2UnipotentPadic, Units.val_one] at hcoe
  apply hx
  calc x = (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 := by simp
    _ = (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1 := hcoe
    _ = 0 := by rw [Matrix.one_apply_ne (by decide)]

theorem gl2CongruenceSubgroup_ne_bot (n : ℕ) : gl2CongruenceSubgroup p n ≠ ⊥ := by
  intro hbot
  have hp0 : (p : ℚ_[p]) ≠ 0 :=
    (Nat.cast_ne_zero (R := ℚ_[p])).mpr (Fact.out : p.Prime).ne_zero
  have hxne : ((p : ℚ_[p]) ^ n) ≠ 0 := pow_ne_zero n hp0
  have hnormeq : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
    rw [norm_pow, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]
  have hmem := gl2UnipotentPadic_mem_gl2CongruenceSubgroup p (n := n) (le_of_eq hnormeq)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact gl2UnipotentPadic_ne_one p hxne hmem

theorem gl2CongruenceSubgroup_one_lt_zero :
    gl2CongruenceSubgroup p 1 < gl2CongruenceSubgroup p 0 := by
  rw [SetLike.lt_iff_le_and_exists]
  refine ⟨gl2CongruenceSubgroup_antitone p (Nat.zero_le 1), gl2UnipotentPadic p 1, ?_, ?_⟩
  · refine gl2UnipotentPadic_mem_gl2CongruenceSubgroup p ?_
    rw [norm_one]
    norm_num
  · intro hmem
    rw [mem_gl2CongruenceSubgroup_iff] at hmem
    have h1 := hmem.1 0 1
    rw [coe_gl2UnipotentPadic] at h1
    have heval : ((!![1, (1 : ℚ_[p]); 0, 1] : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 0 1 = 1 := by
      simp [Matrix.sub_apply]
    rw [heval, norm_one] at h1
    have hlt : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := radius_lt_one p le_rfl
    exact absurd h1 (not_le.mpr hlt)

end CongruenceSubgroup

section NeighbourhoodBasis

variable (p : ℕ) [Fact p.Prime]

theorem exists_entrywise_radius_subset_of_mem_nhds_one
    {W : Set (Matrix (Fin 2) (Fin 2) ℚ_[p])}
    (hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) ℚ_[p])) :
    ∃ n : ℕ, ∀ A : Matrix (Fin 2) (Fin 2) ℚ_[p],
      (∀ i j, ‖(A - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → A ∈ W := by
  have hof : Continuous fun f : Fin 2 → Fin 2 → ℚ_[p] =>
      (Matrix.of f : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
    continuous_matrixOf.mpr continuous_id
  have h1 : (fun f : Fin 2 → Fin 2 → ℚ_[p] => (Matrix.of f : Matrix (Fin 2) (Fin 2) ℚ_[p])) ⁻¹' W
      ∈ 𝓝 (fun i j => (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) := by
    refine (hof.continuousAt
      (x := fun i j => (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)).preimage_mem_nhds ?_
    exact hW
  rw [Metric.mem_nhds_iff] at h1
  obtain ⟨ε, hε0, hball⟩ := h1
  obtain ⟨n, hn⟩ := exists_radius_lt p hε0
  refine ⟨n, fun A hA => ?_⟩
  have hmem : (fun i j => A i j)
      ∈ Metric.ball (fun i j => (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε0]
    intro i
    rw [dist_pi_lt_iff hε0]
    intro j
    rw [dist_eq_norm]
    calc ‖A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ = ‖(A - 1) i j‖ := by
          rw [Matrix.sub_apply]
      _ ≤ (p : ℝ) ^ (-(n : ℤ)) := hA i j
      _ < ε := hn
  exact hball hmem

theorem exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one
    {U : Set (GL (Fin 2) ℚ_[p])} (hU : U ∈ 𝓝 (1 : GL (Fin 2) ℚ_[p])) :
    ∃ n : ℕ, (gl2CongruenceSubgroup p n : Set (GL (Fin 2) ℚ_[p])) ⊆ U := by
  have hnhds : 𝓝 (1 : GL (Fin 2) ℚ_[p])
      = Filter.comap (Units.embedProduct (Matrix (Fin 2) (Fin 2) ℚ_[p]))
          (𝓝 (Units.embedProduct (Matrix (Fin 2) (Fin 2) ℚ_[p]) 1)) :=
    Units.isInducing_embedProduct.nhds_eq_comap 1
  rw [hnhds, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWsub⟩ := hU
  rw [map_one] at hW
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℚ_[p] × (Matrix (Fin 2) (Fin 2) ℚ_[p])ᵐᵒᵖ)
      = ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]), (1 : (Matrix (Fin 2) (Fin 2) ℚ_[p])ᵐᵒᵖ)) from rfl,
    nhds_prod_eq, Filter.mem_prod_iff] at hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hprod⟩ := hW
  have hW₂' : (MulOpposite.op : Matrix (Fin 2) (Fin 2) ℚ_[p] →
      (Matrix (Fin 2) (Fin 2) ℚ_[p])ᵐᵒᵖ) ⁻¹' W₂ ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    have hcont : Continuous (MulOpposite.op : Matrix (Fin 2) (Fin 2) ℚ_[p] →
        (Matrix (Fin 2) (Fin 2) ℚ_[p])ᵐᵒᵖ) := MulOpposite.continuous_op
    refine (hcont.continuousAt (x := (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]))).preimage_mem_nhds ?_
    rw [MulOpposite.op_one]
    exact hW₂
  obtain ⟨n, hn⟩ := exists_entrywise_radius_subset_of_mem_nhds_one p
    (Filter.inter_mem hW₁ hW₂')
  refine ⟨n, fun g hg => ?_⟩
  rw [SetLike.mem_coe, mem_gl2CongruenceSubgroup_iff] at hg
  apply hWsub
  show Units.embedProduct (Matrix (Fin 2) (Fin 2) ℚ_[p]) g ∈ W
  apply hprod
  rw [Units.embedProduct_apply]
  exact Set.mk_mem_prod (hn _ hg.1).1 (hn _ hg.2).2

theorem hasBasis_nhds_one_gl2CongruenceSubgroup :
    (𝓝 (1 : GL (Fin 2) ℚ_[p])).HasBasis (fun _ : ℕ => True)
      (fun n => (gl2CongruenceSubgroup p n : Set (GL (Fin 2) ℚ_[p]))) := by
  constructor
  intro t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p ht
    exact ⟨n, trivial, hn⟩
  · rintro ⟨n, -, hsub⟩
    refine Filter.mem_of_superset ?_ hsub
    exact (isOpen_coe_gl2CongruenceSubgroup p n).mem_nhds (Subgroup.one_mem _)

instance nonarchimedeanGroup_gl2Padic : NonarchimedeanGroup (GL (Fin 2) ℚ_[p]) where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨n, hn⟩ := exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p hU
    exact ⟨⟨gl2CongruenceSubgroup p n, isOpen_coe_gl2CongruenceSubgroup p n⟩, hn⟩

end NeighbourhoodBasis

end FLT.SmoothVectors


