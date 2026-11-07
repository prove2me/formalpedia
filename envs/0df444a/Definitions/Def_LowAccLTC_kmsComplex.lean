-- Prove2me | Definitions.Def_LowAccLTC_kmsComplex
-- name    : LowAccLTC_kmsComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:19.179172+00:00
-- url     : https://prove2.me/theorems/aee2398a-136f-4257-9dfb-6db57701d340
-- title:
--   The KMS coset complex $X(q,r,m)=\mathrm{CC}(\mathrm{SL}_r(\mathbb F_q[t]/(\phi));H_1,\dots,H_r)$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $r\ge 3$, $m\ge 1$, and $\phi\in\mathbb F_q[t]$ irreducible of degree $m$ with $\phi(0)\ne0$. Put $R=\mathbb F_q[t]/(\phi(t))$ and $\Gamma=\mathrm{SL}_r(R)$, identify $\mathbb F_q$ with the constants of $R$ and write $t$ for its image. For $i\in[r]\setminus\{1\}$,
--   $$H_i=\left\{\begin{pmatrix}T_1&0\\ tS&T_2\end{pmatrix}: T_1\in\Delta_{i-1}(\mathbb F_q),\ T_2\in\Delta_{r-i+1}(\mathbb F_q),\ S\in M_{r-i+1,i-1}(\mathbb F_q)\right\},$$
--   and $H_1=\Delta_r(\mathbb F_q)$, where $\Delta_a$ is the group of upper unitriangular $a\times a$ matrices. The **KMS complex** is the coset complex $X(q,r,m)=\mathrm{CC}(\Gamma;H_1,\dots,H_r)$: its vertices of colour $i$ are the left cosets $gH_i$, and $\{g_1H_{i_1},\dots,g_kH_{i_k}\}$ (distinct colours) is a face iff $\bigcap_a g_aH_{i_a}\ne\emptyset$; it carries the uniform distribution on its top faces. Since $\bigcap_iH_i=\{1\}$, the top faces are in bijection with $\Gamma$ via $g\mapsto\{gH_i\}_i$.
--
--   The KMS codes of the goal theorem live on these complexes.
--
--   **Formalization Note** Colour $i$ is `Fin r` index $i-1$. Each $H_i$ is described entrywise: diagonal $1$; above the diagonal inside the block of indices $<i$ or inside the block $\ge i$ a constant; in the lower-left block a multiple $t\,c$ of $t$ by a constant; otherwise $0$. A vertex is the pair $(i, gH_i)$ with the coset as a subset of $\Gamma$. The module proves $1\in H_i$ and $\bigcap_iH_i=\{1\}$. The finiteness instance on $R$ is a parameter; irreducibility, the degree and $\phi(0)\ne0$ are hypotheses of the theorems.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definitions 2.35–2.36 and Example 2.37, pp.22–23 (PDF pp.25–26)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

variable {F : Type*} [Field F] (r : ℕ) (ϕ : Polynomial F)

/-- `Γ = SL_r(R)` with `R = F[t]/(ϕ(t))` (Definition 2.36, p.22). -/
abbrev KMSGamma := Matrix.SpecialLinearGroup (Fin r) (AdjoinRoot ϕ)

/-- The entry condition defining the KMS subgroup of colour `i` (0-based; the paper's colour
`i + 1`) at the position `(a, b)` (0-based row and column), for Definition 2.36 (p.22) and
Example 2.37 (pp.22–23): the diagonal entries are `1`; above the diagonal, inside the block of
indices `< i` or inside the block of indices `≥ i`, the entry is a constant of `F`; in the
lower-left block (`a ≥ i > b`) the entry lies in `t·F`; all other entries are `0`. For `i = 0`
the first block is empty and the condition describes `Δ_r(F)`, the upper unitriangular matrices
(the paper's `H₁`). -/
def kmsEntryOK (i a b : Fin r) (x : AdjoinRoot ϕ) : Prop :=
  if a = b then x = 1
  else if a < b ∧ (b < i ∨ i ≤ a) then ∃ c : F, x = AdjoinRoot.of ϕ c
  else if i ≤ a ∧ b < i then ∃ c : F, x = AdjoinRoot.root ϕ * AdjoinRoot.of ϕ c
  else x = 0

/-- The subgroup `H_{i+1} = {(T₁ 0; tS T₂) : T₁ ∈ Δ_i(F), T₂ ∈ Δ_{r-i}(F), S ∈ M_{r-i,i}(F)}` of
`Γ` (Definition 2.36, p.22; colour `i : Fin r` is the paper's colour `i + 1`, and `F` is
identified with the constants of `R`, `t` with `AdjoinRoot.root ϕ`). -/
def kmsH (i : Fin r) : Set (KMSGamma r ϕ) :=
  {g | ∀ a b, kmsEntryOK r ϕ i a b ((g : Matrix (Fin r) (Fin r) (AdjoinRoot ϕ)) a b)}

lemma one_mem_kmsH (i : Fin r) : (1 : KMSGamma r ϕ) ∈ kmsH r ϕ i := by
  intro a b
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, kmsEntryOK]
  split_ifs <;> first | rfl | exact ⟨0, by simp⟩

lemma eq_one_of_mem_all_kmsH (g : KMSGamma r ϕ) (hg : ∀ i, g ∈ kmsH r ϕ i) : g = 1 := by
  ext a b
  have h := hg b a b
  simp only [kmsEntryOK, lt_irrefl, false_or, and_false, if_false] at h
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simpa using h
  · rw [if_neg hab]; rw [if_neg hab] at h
    have h2 : ¬ (a < b ∧ b ≤ a) := fun h' => absurd h'.2 (not_le.mpr h'.1)
    rw [if_neg h2] at h
    exact h

variable [Fintype (AdjoinRoot ϕ)] [DecidableEq (AdjoinRoot ϕ)]

/-- The KMS complex `X(q, r, m) = CC(Γ; H₁, …, H_r)` (Definitions 2.35 and 2.36, p.22), with
`q = |F|` and `m = deg ϕ`: the coset complex whose vertices of colour `i` are the left cosets
`gH_i`, with the uniform distribution on its top faces. Since `⋂ H_i = {1}`, the top faces are
in bijection with `Γ` via `g ↦ {gH_i}_i` (p.22), so the top-face type is `Γ`.

**Formalization Note.** A vertex is encoded as the pair `(i, gH_i)` of its colour and the coset
`gH_i` as a subset of `Γ`. The irreducibility of `ϕ`, its degree `m` and `ϕ(0) ≠ 0` are
hypotheses of the theorems that use the complex. The `Fintype` instance on `R` is a parameter
(it exists whenever `ϕ ≠ 0`; all such instances are equal). -/
noncomputable def kmsComplex : PartiteComplex r (Fin r × Set (KMSGamma r ϕ)) (KMSGamma r ϕ) where
  col := Prod.fst
  vert g i := (i, (fun h => g * h) '' kmsH r ϕ i)
  col_vert _ _ := rfl
  vert_inj := by
    intro g g' hgg
    have key : ∀ i, g⁻¹ * g' ∈ kmsH r ϕ i := by
      intro i
      have h1 := congrArg (fun F => (F i).2) hgg
      simp only at h1
      have hm : g' ∈ (fun h => g' * h) '' kmsH r ϕ i := ⟨1, one_mem_kmsH r ϕ i, mul_one _⟩
      rw [← h1] at hm
      obtain ⟨h, hh, hgh⟩ := hm
      simp only at hgh
      rw [← hgh, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hh
    have := eq_one_of_mem_all_kmsH r ϕ _ key
    exact (inv_mul_eq_one.mp this)
  μ _ := 1 / (Fintype.card (KMSGamma r ϕ) : ℝ)
  μ_pos _ := by positivity
  μ_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card (KMSGamma r ϕ) := by exact_mod_cast Fintype.card_pos
    field_simp

end LowAccLTC


