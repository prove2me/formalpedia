-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_depolarizingChannel
-- name    : WildeQIT_Compression_Supplement_depolarizingChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:00:01.122227+00:00
-- url     : https://prove2.me/theorems/acd7fa2d-64d6-508f-9086-d71754fa721d
-- title:
--   Qudit depolarizing channel $\mathcal N_D(\rho)=(1-p)\rho+p\pi$
-- statement:
--   Let $d\ge 1$ and $p\in[0,1]$. The **qudit depolarizing channel** on a $d$-dimensional system replaces its input by the maximally mixed state $\pi=I/d$ with probability $p$:
--
--   $$
--   \mathcal N_D(\rho)=(1-p)\rho+p\,\pi .
--   $$
--
--   It is given by the Kraus operators $\sqrt{1-p}\,I$ and $\sqrt{p/d}\,|i\rangle\langle j|$ for $i,j\in\{0,\dots,d-1\}$, which satisfy the completeness relation $\sum_k K_k^\dagger K_k=I$ and give $\mathcal N_D(X)=(1-p)X+\frac pd\operatorname{Tr}\{X\}I$ on every operator $X$.
--
--   The depolarizing channel is the "worst-case" noise model of §4.7.4; its classical capacity is computed in Theorem 20.4.3.
--
--   **Formalization Note** The system is indexed by `Fin d`; the channel is a published `WildeQIT.QChannel` (Kraus form) with Kraus labels `Option (Fin d × Fin d)`. The hypotheses $0\le p\le1$ are needed for the completeness relation.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §4.7.4, p. 175, eq. (4.344), and §20.4.4, p. 576, eq. (20.98)

import Mathlib
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.7.4, p. 175, (4.344),
and §20.4.4, p. 576, (20.98) (the qudit depolarizing channel).
-/

open Matrix

namespace WildeQIT.Compression.Supplement

/-- **Qudit depolarizing channel** `N_D(ρ) = (1 − p)ρ + pπ` (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §4.7.4, p. 175, (4.344), and §20.4.4, p. 576, (20.98)):
with probability `p` the `d`-dimensional input is replaced by the maximally mixed state
`π = I/d`; "the generalization of the depolarizing channel to qudits is … the same as the map in
(4.344), with the exception that the density operators `ρ` and `π` are qudit density operators".

**Formalization Note.** The input and output spaces are indexed by `Fin d`. The channel is given
in the published Kraus form `WildeQIT.QChannel` by the Kraus operators `√(1 − p) I` (label
`none`) and `√(p/d) |i⟩⟨j|` (label `some (i, j)`), so that
`N_D(ρ) = (1 − p)ρ + (p/d) Tr{ρ} I`, which is `(1 − p)ρ + pπ` on every density operator. The
hypotheses `0 ≤ p ≤ 1` are the book's "with some probability `p`" and are needed for the
completeness relation. -/
noncomputable def depolarizingChannel (d : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    QChannel (Fin d) (Fin d) where
  ι := Option (Fin d × Fin d)
  K k := match k with
    | none => ((Real.sqrt (1 - p) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
    | some ij => ((Real.sqrt (p / d) : ℝ) : ℂ) • Matrix.single ij.1 ij.2 (1 : ℂ)
  complete := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; exact Subsingleton.elim _ _
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hs1 : (starRingEnd ℂ) ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ)
        = ((1 - p : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    have hs2 : (starRingEnd ℂ) ((Real.sqrt (p / d) : ℝ) : ℂ) * ((Real.sqrt (p / d) : ℝ) : ℂ)
        = ((p / d : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (div_nonneg h0 (Nat.cast_nonneg d))]
    have hnone : (((Real.sqrt (1 - p) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ *
        (((Real.sqrt (1 - p) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
        ((1 - p : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [conjTranspose_smul, conjTranspose_one, smul_mul_smul_comm, mul_one]
      simpa using congrArg (· • (1 : Matrix (Fin d) (Fin d) ℂ)) hs1
    have hsome : ∀ ij : Fin d × Fin d,
        (((Real.sqrt (p / d) : ℝ) : ℂ) • Matrix.single ij.1 ij.2 (1 : ℂ))ᴴ *
          (((Real.sqrt (p / d) : ℝ) : ℂ) • Matrix.single ij.1 ij.2 (1 : ℂ)) =
        ((p / d : ℝ) : ℂ) • Matrix.single ij.2 ij.2 (1 : ℂ) := by
      intro ij
      rw [conjTranspose_smul, conjTranspose_single, smul_mul_smul_comm, star_one,
        single_mul_single_same, mul_one]
      simpa using congrArg (· • Matrix.single ij.2 ij.2 (1 : ℂ)) hs2
    have hsum : ∑ ij : Fin d × Fin d, Matrix.single ij.2 ij.2 (1 : ℂ) =
        (d : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Finset.smul_sum, Matrix.sum_single_one, Nat.cast_smul_eq_nsmul]
    rw [Fintype.sum_option]
    simp only []
    rw [hnone]
    simp_rw [hsome]
    rw [← Finset.smul_sum, hsum, smul_smul, ← add_smul]
    convert one_smul ℂ (1 : Matrix (Fin d) (Fin d) ℂ)
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring

end WildeQIT.Compression.Supplement


