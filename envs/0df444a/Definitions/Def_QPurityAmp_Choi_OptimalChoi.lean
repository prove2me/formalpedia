-- Prove2me | Definitions.Def_QPurityAmp_Choi_OptimalChoi
-- name    : QPurityAmp_Choi_OptimalChoi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:33.272682+00:00
-- url     : https://prove2.me/theorems/2a9f746b-a21f-4c1d-b2fb-e5263d2b082b
-- title:
--   Thm. II.1, Prop. S2.1, Eqs. (S26)–(S27), pp. 3–4, 18–21 — feasible rows, shifted diagrams ν_i, isotypic projectors of Ū ⊗ U^{⊗n}, the Choi matrix T*, normalized Schur polynomials, dominance
-- statement:
--   This module builds the Choi matrix $T^*$ of Theorem II.1 and the representation-theoretic objects its proof uses.
--
--   A **Young diagram** $\varsigma$ with $n$ boxes and at most $d$ rows labels an outcome of Schur sampling; its row lengths $\varsigma_1\ge\dots\ge\varsigma_d\ge 0$ are padded with zeros to $d$ rows. Rows are numbered $0,\dots,d-1$ in Lean (the paper's row $i$ is Lean row $i-1$).
--
--   1. **Feasible rows** (p. 3). Row $i$ is feasible if it is the last row, or $\varsigma_i>\varsigma_{i+1}$. These are exactly the rows from which one box can be removed, $[\mu_i]=\varsigma-e_i$, in the decomposition $\overline W\otimes W^{[\varsigma]}=\bigoplus_{\text{feasible } i}W^{[\mu_i]}$ of the mixed representation (the last row may become $-1$).
--   2. **Shifted diagrams.** For feasible $i$, $\nu_i=\varsigma+(1^d)-e_i$, with row lengths $\varsigma_r+1-[r=i]$ for $r<d$: a Young diagram with at most $d$ rows and $n+d-1$ boxes. The irrep $[\mu_i]$ of $U(d)$ is $[\nu_i]\otimes\det^{-1}$.
--   3. **The smallest feasible row** $i^*$ of $\varsigma$: the row of the bottom box of the last column.
--   4. **Characters and isotypic projectors.** $\chi_\nu(A)$ is the trace of the polynomial representation of $A$ on the Schur (Weyl) module of $\nu$. For the mixed representation $R(U)=\bar U\otimes U^{\otimes n}$,
--   $$P_{\mu}=d^{[\nu]}\int \overline{\chi_\nu(U)}\,\det U\;R(U)\,dU,$$
--   the projector onto the $[\mu]$-isotypic component, $\mu=\nu-(1^d)$, where $d^{[\nu]}$ is the dimension of the irrep (the number of semistandard tableaux of shape $\nu$ with entries in $\{1,\dots,d\}$).
--   5. **Blocks.** $Q_{\varsigma,i}=P_{\mu_i}(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma)$, where $\Pi_\varsigma$ is the weak Schur sampling projector onto the $\varsigma$-isotypic part of $W^{\otimes n}$. In the mixed Schur basis this is $\Pi^{[\mu_i]}\otimes\mathbb I_{g^{[\varsigma]}}$ inside the $\varsigma$-sector.
--   6. **The optimal Choi matrix** (Theorem II.1):
--   $$T^*=\sum_{\varsigma}\frac{d^{[\varsigma]}}{d^{[\mu_{i^*}]}}\;P_{\mu_{i^*}}\big(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma\big)=U_{\mathrm{mSch}}^\dagger\Big(\bigoplus_{[\varsigma]}\frac{d^{[\varsigma]}}{d^{[\mu_{i^*}]}}\Pi^{[\mu_{i^*}]}\otimes\mathbb I_{g^{[\varsigma]}}\Big)U_{\mathrm{mSch}} .$$
--   7. **Normalized Schur polynomials** $S^{[\nu]}(x)=s^{[\nu]}(x)/d^{[\nu]}$ (p. 20) and the **dominance order** of Eq. (S27): $[\mu]\preceq[\lambda]$ iff $\sum_{a\le k}\mu_a\le\sum_{a\le k}\lambda_a$ for every $k$.
--
--   $T^*$ depends only on $d$ and $n$, not on the noise strength $\lambda$.
--
--   **Formalization Note** The irreps $[\mu_i]$ of the mixed representation are rational: when $\varsigma_d=0$ the last row of $\mu_d$ is $-1$ (the paper calls these "valid YD"). They are named here through the determinant shift $\nu_i$, a polynomial irrep, and the twist $\det^{-1}$ appears in the character as $\overline{\chi_{\mu}(U)}=\overline{\chi_{\nu}(U)}\det U$. The number of boxes of $\nu_i$ is carried in its type as the cardinality of the constructed diagram (it equals $n+d-1$). $i^*$ is the minimum of the nonempty set of feasible rows (the last row is always feasible), so it needs $d\ge 1$. Characters and dimensions come from the published Schur layer (`schurModule`, `polynomialRepresentation`, `schurPolynomial`, `schurDimension`, `isotypicProjector`).
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 3, Eq. (3) and the definition of feasible rows; p. 4, Theorem II.1 and Eq. (4); pp. 16–17, mixed Schur–Weyl duality; p. 18, Proposition S2.1; p. 20, Eq. (S26); p. 21, Eq. (S27)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_Model
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix Kronecker

open QAlgorithms.Schur

/-! Li, Fu, Isogawa, Silva and Chuang, *Optimal Quantum Purity Amplification*,
arXiv:2409.18167v4, pp. 3–4 (feasible rows, Theorem II.1), pp. 16–17 (mixed Schur–Weyl
duality), pp. 18–21 (Proposition S2.1, Eqs. (S26)–(S28)).

Young diagrams `vs : Partition d n` (n boxes, at most d rows) label the Schur-sampling outcomes
[ς]. Rows are 0-based: the paper's row i is `i.val + 1`. The irreps [µ_i] = ς − e_i of the mixed
representation Ū ⊗ U^{⊗n} may have a last row of length −1; they are named through the
determinant shift ν_i = ς + (1^d) − e_i, a genuine Young diagram with at most d rows, with
[µ_i] ≅ [ν_i] ⊗ det⁻¹. -/

/-- Row `i` (0-based) of ς is *feasible* (p. 3: removing the last box of the i-th row of the
d-row diagram, padded with zeros, gives a valid configuration of the mixed representation):
either `i` is the last row `d − 1`, or row `i` is strictly longer than row `i + 1`. -/
def IsFeasibleRow {d n : ℕ} (vs : Partition d n) (i : Fin d) : Prop :=
  i.val + 1 = d ∨ vs.val.rowLen (i.val + 1) < vs.val.rowLen i.val

instance {d n : ℕ} (vs : Partition d n) : DecidablePred (IsFeasibleRow vs) := fun i => by
  unfold IsFeasibleRow; infer_instance

/-- Row lengths of the shifted diagram ν_i: ς_r + 1 − [r = i] for the rows r < d, 0 below. -/
def shiftedLen {d n : ℕ} (vs : Partition d n) (i : Fin d) (r : ℕ) : ℕ :=
  if r < d then vs.val.rowLen r + 1 - (if r = i.val then 1 else 0) else 0

/-- The Young diagram ν_i = ς + (1^d) − e_i, for a feasible row i. -/
def shiftedYD {d n : ℕ} (vs : Partition d n) (i : {i : Fin d // IsFeasibleRow vs i}) :
    YoungDiagram where
  cells := ((Finset.range d) ×ˢ (Finset.range (vs.val.rowLen 0 + 1))).filter
    fun rc => rc.2 < shiftedLen vs i.val rc.1
  isLowerSet := by
    intro a b hb ha
    obtain ⟨r, c⟩ := a
    obtain ⟨r', c'⟩ := b
    have hr' : r' ≤ r := hb.1
    have hc' : c' ≤ c := hb.2
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq]
      at ha ⊢
    obtain ⟨⟨hrd, hc0⟩, hcl⟩ := ha
    have hanti : vs.val.rowLen r ≤ vs.val.rowLen r' := vs.val.rowLen_anti r' r hr'
    have hanti0 : vs.val.rowLen r' ≤ vs.val.rowLen 0 := vs.val.rowLen_anti 0 r' (Nat.zero_le _)
    have hfeas := i.property
    unfold IsFeasibleRow at hfeas
    have hstep : r' < r → vs.val.rowLen r ≤ vs.val.rowLen (r' + 1) :=
      fun h => vs.val.rowLen_anti (r' + 1) r h
    unfold shiftedLen at hcl ⊢
    rw [if_pos hrd] at hcl
    rw [if_pos (lt_of_le_of_lt hr' hrd)]
    refine ⟨⟨lt_of_le_of_lt hr' hrd, by omega⟩, ?_⟩
    by_cases h1 : r' = (i.val : ℕ)
    · by_cases h2 : r = (i.val : ℕ)
      · rw [if_pos h2] at hcl; rw [if_pos h1]; omega
      · rw [if_pos h1]; rw [if_neg h2] at hcl
        have hlt : r' < r := lt_of_le_of_ne hr' (fun h => h2 (h ▸ h1))
        have := hstep hlt
        rcases hfeas with hf | hf
        · omega
        · rw [← h1] at hf; omega
    · rw [if_neg h1]
      split_ifs at hcl <;> omega

/-- ν_i as an element of `Partition d m`, m = its number of boxes (= n + d − 1). -/
def shifted {d n : ℕ} (vs : Partition d n) (i : {i : Fin d // IsFeasibleRow vs i}) :
    Partition d (shiftedYD vs i).card :=
  ⟨shiftedYD vs i, rfl, by
    by_contra h
    push Not at h
    have hmem : (d, 0) ∈ shiftedYD vs i := YoungDiagram.mem_iff_lt_colLen.mpr h
    change (d, 0) ∈ (shiftedYD vs i).cells at hmem
    simp [shiftedYD] at hmem⟩

/-- The smallest feasible row index i* of ς (Theorem II.1). The last row `d − 1` is always
feasible, so the set of feasible rows is nonempty. -/
def istar {d n : ℕ} [NeZero d] (vs : Partition d n) : {i : Fin d // IsFeasibleRow vs i} :=
  let S := Finset.univ.filter (IsFeasibleRow vs)
  have hS : S.Nonempty :=
    ⟨⟨d - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne d)) Nat.one_pos⟩, by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, IsFeasibleRow]
      left
      have := Nat.pos_of_ne_zero (NeZero.ne d)
      change d - 1 + 1 = d
      omega⟩
  ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2⟩

/-- The character χ_ν(A) = tr(ν(A)) of the polynomial representation of GL(d) labelled by ν,
as the trace of the published `polynomialRepresentation` on the Weyl (Schur) module. -/
def character {d m : ℕ} (nu : Partition d m) (A : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  LinearMap.trace ℂ (schurModule nu) (polynomialRepresentation nu A)

/-- The projector onto the isotypic component of the irrep [µ] = [ν] ⊗ det⁻¹ inside the mixed
representation R(U) = Ū ⊗ U^{⊗n} of U(d) on out ⊗ in:
P_µ = d^[µ] ∫ conj(χ_µ(U)) R(U) dU, with χ_µ(U) = χ_ν(U) det(U)⁻¹ and d^[µ] = d^[ν]. -/
def mixedProj {d m : ℕ} (n : ℕ) (nu : Partition d m) :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  ((schurDimension nu : ℝ) : ℂ) •
    haarInt fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      (star (character nu (U : Matrix (Fin d) (Fin d) ℂ)) *
          (U : Matrix (Fin d) (Fin d) ℂ).det) •
        mixedRep n (U : Matrix (Fin d) (Fin d) ℂ)

/-- The block Π^[µ_i] ⊗ I_{g[ς]} of the ς-sector: the projector onto the [µ_i]-component of
out ⊗ (ς-isotypic part of the input registers), i.e. P_{µ_i} (I_out ⊗ Π_ς). -/
def blockProj {d n : ℕ} (vs : Partition d n) (i : {i : Fin d // IsFeasibleRow vs i}) :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  mixedProj n (shifted vs i) * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ isotypicProjector vs)

/-- The Choi matrix of Theorem II.1, p. 4:
T* = U†_mSch (⨁_ς (d^[ς]/d^[µ_{i*}]) Π^[µ_{i*}] ⊗ I_{g[ς]}) U_mSch
   = Σ_ς (d^[ς]/d^[µ_{i*}]) P_{µ_{i*}} (I_out ⊗ Π_ς). -/
def optimalChoi (d n : ℕ) [NeZero d] :
    Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ :=
  ∑ vs : Partition d n,
    ((schurDimension vs / schurDimension (shifted vs (istar vs)) : ℝ) : ℂ) •
      blockProj vs (istar vs)

/-- The normalized Schur polynomial S^[ν](x) = s^[ν](x)/d^[ν] (p. 20). -/
def normSchur {d m : ℕ} (nu : Partition d m) (x : Fin d → ℝ) : ℝ :=
  MvPolynomial.eval x (schurPolynomial nu) / schurDimension nu

/-- The dominance order of Eq. (S27), p. 21: [µ] ⪯ [λ] iff every partial row sum of µ is at
most the corresponding partial row sum of λ. -/
def DomLE (mu la : YoungDiagram) : Prop :=
  ∀ k : ℕ, ∑ a ∈ Finset.range k, mu.rowLen a ≤ ∑ a ∈ Finset.range k, la.rowLen a

end QPurityAmp.Choi


