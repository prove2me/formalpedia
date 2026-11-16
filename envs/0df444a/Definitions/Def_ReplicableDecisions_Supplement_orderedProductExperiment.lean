-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_orderedProductExperiment
-- name    : ReplicableDecisions_Supplement_orderedProductExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:00:59.126176+00:00
-- url     : https://prove2.me/theorems/5d18f6ff-ab57-459e-b922-2debdd69f9d9
-- title:
--   Ordered product experiment $P_j=\bigotimes_{i\le j}Q_i^+\otimes\bigotimes_{i>j}Q_i^-$, early/late acceptable sets (4.1), and $\lambda_i=-\log\mathrm{BC}(Q_i^-,Q_i^+)$
-- statement:
--   For $i\in\{1,\dots,d\}$ let $Q_i^-$ and $Q_i^+$ be distinct strictly positive laws on a finite alphabet $\mathcal Z_i$. The **ordered product family** consists of the $d+1$ product laws on $\mathcal Z_1\times\dots\times\mathcal Z_d$
--   $$P_j=\bigotimes_{i\le j}Q_i^+\otimes\bigotimes_{i>j}Q_i^-,\qquad j=0,\dots,d;$$
--   one sample contains one observation of every coordinate block. These laws are distinct probability vectors.
--
--   The **early/late acceptable sets** of (4.1) are
--   $$\Gamma(P_j)=\begin{cases}\{0\},& j\le\lfloor d/4\rfloor,\\ \{1\},& j\ge\lceil 3d/4\rceil,\\ \{0,1\},&\text{otherwise,}\end{cases}$$
--   and the **block exponents** are $\lambda_i=-\log\mathrm{BC}(Q_i^-,Q_i^+)$, where $\mathrm{BC}(P,Q)=\sum_z\sqrt{P(z)Q(z)}$.
--
--   This is the structural class of Theorem 4.5; the change-point experiment (4.1) is its binary instance.
--
--   **Formalization Note** Blocks are indexed by $i\in\{0,\dots,d-1\}$ (0-based), so "$i\le j$" reads $i<j$. The proof of distinctness uses $Q_i^-\ne Q_i^+$ and the positivity of $Q_i^-$. $\mathrm{BC}$ is the published `FuchsVdGraaf.bhattacharyya`.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), §4.2, p.21 (PDF p.23); (4.1), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment
import Definitions.Def_FuchsVdGraaf_bhattacharyya

namespace ReplicableDecisions.Supplement

/-- **The ordered product law** `P_j = ⊗_{i≤j} Q⁺_i ⊗ ⊗_{i>j} Q⁻_i`, `j = 0, …, d`. Chen,
*Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), §4.2, p.21
(PDF p.23); (4.1), p.16 (PDF p.18), for the binary case.

**Formalization Note.** Coordinate blocks are `i : Fin d` (0-based), so the paper's block `i + 1`
is `i`, and "`i ≤ j`" becomes `(i : ℕ) < j`. One sample is one observation of every block:
`x : (i : Fin d) → Zs i`. -/
noncomputable def orderedLaw {d : ℕ} {Zs : Fin d → Type} (Qm Qp : (i : Fin d) → Zs i → ℝ)
    (j : Fin (d + 1)) (x : (i : Fin d) → Zs i) : ℝ :=
  ∏ i : Fin d, if (i : ℕ) < (j : ℕ) then Qp i (x i) else Qm i (x i)

theorem orderedLaw_mem_simplex {d : ℕ} {Zs : Fin d → Type} [∀ i, Fintype (Zs i)]
    {Qm Qp : (i : Fin d) → Zs i → ℝ} (hm : ∀ i, Qm i ∈ stdSimplex ℝ (Zs i))
    (hp : ∀ i, Qp i ∈ stdSimplex ℝ (Zs i)) (j : Fin (d + 1)) :
    orderedLaw Qm Qp j ∈ stdSimplex ℝ ((i : Fin d) → Zs i) := by
  refine ⟨fun x => Finset.prod_nonneg fun i _ => ?_, ?_⟩
  · split_ifs
    · exact (hp i).1 _
    · exact (hm i).1 _
  · have h := Fintype.prod_sum (fun (i : Fin d) (z : Zs i) => if (i : ℕ) < (j : ℕ) then Qp i z else Qm i z)
    unfold orderedLaw
    rw [← h]
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs
    · exact (hp i).2
    · exact (hm i).2

theorem exists_lt_of_ne_simplex {α : Type*} [Fintype α] {p q : α → ℝ} (hp : p ∈ stdSimplex ℝ α)
    (hq : q ∈ stdSimplex ℝ α) (hne : p ≠ q) : ∃ z, p z < q z := by
  by_contra h
  push Not at h
  apply hne
  have hs : ∑ z, q z = ∑ z, p z := by rw [hp.2, hq.2]
  have := (Finset.sum_eq_sum_iff_of_le (fun z _ => h z)).mp hs
  funext z
  exact (this z (Finset.mem_univ z)).symm

theorem orderedLaw_injective {d : ℕ} {Zs : Fin d → Type} [∀ i, Fintype (Zs i)]
    {Qm Qp : (i : Fin d) → Zs i → ℝ} (hm : ∀ i, Qm i ∈ stdSimplex ℝ (Zs i))
    (hp : ∀ i, Qp i ∈ stdSimplex ℝ (Zs i)) (hpos : ∀ i z, 0 < Qm i z)
    (hne : ∀ i, Qm i ≠ Qp i) : Function.Injective (orderedLaw Qm Qp) := by
  have hz : ∀ i, ∃ z, Qm i z < Qp i z := fun i => exists_lt_of_ne_simplex (hm i) (hp i) (hne i)
  choose z hz using hz
  have key : ∀ j k : Fin (d + 1), j < k → orderedLaw Qm Qp j z < orderedLaw Qm Qp k z := by
    intro j k hjk
    have hjk' : (j : ℕ) < k := hjk
    have hk : (k : ℕ) ≤ d := Nat.lt_succ_iff.mp k.2
    unfold orderedLaw
    apply Finset.prod_lt_prod
    · intro i _
      split_ifs
      · exact lt_trans (hpos i (z i)) (hz i)
      · exact hpos i (z i)
    · intro i _
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (lt_trans h1 hjk') h2
      · exact (hz i).le
      · exact le_rfl
    · refine ⟨⟨j, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [lt_irrefl, if_false, hjk', if_true]
      exact hz _
  intro j k h
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact absurd (congrFun h z) (key j k hlt).ne
  · exact heq
  · exact absurd (congrFun h z) (key k j hgt).ne'

/-- **The ordered product experiment** `{P_0, …, P_d}` of §4.2. Chen, STOC 2027 submission
(sha256 52d181db…), §4.2, p.21 (PDF p.23): "For i ∈ {1, . . . , d}, let Q⁻_i and Q⁺_i be distinct
strictly positive laws on a finite alphabet Z_i. Define the ordered product family …".

**Formalization Note.** The models are indexed by `j : Fin (d + 1)`; distinctness is proved from
`Q⁻_i ≠ Q⁺_i` and the strict positivity of `Q⁻_i` (the theorems also assume `Q⁺_i > 0`, as the
page does). Heterogeneous alphabets `Zs i : Type` are allowed. -/
noncomputable def orderedProductExperiment {d : ℕ} {Zs : Fin d → Type} [∀ i, Fintype (Zs i)]
    (Qm Qp : (i : Fin d) → Zs i → ℝ) (hm : ∀ i, Qm i ∈ stdSimplex ℝ (Zs i))
    (hp : ∀ i, Qp i ∈ stdSimplex ℝ (Zs i)) (hpos : ∀ i z, 0 < Qm i z)
    (hne : ∀ i, Qm i ≠ Qp i) : Experiment (Fin (d + 1)) ((i : Fin d) → Zs i) where
  P := orderedLaw Qm Qp
  mem_simplex := orderedLaw_mem_simplex hm hp
  distinct := orderedLaw_injective hm hp hpos hne

/-- **The early/late acceptable sets** of (4.1): `Γ(P_j) = {0}` if `j ≤ ⌊d/4⌋`, `{1}` if
`j ≥ ⌈3d/4⌉`, `{0, 1}` otherwise. Chen, STOC 2027 submission (sha256 52d181db…), (4.1), p.16
(PDF p.18), also used in §4.2 ("with the early/late acceptable sets of (4.1)", p.21).

**Formalization Note.** `0 = false`, `1 = true`; `⌊d/4⌋` and `⌈3d/4⌉` are of the real numbers
`d/4` and `3d/4`. For `d ≥ 1` the two forced ranges are disjoint. -/
noncomputable def earlyLateΓ (d : ℕ) (j : Fin (d + 1)) : Set Bool :=
  if ((j : ℕ) : ℤ) ≤ ⌊(d : ℝ) / 4⌋ then {false}
  else if ⌈3 * (d : ℝ) / 4⌉ ≤ ((j : ℕ) : ℤ) then {true} else Set.univ

/-- **The block exponents** `λ_i = −log BC(Q⁻_i, Q⁺_i)`. Chen, STOC 2027 submission
(sha256 52d181db…), §4.2, p.21 (PDF p.23).

**Formalization Note.** `BC` is the published `FuchsVdGraaf.bhattacharyya`, as in the published
`hellingerSq`. -/
noncomputable def blockExponent {d : ℕ} {Zs : Fin d → Type} [∀ i, Fintype (Zs i)]
    (Qm Qp : (i : Fin d) → Zs i → ℝ) (i : Fin d) : ℝ :=
  -Real.log (FuchsVdGraaf.bhattacharyya (Qm i) (Qp i))

end ReplicableDecisions.Supplement


