-- Prove2me | Definitions.Def_AlgebraicPCSP_BLP_Qconv
-- name    : AlgebraicPCSP_BLP_Qconv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:08.724454+00:00
-- url     : https://prove2.me/theorems/7d0add00-42d7-4c30-bc2d-fd76ee2edb76
-- title:
--   The structure Q_conv, its finite reducts, and the minion 𝒬_conv of convex linear functions (§7.2, p. 46)
-- statement:
--   The structure $\mathbf Q_{\mathrm{conv}}$ has domain $\mathbb Q$, and its (infinitely many) relations are all linear inequalities with rational coefficients: for every $k\ge 1$, $c\in\mathbb Q^k$ and $d\in\mathbb Q$, the relation
--   $$\Big\{x\in\mathbb Q^k \;\Big|\; \sum_{i=1}^k c_ix_i\le d\Big\}.$$
--   A *finite reduct* $\mathbf D$ of $\mathbf Q_{\mathrm{conv}}$ is obtained by dropping all but finitely many of these relations.
--
--   The minion $\mathcal Q_{\mathrm{conv}}$ on $(\mathbb Q,\mathbb Q)$ consists of all *convex linear functions*, i.e. the functions $f:\mathbb Q^n\to\mathbb Q$, $n\ge 1$, of the form
--   $$f(x_1,\dots,x_n)=\sum_{i\in[n]}\alpha_ix_i,\qquad \alpha_i\in[0,1],\quad \sum_{i\in[n]}\alpha_i=1.$$
--   The paper notes that these are exactly the polymorphisms of $\mathbf Q_{\mathrm{conv}}$; here $\mathcal Q_{\mathrm{conv}}$ is defined directly by the formula.
--
--   $\mathcal Q_{\mathrm{conv}}$ is the minion that governs the basic LP relaxation: Theorem 7.9 says that BLP solves $\mathrm{PCSP}(\mathbf A,\mathbf B)$ exactly when $\mathcal Q_{\mathrm{conv}}$ maps to $\mathrm{Pol}(\mathbf A,\mathbf B)$.
--
--   **Formalization Note** The relations of $\mathbf Q_{\mathrm{conv}}$ are the non-strict inequalities $\sum c_ix_i\le d$ indexed by `LinIneq` (arity $k\ge 1$, coefficients $c$, bound $d$); equalities are pp-definable from two of them. The paper's remark that the relations pp-definable in $\mathbf Q_{\mathrm{conv}}$ are the convex polytopes points to this non-strict reading. A finite reduct is `QconvReduct S` for a finite set `S` of inequalities, with signature the subtype of `S`. The minion `convexMinion` proves its minion axioms inside the definition (the minor of a convex combination is a convex combination with coefficients summed along the fibres of $\pi$).
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 46, §7.2 (Q_conv, finite reduct, the set 𝒬_conv of convex linear functions)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- A linear inequality with rational coefficients in `k ≥ 1` variables,
`c₁x₁ + ⋯ + c_kx_k ≤ d` (p. 46, following [BM17, Definition 4]). These are the relation
symbols of `Q_conv`. -/
structure LinIneq where
  /-- The number of variables (the arity of the relation). -/
  k : ℕ
  k_pos : 0 < k
  /-- The coefficients `c₁, …, c_k`. -/
  c : Fin k → ℚ
  /-- The right-hand side `d`. -/
  d : ℚ

/-- The structure `Q_conv` (p. 46): domain `ℚ`, and one relation for every linear inequality
with rational coefficients, `{x ∈ ℚᵏ | ∑ᵢ cᵢxᵢ ≤ d}`. It has infinitely many relations. -/
def Qconv : RelStruct LinIneq LinIneq.k ℚ where
  rel ι := {x | ∑ i, ι.c i * x i ≤ ι.d}

/-- The finite reduct of `Q_conv` keeping only the relations named in the finite set `S` of
linear inequalities (p. 46: "by simply dropping all but finitely many relations"). Its
signature is the subtype of `S`, so it is finite. -/
def QconvReduct (S : Finset LinIneq) : RelStruct S (fun ι => ι.val.k) ℚ where
  rel ι := Qconv.rel ι.val

/-- The minion `𝒬_conv` on `(ℚ, ℚ)` of all convex linear functions (p. 46): the `n`-ary
functions `f(x₁, …, xₙ) = ∑_{i ∈ [n]} αᵢxᵢ` with `αᵢ ∈ [0, 1]` and `∑ᵢ αᵢ = 1`. There are no
nullary members (the coefficients of a nullary function cannot sum to `1`). -/
def convexMinion : AlgebraicPCSP.Theory.Minion ℚ ℚ where
  mem n := {f | ∃ α : Fin n → ℚ, (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ ∑ i, α i = 1 ∧
    f = fun x => ∑ i, α i * x i}
  mem_zero := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨α, -, hα, -⟩
    simp at hα
  nonempty := ⟨1, fun x => x 0, fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩, by simp,
    by funext x; simp⟩
  minor_mem := by
    classical
    rintro m n π g ⟨α, hα01, hαsum, rfl⟩
    refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => π i = j), α i, ?_, ?_, ?_⟩
    · intro j
      refine ⟨Finset.sum_nonneg (fun i _ => (hα01 i).1), ?_⟩
      calc ∑ i ∈ Finset.univ.filter (fun i => π i = j), α i ≤ ∑ i, α i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => (hα01 i).1)
        _ = 1 := hαsum
    · rw [← hαsum, ← Finset.sum_fiberwise Finset.univ π α]
    · funext x
      simp only [Function.comp]
      rw [← Finset.sum_fiberwise Finset.univ π (fun i => α i * x (π i))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [(Finset.mem_filter.mp hi).2]

end AlgebraicPCSP.BLP


