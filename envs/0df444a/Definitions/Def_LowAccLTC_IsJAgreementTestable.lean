-- Prove2me | Definitions.Def_LowAccLTC_IsJAgreementTestable
-- name    : LowAccLTC_IsJAgreementTestable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:25.86073+00:00
-- url     : https://prove2.me/theorems/ca0821ca-5ed1-4439-81da-94516be1774c
-- title:
--   The $j$-agreement test and $(\alpha_0,\rho)$-agreement testability
-- statement:
--   Let $X$ be a weighted $r$-partite complex with HDX code $C=\mathrm{Tan}(X,C_0)$ and $1\le j\le r/2$. The **$j$-agreement test** takes a collection $\{c_s\in C_s\}_{s\in X\langle j\rangle}$ of local codewords, samples an edge $\{s,s'\}$ of the $j$-faces complex $Y=\mathcal F^jX$ (a top face $t\sim\mu$, a uniformly random $2j$-subset of its vertices, partitioned uniformly into two $j$-faces) and accepts iff $c_s$ and $c_{s'}$ agree on $\mathrm{star}(s\sqcup s')$. Write $\alpha$ for its rejection probability.
--
--   $C$ is **$(\alpha_0,\rho)$-agreement testable** w.r.t. the $j$-test if for every collection with $\alpha\le\alpha_0$ there is a global codeword $\hat c\in C$ with
--   $$\Pr_{s\sim X\langle j\rangle}\big[c_s\neq \hat c|_s\big]\le \rho(\alpha).$$
--   The module also defines the finite sets of ordered pairs and triples of disjoint $j$-sets of colours, which give the laws of oriented edges and triangles of $\mathcal F^jX$.
--
--   High-acceptance agreement testability under the $j$-test is assumption 4 of Theorem 4.1 and the content of Claim 5.8 for KMS codes.
--
--   **Formalization Note** Only the implication is bundled. A collection is a function on all finite vertex sets; only its values on $j$-faces matter.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.6 p.14 (PDF p.17), Definition 2.14 p.17 (PDF p.20), Definition 3.5 p.25 (PDF p.28)

import Definitions.Def_LowAccLTC_TannerCode

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

/-- Ordered pairs `(I, I')` of disjoint `j`-subsets of the colours. Sampling a top face `t ∼ μ`
and a uniform element of `jPairs r j` is the law of an oriented edge `(s, s')` of the `j`-faces
complex `Y = F^j X`: sample a `2j`-face and partition it uniformly into two `j`-faces
(Definition 2.14, p.17; Definition 3.5, p.25). -/
noncomputable def jPairs (r j : ℕ) : Finset (Finset (Fin r) × Finset (Fin r)) :=
  ((Finset.univ : Finset (Fin r)).powersetCard j ×ˢ (Finset.univ : Finset (Fin r)).powersetCard j).filter
    fun P => Disjoint P.1 P.2

/-- Ordered triples of pairwise disjoint `j`-subsets of the colours: the law of an oriented
triangle of `F^j X` (sample a `3j`-face and partition it uniformly, Definition 2.14, p.17). -/
noncomputable def jTriples (r j : ℕ) :
    Finset (Finset (Fin r) × Finset (Fin r) × Finset (Fin r)) :=
  ((Finset.univ : Finset (Fin r)).powersetCard j ×ˢ (Finset.univ : Finset (Fin r)).powersetCard j ×ˢ
      (Finset.univ : Finset (Fin r)).powersetCard j).filter
    fun Q => Disjoint Q.1 Q.2.1 ∧ Disjoint Q.1 Q.2.2 ∧ Disjoint Q.2.1 Q.2.2

/-- Two words disagree somewhere on the view `S`. -/
def Disagree {T A : Type*} (S : Finset T) (g h : T → A) : Prop := ∃ x ∈ S, g x ≠ h x

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- Rejection probability of the `j`-agreement test (Definition 3.5, p.25) on a collection
`c s` of local codewords indexed by `j`-faces: sample `{s, s'} ∼ Y⟨2⟩` and reject iff `c_s` and
`c_{s'}` differ on `star(s ⊔ s')`. -/
noncomputable def jTestRejection (j : ℕ) (c : Finset V → (T → A)) : ℝ := by
  classical exact X.E (fun t => avg (jPairs r j) (fun P =>
    ind (Disagree (X.star (X.face t P.1 ∪ X.face t P.2)) (c (X.face t P.1)) (c (X.face t P.2)))))

/-- `Tan(X, C₀)` is `(α₀, ρ)`-agreement testable w.r.t. the `j`-agreement test (Definition 2.6,
p.14, with Definition 3.5, p.25): for every collection `{c_s ∈ C_s}_{s ∈ X⟨j⟩}` whose rejection
probability `α` is at most `α₀` there is a global codeword `ĉ` with
`P_{s ∼ X⟨j⟩}[c_s ≠ ĉ|_s] ≤ ρ(α)`. The marginal law on `j`-faces is the induced one (sample
`t ∼ μ`, then a uniform `j`-subset of its colours).

**Formalization Note.** Only the implication is bundled; conditions on `ρ` and `α₀` are stated
where the paper assumes them. Values of `c` off the `j`-faces are irrelevant. -/
def IsJAgreementTestable (C₀ : (u : Finset V) → Set (X.star u → A)) (j : ℕ) (α₀ : ℝ)
    (ρ : ℝ → ℝ) : Prop :=
  ∀ c : Finset V → (T → A), (∀ s, X.IsFace s → s.card = j → c s ∈ X.localCode C₀ s) →
    X.jTestRejection j c ≤ α₀ →
    ∃ cHat ∈ X.tanner C₀,
      X.E (fun t => avg (Finset.univ.powersetCard j) (fun I =>
        ind (Disagree (X.star (X.face t I)) (c (X.face t I)) cHat))) ≤ ρ (X.jTestRejection j c)

end PartiteComplex

end LowAccLTC


