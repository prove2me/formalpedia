-- Prove2me | Definitions.Def_LowAccLTC_IsVATestable
-- name    : LowAccLTC_IsVATestable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:39:22.633508+00:00
-- url     : https://prove2.me/theorems/395a1a44-6a3b-4116-b9f9-caba13268437
-- title:
--   The vertex agreement test on a link and agreement testability w.r.t. it
-- statement:
--   Let $Y$ be a weighted partite complex and $b$ a face of $Y$ (possibly empty). On the link $Y_b$, a collection of local codewords $\{c_u\in L_u\}$, one for each vertex $u$ of the link, is tested by the **vertex agreement test**: sample an edge $uw$ of $Y_b$ (a top face $t\sim\mu$ conditioned on $b\subseteq t$ and an ordered pair of distinct vertices of $t\setminus b$) and accept iff $c_u$ and $c_w$ agree on $\mathrm{star}(b\cup\{u,w\})$. With rejection probability $\alpha$, a code $G$ on $\mathrm{star}(b)$ is **$(\alpha_0,\rho)$-agreement testable** w.r.t. this test if $\alpha\le\alpha_0$ implies that some $\hat c\in G$ satisfies
--   $$\Pr_{u\sim Y_b\langle 1\rangle}\big[c_u\neq\hat c|_{\mathrm{star}(b\cup\{u\})}\big]\le\rho(\alpha).$$
--   For $b=\emptyset$ this is the vertex agreement test on $Y$ itself.
--
--   This test is used in the trickling-down Proposition 5.11, in the colour-restriction Lemma 5.4 (on $Y^{\mathcal P}$) and in Claim 5.12 (on co-rank-two links of $Y^{\mathcal P}$).
--
--   **Formalization Note** $L_u$ is the local code of the view of $u$ (words read on $\mathrm{star}(b\cup\{u\})$); only the implication is bundled.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.6 p.14 (PDF p.17), Definition 5.10 p.48 (PDF p.51)

import Definitions.Def_LowAccLTC_IsJAgreementTestable

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- Rejection probability of the vertex agreement test on the link `X_b` of a face `b`
(Definition 5.10, p.48, applied to the link): sample an edge `uw` of `X_b` (a top face
`t ∼ μ` conditioned on `b ⊆ t` and a uniform ordered pair of distinct vertices of `t ∖ b`) and
reject iff `c_u` and `c_w` differ on their common view `star(b ∪ {u, w})`. -/
noncomputable def vaRejection (b : Finset V) (c : V → (T → A)) : ℝ := by
  classical exact X.Estar b (fun t => avg (X.freePairs b t) (fun ij =>
    ind (Disagree (X.star (insert (X.vert t ij.1) (insert (X.vert t ij.2) b)))
      (c (X.vert t ij.1)) (c (X.vert t ij.2)))))

/-- Fraction of link vertices `u` of `X_b` (sampled from the induced vertex law of the link)
whose local word `c_u` differs from `ĉ` on the view `star(b ∪ {u})`. -/
noncomputable def vaMismatch (b : Finset V) (c : V → (T → A)) (cHat : T → A) : ℝ := by
  classical exact X.Estar b (fun t => avg (X.freeColors b t) (fun i =>
    ind (Disagree (X.star (insert (X.vert t i) b)) (c (X.vert t i)) cHat)))

/-- The code `G` on the link `X_b` is `(α₀, ρ)`-agreement testable w.r.t. the vertex agreement
test (Definition 2.6, p.14, with Definition 5.10, p.48): for every collection of local codewords
`{c_u ∈ L u}` on the vertices `u` of the link `X_b` whose rejection probability `α` is at most
`α₀`, there is `ĉ ∈ G` with `P_u[c_u ≠ ĉ|_{b ∪ {u}}] ≤ ρ(α)`. With `b = ∅` this is the vertex
agreement test on `X` itself.

**Formalization Note.** `L u` is the local code of the view of `u` (a set of words on all top
faces read on `star(b ∪ {u})`); `G` is the code on `star(b)`. Only the implication is bundled. -/
def IsVATestable (b : Finset V) (L : V → Set (T → A)) (G : Set (T → A)) (α₀ : ℝ)
    (ρ : ℝ → ℝ) : Prop :=
  ∀ c : V → (T → A), (∀ t ∈ X.star b, ∀ i, X.vert t i ∉ b → c (X.vert t i) ∈ L (X.vert t i)) →
    X.vaRejection b c ≤ α₀ → ∃ cHat ∈ G, X.vaMismatch b c cHat ≤ ρ (X.vaRejection b c)

end PartiteComplex

end LowAccLTC


