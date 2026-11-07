-- Prove2me | Definitions.Def_LowAccLTC_IsLALTCVertex
-- name    : LowAccLTC_IsLALTCVertex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:29.913001+00:00
-- url     : https://prove2.me/theorems/31bc554c-86a5-4ad5-9a3b-f58321ce1ce9
-- title:
--   The vertex test and $(\varepsilon,\varphi)$-low-acceptance local testability
-- statement:
--   For a word $f$ on the top faces of a weighted partite complex $X$ with HDX code $C=\mathrm{Tan}(X,C_0)$, the **vertex test** samples a vertex $v\sim X\langle 1\rangle$ (a top face $t\sim\mu$ and a uniformly random vertex of $t$) and reads $f$ on $\mathrm{star}(v)$; the quantity it measures is
--   $$\varepsilon(f)=\mathbb E_{v\sim X\langle 1\rangle}\big[\mathrm{dist}(f|_v,C_v)\big].$$
--   The code $C$ is an **$(\varepsilon,\varphi)$-LA LTC** (low acceptance locally testable code) w.r.t. the vertex test if for every word $f$,
--   $$x:=1-\varepsilon(f)\ \ge\ \varepsilon \quad\Longrightarrow\quad 1-\mathrm{dist}(f,C)\ \ge\ \varphi(x).$$
--
--   This is the notion proved for KMS codes in the goal theorem and produced by the general framework of Theorem 4.1.
--
--   **Formalization Note** Only the implication is part of the definition; the conditions of Definition 2.3 on $\varphi$ and on $\varepsilon$ are hypotheses of the theorems that need them.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.3 p.14 (PDF p.17), Definition 3.4 p.25 (PDF p.28)

import Definitions.Def_LowAccLTC_TannerCode

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T A : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- The vertex-test quantity `ε(f) = E_{v ∼ X⟨1⟩}[dist(f|_v, C_v)]` (Definition 3.4, p.25):
a vertex is sampled by sampling a top face `t ∼ μ` and a uniformly random colour `i`, and `f` is
compared with the induced local code `C_v` on `star(v)`. -/
noncomputable def vertexTestDist (C₀ : (u : Finset V) → Set (X.star u → A)) (f : T → A) : ℝ :=
  X.E (fun t => avg Finset.univ (fun i : Fin r =>
    X.distTo (X.star {X.vert t i}) f (X.localCode C₀ {X.vert t i})))

/-- `Tan(X, C₀)` is an `(ε, φ)`-LA LTC (low acceptance locally testable code) under the vertex
test (Definition 2.3, p.14, with the vertex test of Definition 3.4): for every word `f`,
`x := 1 - E_v[dist(f|_v, C_v)] ≥ ε` implies `1 - dist(f, C) ≥ φ(x)`.

**Formalization Note.** Only the implication is bundled; the conditions of Definition 2.3 on
`φ` (monotone, `[0,1] → ℝ₊`) and `ε ∈ (0,1)` are stated as hypotheses where the paper assumes
them. -/
def IsLALTCVertex (C₀ : (u : Finset V) → Set (X.star u → A)) (ε : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ f : T → A, ε ≤ 1 - X.vertexTestDist C₀ f →
    φ (1 - X.vertexTestDist C₀ f) ≤ 1 - X.distTo Finset.univ f (X.tanner C₀)

end PartiteComplex

end LowAccLTC


