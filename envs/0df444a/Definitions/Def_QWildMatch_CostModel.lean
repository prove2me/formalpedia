-- Prove2me | Definitions.Def_QWildMatch_CostModel
-- name    : QWildMatch_CostModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:23.523455+00:00
-- url     : https://prove2.me/theorems/ed20e1c9-17da-4f5f-b4a0-33522858bb66
-- title:
--   The weighted wildcard cost table and the quantities $\alpha,\beta,r_+,r_-,\ell$
-- statement:
--   Let $\Sigma$ be a finite nonempty text alphabet and let $\star\notin\Sigma$ be the wildcard, which occurs only in the pattern. A cost table consists of substitution costs $\mu:(\Sigma\cup\{\star\})\times\Sigma\to\mathbb R_{\ge0}$, deletion costs $c_{\mathrm{del}}:\Sigma\cup\{\star\}\to\mathbb R_{>0}$ and insertion costs $c_{\mathrm{ins}}:\Sigma\to\mathbb R_{>0}$; it need not be a metric. From the table and a threshold $k$ one derives
--
--   $$\alpha=\min_{b\in\Sigma}c_{\mathrm{ins}}(b),\qquad \beta=\min_{a\in\Sigma\cup\{\star\}}c_{\mathrm{del}}(a),\qquad r_+=\lfloor k/\alpha\rfloor,\qquad r_-=\lfloor k/\beta\rfloor,\qquad \ell=m+r_+,$$
--
--   where $m$ is the pattern length. The number $r_+$ bounds the inserted text symbols of an alignment of cost at most $k$, $r_-$ the deleted pattern symbols, and $\ell$ the longest text window a fixed start can use.
--
--   **Formalization Note** The pattern alphabet is `Option Sym`, with `none` the wildcard. The page's equations $\mu(\star,b)=0$ and $\mu(a,a)=0$ are not bundled in the structure, because Theorems 4.1 and 6.5 speak of arbitrary nonnegative substitution costs; they are kept as the separate predicate `IsWildcardCost`, which no statement assumes. The floors are `Nat.floor`, which returns $0$ on a negative argument.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §3, pp.3–4; Lemma 3.1, p.4; §4, p.5

import Mathlib

namespace QWildMatch

/-- The classically specified cost table of Zhao, Chen, Li, Kong, Peng, Yu, Yue, *Quantum Approximate
Pattern Matching with Wildcards and Weighted Edits*, STOC 2027 submission (file sha256 9e87a9dd…),
§3, pp.3–4: substitution costs `μ : (Σ ∪ {⋆}) × Σ → ℝ≥0`, deletion costs `c_del : Σ ∪ {⋆} → ℝ>0`,
insertion costs `c_ins : Σ → ℝ>0`.

**Formalization Note** The pattern alphabet `Σ ∪ {⋆}` is `Option Sym`, with `none` = `⋆`. The page's
equations `μ(⋆, b) = 0` and `μ(a, a) = 0` are not bundled: Theorems 4.1 and 6.5 speak of arbitrary
nonnegative substitution costs and their proofs use neither equation, so every result here holds for
any `μ ≥ 0` and specializes to the §3 model. See `IsWildcardCost`. -/
structure CostModel (Sym : Type) where
  /-- Substitution cost `μ(a, b)` of pattern symbol `a` against text symbol `b`. -/
  μ : Option Sym → Sym → ℝ
  /-- Deletion cost `c_del(a)` of a pattern symbol. -/
  cdel : Option Sym → ℝ
  /-- Insertion cost `c_ins(b)` of a text symbol. -/
  cins : Sym → ℝ
  μ_nonneg : ∀ a b, 0 ≤ μ a b
  cdel_pos : ∀ a, 0 < cdel a
  cins_pos : ∀ b, 0 < cins b

/-- The two equations of the cost table on p.3, `μ(⋆, b) = 0` and `μ(a, a) = 0`, kept visible for
reference. No statement of this mission assumes them (Zhao et al., STOC 2027 submission, §3, p.3). -/
def IsWildcardCost {Sym : Type} (cm : CostModel Sym) : Prop :=
  (∀ b, cm.μ none b = 0) ∧ ∀ a, cm.μ (some a) a = 0

/-- `α = min_{b ∈ Σ} c_ins(b)`, the minimum **insertion** cost (Zhao et al., STOC 2027 submission,
§3, p.4). -/
noncomputable def CostModel.alpha {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty cm.cins

/-- `β = min_{a ∈ Σ ∪ {⋆}} c_del(a)`, the minimum **deletion** cost (Zhao et al., STOC 2027
submission, §3, p.4). -/
noncomputable def CostModel.beta {Sym : Type} [Fintype Sym] (cm : CostModel Sym) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty cm.cdel

/-- `r₊ = ⌊k/α⌋`, the bound on inserted symbols (Zhao et al., STOC 2027 submission, Lemma 3.1, p.4).

**Formalization Note** `⌊·⌋₊` returns `0` on a negative argument; a path of cost at most `k` forces
`k ≥ 0`, and the theorems that need it say so. -/
noncomputable def rPlus {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym) (k : ℝ) : ℕ :=
  ⌊k / cm.alpha⌋₊

/-- `r₋ = ⌊k/β⌋`, the bound on deleted symbols (Zhao et al., STOC 2027 submission, Lemma 3.1, p.4). -/
noncomputable def rMinus {Sym : Type} [Fintype Sym] (cm : CostModel Sym) (k : ℝ) : ℕ :=
  ⌊k / cm.beta⌋₊

/-- `ℓ = m + r₊`, the longest text window a fixed-start verifier reads (Zhao et al., STOC 2027
submission, §4, p.5; §6.1, p.8; Theorem 6.5, p.10). -/
noncomputable def ell {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym)
    (P : List (Option Sym)) (k : ℝ) : ℕ :=
  P.length + rPlus cm k

end QWildMatch


