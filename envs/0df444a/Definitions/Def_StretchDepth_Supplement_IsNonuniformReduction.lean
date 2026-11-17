-- Prove2me | Definitions.Def_StretchDepth_Supplement_IsNonuniformReduction
-- name    : StretchDepth_Supplement_IsNonuniformReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:11:00.349003+00:00
-- url     : https://prove2.me/theorems/7a49af7f-5153-49ad-9e4f-5f1e6973f5c0
-- title:
--   Amplification reductions with nonuniform security (Definition 7)
-- statement:
--   Let $N>n$, $M>m$ and $0<\gamma,\epsilon\le1$. A **$(q,\gamma,\epsilon,d)$ amplification reduction with nonuniform security** from $n\mapsto N$ stretch to $m\mapsto M$ stretch is a pair $(H,R)$ where $H:\{0,1\}^m\to\{0,1\}^M$ is a $(q,d)$-construction from $G:\{0,1\}^n\to\{0,1\}^N$ and, for each **advice string** $a\in\{0,1\}^q$, $R_a$ is a randomized query procedure with output in $\{0,1\}$ querying $G$ and $T:\{0,1\}^M\to\{0,1\}$, such that for all $G,T$
--   $$
--   \mathrm{Adv}_{H^G}(T)\ge\gamma\ \Longrightarrow\ \exists a\in\{0,1\}^q,\ \mathrm{Adv}_G(R^{G,T}_a)\ge\epsilon,
--   $$
--   and on every input, for every choice of its randomness and every advice $a$, $R_a$ makes at most $q$ queries in total to $G$ and $T$.
--
--   The advice may depend on $G$ and $T$; this strengthens the uniform reductions of Definition 3 (the base mission's `IsPRGReduction`).
--
--   **Formalization Note** The base mission's query layer (`IsConstruction`, `QProc`, `WithinQueries`, `advH`, `SAdv`) is reused unchanged.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Appendix A, Definition 7, p.31 (PDF p.31)

import Definitions.Def_StretchDepth_IsPRGReduction

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- **`(q, γ, ϵ, d)` amplification reduction with nonuniform security.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 7, p.31: "a pair (H, R) such that H(·) : {0,1}^m → {0,1}^M is a
(q, d)-construction from inner function G : {0,1}^n → {0,1}^N, and for each advice string
a ∈ {0,1}^q, R^{G,T}_a is a randomized query procedure outputting a value in {0,1} and querying
oracles G : {0,1}^n → {0,1}^N, T : {0,1}^M → {0,1}, such that for every possible G, T we have:
Adv_{H^G}(T) ≥ γ ⟹ ∃a ∈ {0,1}^q, Adv_G(R^{G,T}_a) ≥ ϵ. On every input and for every choice of its
randomness and advice a, R_a makes at most q queries in total to G and T."

**Formalization Note.** The base mission's query layer is reused unchanged (`IsConstruction`,
`QProc`, `WithinQueries`, `advH`, `SAdv`; `Adv_G = |SAdv_G|`). The advice string is chosen after
`G` and `T`; its length is the same `q` that bounds the queries. The conditions `N > n`, `M > m`,
`0 < γ, ϵ ≤ 1` are hypotheses of the theorems using this predicate. -/
def IsNonuniformReduction {n N m M : ℕ} (H : Bits m → RoundTree n N M) (q : ℕ)
    (R : Bits q → PMF (Bits N → QProc n N M)) (γ ε : ℝ) (d : ℕ) : Prop :=
  IsConstruction H q d ∧ (∀ a : Bits q, WithinQueries (R a) q) ∧
    ∀ (G : Bits n → Bits N) (T : Bits M → Bool),
      γ ≤ advH H G T → ∃ a : Bits q, ε ≤ |SAdv (R a) G T|

end StretchDepth.Supplement


