-- Prove2me | Definitions.Def_StretchDepth_IsPRGReduction
-- name    : StretchDepth_IsPRGReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:42.796197+00:00
-- url     : https://prove2.me/theorems/5df9ba0e-e297-49c8-933d-59bb596229a1
-- title:
--   PRG stretch amplification reductions
-- statement:
--   Let $T:\{0,1\}^M\to\{0,1\}$ be a test and $R$ a randomized query procedure with oracles $G$ and $T$ and one output bit. The **signed advantage** of $R^{G,T}$ against $G$ is
--   $$
--   \mathrm{SAdv}_G(R^{G,T})=\Pr[R^{G,T}(G(U_n))=1]-\Pr[R^{G,T}(U_N)=1],
--   $$
--   and the advantage of $T$ against $H^G$ is
--   $$
--   \mathrm{Adv}_{H^G}(T)=\bigl|\Pr[T(H^G(U_m))=1]-\Pr[T(U_M)=1]\bigr|.
--   $$
--   A **$(q,\gamma,\epsilon,d)$ amplification reduction** is a pair $(H,R)$ with:
--
--   1. $H$ a $(q,d)$-construction;
--   2. $R$ making at most $q$ queries in total to $G$ and $T$, on every input and for every choice of randomness;
--   3. for all $G,T$: $\mathrm{Adv}_{H^G}(T)\ge\gamma$ implies $|\mathrm{SAdv}_G(R^{G,T})|\ge\epsilon$.
--
--   There is no depth restriction on $R$, and $T$ is deterministic. This is the notion of a fully black-box security reduction.
--
--   **Formalization Note** $R$ is a `PMF` over functions from the challenge to a decision tree (`QAlgorithms.DecisionTree`): one draw fixes the procedure on every challenge. A `PMF` loses nothing, since after pruning to reachable branches the procedures with at most $q$ queries form a finite set. The query bound runs over real pairs $(G,T)$ and over the support of $R$; `DecisionTree.MakesAtMost` is not used, because it also quantifies over oracles that answer a $G$-query with a $T$-answer, a condition the source does not impose. The parameter conditions $N>n$, $M>m$, $0<\gamma,\epsilon\le 1$ are hypotheses of the theorems.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definitions 2 and 3, pp.13–14

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_StretchDepth_IsConstruction

namespace StretchDepth

open QAlgorithms

variable {n N m M : ℕ}

/-- A deterministic query procedure of the reduction: a decision tree whose queries are inputs of
`G` or of `T` and whose answers are values of `G` or of `T`, with a bit as output. -/
abbrev QProc (n N M : ℕ) := DecisionTree (Bits n ⊕ Bits M) (Bits N ⊕ Bool) Bool

/-- The combined oracle of a real pair `(G, T)`. -/
def oracle (G : Bits n → Bits N) (T : Bits M → Bool) : Bits n ⊕ Bits M → Bits N ⊕ Bool :=
  Sum.elim (fun w => Sum.inl (G w)) (fun y => Sum.inr (T y))

/-- `Pr[R^{G,T}(z) = 1]`, over the internal randomness of `R`. -/
noncomputable def acceptProb (R : PMF (Bits N → QProc n N M)) (G : Bits n → Bits N)
    (T : Bits M → Bool) (z : Bits N) : ℝ :=
  ((R.map fun f => (f z).eval (oracle G T)) true).toReal

/-- Definition 2, pp.13–14: `SAdv_G(R^{G,T}) = Pr[R^{G,T}(G(U_n)) = 1] − Pr[R^{G,T}(U_N) = 1]`.
`Adv` is the absolute value. -/
noncomputable def SAdv (R : PMF (Bits N → QProc n N M)) (G : Bits n → Bits N)
    (T : Bits M → Bool) : ℝ :=
  (∑ w : Bits n, acceptProb R G T (G w)) / 2 ^ n - (∑ z : Bits N, acceptProb R G T z) / 2 ^ N

/-- Definition 2, pp.13–14, for the deterministic distinguisher `T` and the generator `H^G`:
`Adv_{H^G}(T) = |Pr_x[T(H^G(x)) = 1] − Pr_y[T(y) = 1]|`. -/
noncomputable def advH (H : Bits m → RoundTree n N M) (G : Bits n → Bits N)
    (T : Bits M → Bool) : ℝ :=
  |((Finset.univ.filter fun x : Bits m => T (run G (H x)) = true).card : ℝ) / 2 ^ m -
    ((Finset.univ.filter fun y : Bits M => T y = true).card : ℝ) / 2 ^ M|

/-- Definition 3, p.14: "On every input and for every choice of its randomness, R makes at most q
queries in total to G and T." Read on real pairs `(G, T)` and on the support of `R`. -/
def WithinQueries (R : PMF (Bits N → QProc n N M)) (q : ℕ) : Prop :=
  ∀ f ∈ R.support, ∀ (z : Bits N) (G : Bits n → Bits N) (T : Bits M → Bool),
    (f z).queries (oracle G T) ≤ q

/-- **`(q, γ, ϵ, d)` amplification reduction.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 3, p.14: "a pair (H, R) such that H(·) : {0, 1}m → {0, 1}M is a
(q, d)-construction from inner function G : {0, 1}n → {0, 1}N, and RG,T is a randomized query
procedure outputting a value in {0, 1} and querying oracles G : {0, 1}n → {0, 1}N,
T : {0, 1}M → {0, 1}, such that for every possible G, T we have: AdvHG(T) ≥ γ =⇒ AdvG(RG,T ) ≥ ϵ".

**Formalization Note.** `R` is a `PMF` over functions from the challenge to a decision tree: one
draw fixes the procedure on every challenge, as in Definition 2 (a distribution over Boolean
functions). A `PMF` loses nothing: after pruning to reachable branches, procedures with at most
`q` queries form a finite set. The query bound runs over real pairs and the support of `R`;
`DecisionTree.MakesAtMost` is deliberately not used, since it quantifies over oracles answering a
`G`-query with a `T`-answer, a condition the page does not impose. `T` is a deterministic function
(p.14). There is no depth bound on `R` (p.14). The conditions `N > n`, `M > m`, `0 < γ, ϵ ≤ 1` are
hypotheses of the theorems using this predicate. -/
def IsPRGReduction (H : Bits m → RoundTree n N M) (R : PMF (Bits N → QProc n N M)) (q : ℕ)
    (γ ε : ℝ) (d : ℕ) : Prop :=
  IsConstruction H q d ∧ WithinQueries R q ∧
    ∀ (G : Bits n → Bits N) (T : Bits M → Bool), γ ≤ advH H G T → ε ≤ |SAdv R G T|

end StretchDepth


