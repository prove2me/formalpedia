-- Prove2me | Definitions.Def_AGProxGap_Supplement_IsGSLevel
-- name    : AGProxGap_Supplement_IsGSLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:16:30.482534+00:00
-- url     : https://prove2.me/theorems/0b379a66-cd00-4dbb-a0c4-4cb267cff389
-- title:
--   Evaluation data at a level of the Garcia–Stichtenoth tower
-- statement:
--   Fix a level $j$ of the Garcia–Stichtenoth tower with function field $F_j$. Places $P_1,\dots,P_n,P_\infty$ of $F_j/\mathbb F_q$ are the level's **evaluation data** when
--   1. $x_0$ has a pole at $P_\infty$;
--   2. $P_1,\dots,P_n$ are pairwise distinct;
--   3. $\{P_1,\dots,P_n\}$ is exactly the set of rational places of $F_j$ other than $P_\infty$.
--
--   Since $x_0$ has a unique pole $P_{\infty,j}$ on $X_j$, these are the paper's $P_{\infty,j}$ and $D_j=\sum_{P\in X_j(\mathbb F_q)\setminus\{P_{\infty,j}\}}P$, with $n=n_j$. Also defined is the word $x^k(D)=(x_0^k(P_1),\dots,x_0^k(P_n))$.
--
--   **Formalization Note** The points are listed in an arbitrary order; statements quantify over every enumeration.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.4, p.15; §5, pp.34–35

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AGProxGap_Supplement_GSTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap.Supplement

/-- **The evaluation data at one level of the Garcia–Stichtenoth tower** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.4, p.15: "For
each j ≥ 0, let X_j be the curve with function field F_j. The function x_0 has a unique pole on
X_j, which we denote by P_{∞,j}. We use all the other rational points of X_j for evaluation and
write b_j = [F_j : F_0], D_j = Σ_{P∈X_j(F_q)∖{P_∞,j}} P, n_j = deg D_j"; §5, p.34: "We take the
natural point at infinity as P_∞ and use all the other rational points for evaluation").

For a tower datum `T` and a level `j`, places `P_1, …, P_n, P_∞` of the function field
`F_j/F_q` form the level's data when:
1. `x_0` has a pole at `P_∞` (`ord_{P_∞}(x_0) < 0`);
2. `P_1, …, P_n` are pairwise distinct;
3. they are exactly the rational places of `F_j` other than `P_∞`.

**Formalization Note** Places are the platform's `AlgebraicCurve.Place F_q F_j`, rational ones
have `IsRational`. Since `x_0` has a unique pole on `X_j` (Lemma 2.6), clause 1 determines
`P_∞ = P_{∞,j}`; clauses 2–3 make `P : Fin n → Place` an enumeration of `X_j(F_q) ∖ {P_∞,j}`,
so `n = n_j` and `D = D_j`. Every enumeration order gives the same code up to a coordinate
permutation, and the statements quantify over all of them. -/
def IsGSLevel {Fq : Type u} {Ω : Type v} [Field Fq] [Field Ω] [Algebra Fq Ω] {s : ℕ}
    (T : GSTower Fq Ω s) (j : ℕ) {n : ℕ} (P : Fin n → Place Fq (T.field j))
    (Pinf : Place Fq (T.field j)) : Prop :=
  Pinf.ord (T.x0At j) < 0 ∧ Function.Injective P ∧
    ∀ Q : Place Fq (T.field j), (∃ i, P i = Q) ↔ (Q.IsRational ∧ Q ≠ Pinf)

/-- The word `x^k(D) = (x_0^k(P_1), …, x_0^k(P_n)) ∈ F_q^n` at a level of the tower (§5.2, p.36:
"u_0 = x^{(1−2/p^a+1/p^{2a})q}(D)"; §5.3, p.39). -/
noncomputable def xWord {Fq : Type u} {Ω : Type v} [Field Fq] [Field Ω] [Algebra Fq Ω] {s : ℕ}
    (T : GSTower Fq Ω s) (j : ℕ) {n : ℕ} (P : Fin n → Place Fq (T.field j)) (k : ℕ) :
    Fin n → Fq :=
  fun i => (P i).evalAt ((T.x0At j) ^ k)

end AGProxGap.Supplement


