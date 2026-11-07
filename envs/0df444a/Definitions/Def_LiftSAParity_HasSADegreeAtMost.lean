-- Prove2me | Definitions.Def_LiftSAParity_HasSADegreeAtMost
-- name    : LiftSAParity_HasSADegreeAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:38.045535+00:00
-- url     : https://prove2.me/theorems/4515ab1a-32e5-401f-beb1-21d7e57af6db
-- title:
--   Sherali–Adams refutation of degree at most $d$
-- statement:
--   A Sherali–Adams refutation $\{q_p\}_p, h_\alpha$ has **degree at most $d$** when every term has total degree at most $d$:
--   $$\deg p+\deg q_p\le d\ \text{ for every axiom } p \text{ with } q_p\neq 0,\qquad \deg h_\alpha\le d .$$
--   This is the paper's "the degree of a refutation is the maximum degree of a monomial in it", with clauses encoded in product form and degree counting the total degree of each term (footnote 1).
--
--   **Formalization Note** Degree is measured on each term $p\cdot q_p$, before any cancellation between different terms. Since $\mathbb R[X]$ is a domain, $\deg(p\,q_p)=\deg p+\deg q_p$ for $q_p\neq0$.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4 and footnote 1

import Mathlib
import Definitions.Def_LiftSAParity_SARefutation

namespace LiftSAParity

/-- **Degree of a Sherali–Adams refutation, at most `d`** (de Rezende–Engström–Shekhovtsov,
*Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256
cab5a032…), §1.1, p.4: "The degree of a refutation is the maximum degree of a monomial in it",
with footnote 1: "clauses are encoded in product form and degree counts the total degree of each
term"). Every term `p · q_p` with `q_p ≠ 0` has `deg p + deg q_p ≤ d`, and `deg h_α ≤ d`.

**Formalization Note** Degree is measured on each term `p · q_p`, before any cancellation between
different terms. Since `ℝ[X]` is a domain, `deg (p · q_p) = deg p + deg q_p` for `q_p ≠ 0`. -/
def HasSADegreeAtMost {V : Type*} [Fintype V] {φ : CNF V} (π : SARefutation φ) (d : ℕ) : Prop :=
  (∀ C : φ, π.qClause C ≠ 0 →
      (clauseMono C.1).totalDegree + (π.qClause C).totalDegree ≤ d) ∧
  (∀ v : V, π.qComp v ≠ 0 → (compAxiom v).totalDegree + (π.qComp v).totalDegree ≤ d) ∧
  (∀ vb : V × Bool, π.qBool vb ≠ 0 →
      (boolAxiom vb).totalDegree + (π.qBool vb).totalDegree ≤ d) ∧
  π.h.totalDegree ≤ d

end LiftSAParity


