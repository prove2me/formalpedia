-- Prove2me | Definitions.Def_BoolCSPDel_Rel
-- name    : BoolCSPDel_Rel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:50.471205+00:00
-- url     : https://prove2.me/theorems/d79c5b41-a788-4a8b-82c8-7803e0dd6395
-- title:
--   Boolean relations of arity at most $k$ and constraint languages
-- statement:
--   A **relation** of arity at most $k$ is an arity $a\le k$ together with a set $R\subseteq\{0,1\}^a$; it is **proper** if $R\ne\{0,1\}^a$. A **constraint language** $\Gamma$ is a finite set of such relations. It is **constant-satisfiable** if there is one value $v\in\{0,1\}$ with $v^a\in R$ for every $R\in\Gamma$ of arity $a$.
--
--   There are finitely many languages for each $k$, which is what makes the constants $O_k$, $\Omega_k$ of the paper uniform in $\Gamma$.
--
--   **Formalization Note** Mixed arities are allowed, as in the paper's lower-bound constructions and Corollary 4.16. A set of relations has no duplicates.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.1, p.17; p.18; footnote 4, p.6

import Mathlib

namespace BoolCSPDel

/-- **Boolean relations and constraint languages.** Bandekar, Sharma, Velusamy, *A New
Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission
(manuscript sha256 15f83519…), §3.1, p.17, and footnote 4, p.6.

A relation of arity at most `k`: an arity `a ≤ k` together with a set of tuples in `{0,1}^a`.

**Formalization Note.** `Rel k` is a finite type, so there are finitely many languages for each `k`,
as p.17 says, and a constant quantified over `Lang k` depends on `k` only. Mixed arities are allowed
(p.21: "we nevertheless use original arities"; Corollary 4.16: "arity at most k"). -/
abbrev Rel (k : ℕ) : Type := Σ a : Fin (k + 1), Finset (Fin a → Bool)

/-- A constraint language: a finite set of relations of arity at most `k`. -/
abbrev Lang (k : ℕ) : Type := Finset (Rel k)

/-- `R` is nonempty and proper (not the full Boolean cube). -/
def IsNonemptyProper {k : ℕ} (R : Rel k) : Prop := R.2.Nonempty ∧ R.2 ≠ Finset.univ

/-- Every relation of the language is nonempty and proper (footnote 4, p.6). -/
def AllNonemptyProper {k : ℕ} (Γ : Lang k) : Prop := ∀ R ∈ Γ, IsNonemptyProper R

/-- Constant-satisfiable language, p.18: one value `v` with `v^a ∈ R` for every `R ∈ Γ`. -/
def ConstSat {k : ℕ} (Γ : Lang k) : Prop := ∃ v : Bool, ∀ R ∈ Γ, (fun _ => v) ∈ R.2

end BoolCSPDel


