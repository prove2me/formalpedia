-- Prove2me | Definitions.Def_LDPSelect_IsMinorOf
-- name    : LDPSelect_IsMinorOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:50.258206+00:00
-- url     : https://prove2.me/theorems/8909a7b7-245d-4a8c-b052-17b2a2b6ef2e
-- title:
--   Minors of a downward-closed family, and isomorphism of families
-- statement:
--   Let $\mathcal F$ be a downward-closed family on $E$. For a feasible set $I_0\in\mathcal F$ the **contraction** is $\mathcal F/I_0=\{S\subseteq E\setminus I_0 : S\cup I_0\in\mathcal F\}$, and the **deletion** of $E'\subseteq E$ is $\{S\in\mathcal F : S\cap E'=\emptyset\}$. Every minor, obtained by repeated contractions and deletions, is a single contraction followed by a single deletion.
--
--   A family $\mathcal O$ on a $k$-element ground set $[k]$ is a **minor** of $\mathcal F$ if there are a feasible set $I_0\in\mathcal F$ and an injection $f:[k]\to E\setminus I_0$ with
--
--   $$S\in\mathcal O \iff f(S)\cup I_0\in\mathcal F\qquad\text{for all } S\subseteq[k].$$
--
--   The elements outside $I_0\cup f([k])$ are the deleted ones. The injection makes the notion invariant under relabelling of $\mathcal O$: "$\mathcal F$ has $\mathcal O$ as a minor" means up to isomorphism, as Theorem 1 uses it.
--
--   Two families $\mathcal O$ on $[k]$ and $\mathcal F$ on $[n]$ are **isomorphic** if a bijection $[k]\to[n]$ carries $\mathcal O$ onto $\mathcal F$.
--
--   **Formalization Note** The single form follows p.8: "Every minor of a matroid, and more generally of a downward-closed family, can be written as a single contraction of a feasible set followed by a single deletion."
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §5, p.9 (pdf p.10); §3.4, p.8 (pdf p.9)

import Mathlib
import Definitions.Def_LDPSelect_Family

namespace LDPSelect

/-!
# Minors and isomorphism of families

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §5, p.9 (contraction and deletion); §3.4, p.8 (a minor is one contraction followed by one
deletion).

**Formalization Note.** A minor is written in the single form of p.8: a feasible set `I`, an injection
`f` from the minor's ground set into the elements outside `I`, all other elements being deleted. The
injection makes "has `O` as a minor" hold up to isomorphism, as Theorem 1 uses it.
-/

/-- `O` is, up to relabelling, the minor `F / I \\ E′` of `F`, where `I ∈ F`, the embedding `f` names the
surviving elements, and `E′` is the set of elements outside `I` and outside the range of `f`. -/
def IsMinorOf {k n : ℕ} (O : Family k) (F : Family n) : Prop :=
  ∃ (I : Finset (Fin n)) (f : Fin k ↪ Fin n),
    I ∈ F ∧ (∀ j, f j ∉ I) ∧ ∀ S : Finset (Fin k), S ∈ O ↔ S.map f ∪ I ∈ F

/-- Isomorphism of families: a bijection of ground sets carrying one family onto the other. -/
def IsIsoFam {k n : ℕ} (O : Family k) (F : Family n) : Prop :=
  ∃ e : Fin k ≃ Fin n, ∀ S : Finset (Fin k), S ∈ O ↔ S.map e.toEmbedding ∈ F

end LDPSelect


