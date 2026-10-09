-- Prove2me | Definitions.Def_NicerEars_TJoin_ForestRep
-- name    : NicerEars_TJoin_ForestRep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:49.714186+00:00
-- url     : https://prove2.me/theorems/77ff7939-cbf2-47c8-82c4-9b45a5c29757
-- title:
--   §3.2, p. 12 — forest representative systems
-- statement:
--   (Sebő–Vygen, §3.2, p. 12.) Let $U$ and $M$ be finite sets and $U_f\subseteq U$ for $f\in M$. For $F\subseteq M$, a family $(e_f)_{f\in F}$ is a **forest representative system** for $(U_f)_{f\in F}$ if
--
--   1. $e_f\in\binom{U_f}{2}$ (a two-element subset of $U_f$) for all $f\in F$;
--   2. $e_f\ne e_{f'}$ for $f\ne f'$;
--   3. the graph $(U,\{e_f: f\in F\})$ is a forest.
--
--   This is the matroidal generalization of a system of distinct representatives used in Lovász's min-max theorem (Corollary 14), which computes the maximum earmuff.
--
--   **Formalization Note.** The family is a function $e: M\to\mathrm{Sym}^2 U$ of which only the values on $F$ matter; the forest condition is acyclicity of the simple graph with edge set $\{e_f: f\in F\}$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, §3.2, p. 12

import Mathlib

namespace NicerEars.TJoin

/-- §3.2, p. 12: for finite sets `U`, `M` and sets `U_f ⊆ U` (`f ∈ M`), the family `(e_f)_{f ∈ F}`
is a forest representative system for `(U_f)_{f ∈ F}` if `e_f` is a two-element subset of `U_f` for
every `f ∈ F`, `e_f ≠ e_{f'}` for `f ≠ f'`, and the graph `(U, {e_f : f ∈ F})` is a forest. -/
def IsForestRepSystem {U M : Type} (Uf : M → Finset U) (F : Finset M) (e : M → Sym2 U) : Prop :=
  (∀ f ∈ F, ¬ (e f).IsDiag ∧ ∀ u ∈ e f, u ∈ Uf f) ∧
  Set.InjOn e (F : Set M) ∧
  (SimpleGraph.fromEdgeSet (e '' (F : Set M))).IsAcyclic

/-- `(U_f)_{f ∈ F}` has a forest representative system. -/
def HasForestRepSystem {U M : Type} (Uf : M → Finset U) (F : Finset M) : Prop :=
  ∃ e : M → Sym2 U, IsForestRepSystem Uf F e

end NicerEars.TJoin


