-- Prove2me | Definitions.Def_DataValidation_transReduction
-- name    : DataValidation_transReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:34.193901+00:00
-- url     : https://prove2.me/theorems/daa87863-5b8c-4120-a9fd-601de4e1c4b1
-- title:
--   Directed paths, acyclic edge sets, and the transitive reduction $R(E)$
-- statement:
--   Let $E\subseteq V\times V$ be a finite set of directed edges. A **directed path** from $u$ to $v$ in $E$ is a walk of at least one edge, and $E$ is **acyclic** if no vertex has a directed path to itself. The **transitive reduction** of $E$ is
--
--   $$R(E)=\{(u,v)\in E : E\setminus\{(u,v)\}\text{ contains no directed }u\text{-}v\text{ path}\}.$$
--
--   In the Data Validation Problem these are the only edges a policy may probe: a precedence implied by a longer chain cannot be challenged until the chain is broken.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), §1, p.1, and footnote 1

import Mathlib

set_option autoImplicit false

namespace DataValidation

/-- A **directed path** from `u` to `v` in the edge set `E`: a walk of at least one edge. Tinguely,
van der Heijden, *Approximation and Hardness for the Data Validation Problem*, arXiv:2611.06773
(sha256 6595f819…), §1, p.1, footnote 1: "When we speak of paths on a DAG, we always mean directed
paths."

**Formalization Note.** At least one edge, so that `HasPath E v v` says that `E` has a cycle
through `v`; a path between distinct vertices is the same thing as in the page's reading. -/
def HasPath {V : Type*} (E : Finset (V × V)) (u v : V) : Prop :=
  Relation.TransGen (fun a b => (a, b) ∈ E) u v

/-- `E` is **acyclic**: it has no directed cycle (in particular no loop). arXiv:2611.06773
(sha256 6595f819…), §1, p.1, "directed acyclic graph". -/
def IsAcyclic {V : Type*} (E : Finset (V × V)) : Prop :=
  ∀ v, ¬ HasPath E v v

open scoped Classical in
/-- The **transitive reduction** `R(E)`: all edges `(u, v) ∈ E` such that `E ∖ {(u, v)}` contains no
directed `u`-`v` path. arXiv:2611.06773 (sha256 6595f819…), §1, p.1. -/
noncomputable def transReduction {V : Type*} [DecidableEq V] (E : Finset (V × V)) :
    Finset (V × V) :=
  E.filter fun e => ¬ HasPath (E.erase e) e.1 e.2

end DataValidation


