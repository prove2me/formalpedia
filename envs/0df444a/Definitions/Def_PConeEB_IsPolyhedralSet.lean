-- Prove2me | Definitions.Def_PConeEB_IsPolyhedralSet
-- name    : PConeEB_IsPolyhedralSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:13.14757+00:00
-- url     : https://prove2.me/theorems/bb64af7c-776a-41cf-8611-f57b01fd18d1
-- title:
--   Polyhedral set
-- statement:
--   A set $P\subseteq\mathcal E$ is **polyhedral** if it is the solution set of finitely many linear inequalities: there are $w_1,\dots,w_m\in\mathcal E$ and $c_1,\dots,c_m\in\mathbb R$ with
--   $$
--   P=\{x:\langle w_i,x\rangle\le c_i,\ i=1,\dots,m\}.
--   $$
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §2, p.3

import Mathlib

namespace PConeEB

/-- A polyhedral set: the solution set of finitely many linear inequalities `⟨w i, x⟩ ≤ c i`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §2, p.3. -/
def IsPolyhedralSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Set E) :
    Prop :=
  ∃ (m : ℕ) (w : Fin m → E) (c : Fin m → ℝ), P = {x | ∀ i, inner ℝ (w i) x ≤ c i}

end PConeEB


