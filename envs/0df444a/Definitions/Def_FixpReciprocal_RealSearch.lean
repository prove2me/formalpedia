-- Prove2me | Definitions.Def_FixpReciprocal_RealSearch
-- name    : FixpReciprocal_RealSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:26.164915+00:00
-- url     : https://prove2.me/theorems/9652f71e-9b0e-4c6c-876b-bc24c42953a5
-- title:
--   Search problems with real-valued solution sets
-- statement:
--   A **search problem with real-valued solution sets** $\Pi$ consists of a type of instances, an injective encoding of instances as words over $\mathrm{Sym}$, a dimension $n(\mathcal I)$ for each instance $\mathcal I$, and a solution set $\mathrm{Sol}_\Pi(\mathcal I)\subseteq\mathbb R^{n(\mathcal I)}$.
--
--   This is the framework of total search problems with real-valued solutions that the paper takes from Etessami and Yannakakis. The classes and reductions of the mission are stated for these objects.
--
--   **Formalization Note** Instances are typed: well-formedness is part of the instance type, so machines are constrained only on real instances, and a string that is not an instance may be mapped to anything. Injectivity of the encoding prevents a machine from ignoring its input. `lookup` reads a coordinate of a vector through a natural-number index and returns $0$ out of range; every statement that uses it bounds its indices.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), §3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace FixpReciprocal

open OnlineCRS.Combine

/-- **A search problem with real-valued solution sets.** Instances, a binary encoding of each
instance as a word (injective, so that a machine cannot ignore the instance), the dimension of the
solution vectors of each instance, and the solution set `Sol_Π(I)`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §3, p.10 ("search problems with real-valued solution sets"; "Sol_Π(I)").

**Formalization Note.** Instances are typed: well-formedness is part of `Inst`, so polynomial-time
machines are constrained only on real instances and strings that are not instances get any output.
Nothing requires the solution set to be nonempty; the paper's classes are about total problems, and
`InFIXP` forces totality because a basic FIXP instance always has a fixed point. -/
structure RealSearch where
  /-- the instances -/
  Inst : Type
  /-- the encoding of an instance -/
  enc : Inst → List Sym
  /-- distinct instances have distinct encodings -/
  enc_injective : Function.Injective enc
  /-- the number of real coordinates of a solution of the instance -/
  dim : Inst → ℕ
  /-- the solution set of the instance -/
  Sol : (I : Inst) → Set (Fin (dim I) → ℝ)

/-- Coordinate `j` of a real vector, read through a natural-number index (`0` when out of range;
every statement that uses it bounds its indices). -/
noncomputable def lookup {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x ⟨j, h⟩ else 0

end FixpReciprocal


